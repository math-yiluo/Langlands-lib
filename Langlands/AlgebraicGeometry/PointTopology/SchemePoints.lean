import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeMaps
import Mathlib.AlgebraicGeometry.Stalk

/-!
# Affine-chart final topology on actual scheme points
-/

noncomputable section

universe u v

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R : Type u) [CommRing R]
variable (X : Over (Spec (CommRingCat.of R)))

/-- An actual open subscheme with its structure morphism over the same base. -/
def openOver (U : X.left.Opens) : Over (Spec (CommRingCat.of R)) :=
  Over.mk (U.ι ≫ X.hom)

/-- The actual open immersion as a relative morphism. -/
def openOverι (U : X.left.Opens) : openOver R X U ⟶ X :=
  Over.homMk U.ι

instance (U : X.left.Opens) [IsAffine U] : IsAffine (openOver R X U).left :=
  inferInstanceAs (IsAffine U)

variable (S : Type u) [CommRing S] [Algebra R S]

/-- The inclusion of open-subscheme points is actual postcomposition. -/
def openPointMap (U : X.left.Opens) :
    RingPoint R (openOver R X U) S → RingPoint R X S :=
  fun p => p ≫ openOverι R X U

theorem openPointMap_injective (U : X.left.Opens) :
    Function.Injective (openPointMap R X S U) := by
  intro p q h
  apply RingPoint.ext
  apply (cancel_mono U.ι).mp
  exact congrArg (fun z : RingPoint R X S => z.left) h

/-- Factor a point through an open subscheme containing its whole image. -/
def openPointLift (U : X.left.Opens) (p : RingPoint R X S)
    (hp : Set.range p.left ⊆ U) : RingPoint R (openOver R X U) S := by
  let f : Spec (CommRingCat.of S) ⟶ X.left := p.left
  let q : Spec (CommRingCat.of S) ⟶ U.toScheme :=
    IsOpenImmersion.lift U.ι f (by rw [Scheme.Opens.range_ι]; exact hp)
  have hbase : f ≫ X.hom = Spec.algebraMap R S := Over.w p
  exact Over.homMk q
    (by
      change q ≫ (U.ι ≫ X.hom) = Spec.algebraMap R S
      calc
        _ = (q ≫ U.ι) ≫ X.hom := (Category.assoc _ _ _).symm
        _ = f ≫ X.hom :=
          congrArg (fun g : Spec (CommRingCat.of S) ⟶ X.left => g ≫ X.hom)
            (IsOpenImmersion.lift_fac U.ι f _)
        _ = _ := hbase)

@[simp] theorem openPointMap_lift (U : X.left.Opens) (p : RingPoint R X S)
    (hp : Set.range p.left ⊆ U) :
    openPointMap R X S U (openPointLift R X S U p hp) = p := by
  apply RingPoint.ext
  exact IsOpenImmersion.lift_fac U.ι p.left _

/-- Open-subscheme points are exactly the actual points with image in that open. -/
def openPointEquiv (U : X.left.Opens) :
    RingPoint R (openOver R X U) S ≃
      {p : RingPoint R X S // Set.range p.left ⊆ U} where
  toFun p := ⟨openPointMap R X S U p, by
    rintro _ ⟨z, rfl⟩
    exact (p.left z).property⟩
  invFun p := openPointLift R X S U p.val p.property
  left_inv p := (openPointMap_injective R X S U)
    (openPointMap_lift R X S U _ _)
  right_inv p := Subtype.ext (openPointMap_lift R X S U _ _)

/-- Over a local value ring, one closed-point image determines containment in an open. -/
theorem range_subset_open_iff_closedPoint [IsLocalRing S]
    (U : X.left.Opens) (p : RingPoint R X S) :
    Set.range p.left ⊆ U ↔ p.left (IsLocalRing.closedPoint S) ∈ U := by
  constructor
  · intro h
    exact h ⟨_, rfl⟩
  · intro h y hy
    obtain ⟨z, rfl⟩ := hy
    exact ((IsLocalRing.specializes_closedPoint z).map p.left.continuous).mem_open U.isOpen h

/-- Every open cover covers actual points when the value ring is local. -/
theorem exists_openPointMap_of_cover [IsLocalRing S]
    {ι : Type v} (U : ι → X.left.Opens) (hU : iSup U = ⊤)
    (p : RingPoint R X S) :
    ∃ i, ∃ q : RingPoint R (openOver R X (U i)) S,
      openPointMap R X S (U i) q = p := by
  have hp : p.left (IsLocalRing.closedPoint S) ∈ iSup U := by rw [hU]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hp
  exact ⟨i, openPointLift R X S (U i) p
    ((range_subset_open_iff_closedPoint R X S (U i) p).mpr hi),
    openPointMap_lift R X S (U i) p _⟩

/-- Every actual point over a local ring factors through an affine open. -/
theorem exists_affineOpenPoint [IsLocalRing S] (p : RingPoint R X S) :
    ∃ U : X.left.affineOpens, ∃ q : RingPoint R (openOver R X U.val) S,
      openPointMap R X S U.val q = p := by
  obtain ⟨U, hU, hp, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := X.left) (x := p.left (IsLocalRing.closedPoint S)) (U := ⊤) (by trivial)
  exact ⟨⟨U, hU⟩, openPointLift R X S U p
    ((range_subset_open_iff_closedPoint R X S U p).mpr hp),
    openPointMap_lift R X S U p _⟩

variable [TopologicalSpace S]

/-- The final topology on actual points obtained from all affine open charts. -/
@[instance_reducible]
def schemePointTopology : TopologicalSpace (RingPoint R X S) :=
  ⨆ U : X.left.affineOpens,
    @TopologicalSpace.coinduced (RingPoint R (openOver R X U.val) S) (RingPoint R X S)
      (openPointMap R X S U.val)
      (by letI : IsAffine (openOver R X U.val).left := U.property; exact inferInstance)

theorem schemePointTopology_isOpen_iff (V : Set (RingPoint R X S)) :
    IsOpen[schemePointTopology R X S] V ↔
      ∀ U : X.left.affineOpens,
        letI : IsAffine (openOver R X U.val).left := U.property
        IsOpen ((openPointMap R X S U.val) ⁻¹' V) := by
  rw [schemePointTopology, isOpen_iSup_iff]
  rfl

theorem schemePointTopology_continuous_chart (U : X.left.affineOpens) :
    letI : IsAffine (openOver R X U.val).left := U.property
    Continuous[inferInstance, schemePointTopology R X S] (openPointMap R X S U.val) := by
  let : IsAffine (openOver R X U.val).left := U.property
  exact continuous_iSup_rng (i := U) continuous_coinduced_rng

/-- The top open subscheme is the original relative scheme. -/
def openOverTopIso : openOver R X ⊤ ≅ X :=
  Over.isoMk X.left.topIso (by rfl)

/-- The affine-chart construction agrees with the published affine topology. -/
theorem schemePointTopology_eq_affine [IsAffine X.left] :
    schemePointTopology R X S =
      (inferInstance : TopologicalSpace (RingPoint R X S)) := by
  apply le_antisymm
  · apply iSup_le
    intro U
    let : IsAffine (openOver R X U.val).left := U.property
    apply continuous_iff_coinduced_le.mp
    apply (affineSchemePointHomeomorph R X S).isInducing.continuous_iff.mpr
    change Continuous (fun p : RingPoint R (openOver R X U.val) S =>
      affineSchemePointEquiv R X S (openPointMap R X S U.val p))
    have heq : (fun p : RingPoint R (openOver R X U.val) S =>
        affineSchemePointEquiv R X S (openPointMap R X S U.val p)) =
        (AlgPoint.precomp (affineCoordinatePullback R (openOverι R X U.val))) ∘
          (affineSchemePointHomeomorph R (openOver R X U.val) S) := by
      funext p
      exact affineSchemePointEquiv_natural R S (openOverι R X U.val) p
    rw [heq]
    exact (AlgPoint.continuous_precomp _).comp
      (affineSchemePointHomeomorph R (openOver R X U.val) S).continuous
  · let U : X.left.affineOpens := ⟨⊤, isAffineOpen_top X.left⟩
    let : IsAffine (openOver R X U.val).left := U.property
    have heq : (openPointMap R X S U.val) =
        (affineSchemePointIsoHomeomorph R S (openOverTopIso R X)) := by
      funext p
      exact (affineSchemePointIsoHomeomorph_apply R S (openOverTopIso R X) p).symm
    have htop : TopologicalSpace.coinduced (openPointMap R X S U.val) inferInstance =
        (inferInstance : TopologicalSpace (RingPoint R X S)) := by
      rw [heq]
      exact (affineSchemePointIsoHomeomorph R S (openOverTopIso R X)).coinduced_eq
    rw [← htop]
    exact le_iSup (fun U : X.left.affineOpens =>
      TopologicalSpace.coinduced (openPointMap R X S U.val)
        (by letI : IsAffine (openOver R X U.val).left := U.property; exact inferInstance)) U

end Langlands.AlgebraicGeometry.PointTopology
