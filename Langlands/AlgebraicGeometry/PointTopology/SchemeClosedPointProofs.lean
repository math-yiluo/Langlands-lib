import Langlands.AlgebraicGeometry.PointTopology.SchemeOpenPointProofs
import Langlands.AlgebraicGeometry.PointTopology.SchemeClosedPointStatements
import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeMapProofs
import Mathlib.Topology.LocalAtTarget

/-!
# Closed immersions on actual scheme point spaces
-/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R : Type u) [CommRing R]

/-- Restriction of an actual relative morphism to an open of its target. -/
def restrictedOver {X Y : Over (Spec (CommRingCat.of R))}
    (f : X ⟶ Y) (U : Y.left.Opens) :
    openOver R X (f.left ⁻¹ᵁ U) ⟶ openOver R Y U :=
  Over.homMk (f.left ∣_ U) (by
    change (f.left ∣_ U) ≫ (U.ι ≫ Y.hom) = (f.left ⁻¹ᵁ U).ι ≫ X.hom
    calc
      _ = ((f.left ∣_ U) ≫ U.ι) ≫ Y.hom := (Category.assoc _ _ _).symm
      _ = ((f.left ⁻¹ᵁ U).ι ≫ f.left) ≫ Y.hom :=
        congrArg (fun g => g ≫ Y.hom) (morphismRestrict_ι f.left U)
      _ = (f.left ⁻¹ᵁ U).ι ≫ (f.left ≫ Y.hom) := Category.assoc _ _ _
      _ = _ := congrArg (fun g => (f.left ⁻¹ᵁ U).ι ≫ g) (Over.w f))

@[simp] theorem restrictedOver_fac {X Y : Over (Spec (CommRingCat.of R))}
    (f : X ⟶ Y) (U : Y.left.Opens) :
    restrictedOver R f U ≫ openOverι R Y U = openOverι R X (f.left ⁻¹ᵁ U) ≫ f := by
  apply Over.OverMorphism.ext
  exact morphismRestrict_ι f.left U

variable (S : Type u) [CommRing S] [Algebra R S]

/-- The actual restriction square commutes on point carriers. -/
theorem restrictedOverPoint_factor {X Y : Over (Spec (CommRingCat.of R))}
    (f : X ⟶ Y) (U : Y.left.Opens) :
    (fun p : RingPoint R X S => (p ≫ f : RingPoint R Y S)) ∘
      openPointMap R X S (f.left ⁻¹ᵁ U) =
    openPointMap R Y S U ∘
      (fun q : RingPoint R (openOver R X (f.left ⁻¹ᵁ U)) S =>
        (q ≫ restrictedOver R f U : RingPoint R (openOver R Y U) S)) := by
  funext q
  dsimp only [RingPoint] at q
  change (q ≫ openOverι R X _) ≫ f = (q ≫ restrictedOver R f U) ≫ openOverι R Y U
  exact (Category.assoc q _ _).trans
    ((congrArg (fun t => q ≫ t) (restrictedOver_fac R f U).symm).trans
      (Category.assoc q _ _).symm)

/-- Chart containment of the image detects factorization through the preimage open. -/
theorem preimage_chart_subset_range {X Y : Over (Spec (CommRingCat.of R))}
    (f : X ⟶ Y) (U : Y.left.Opens) :
    (fun p : RingPoint R X S => (p ≫ f : RingPoint R Y S)) ⁻¹'
      Set.range (openPointMap R Y S U) ⊆
        Set.range (openPointMap R X S (f.left ⁻¹ᵁ U)) := by
  intro p hp
  obtain ⟨q, hq⟩ := hp
  have hpU : Set.range (p ≫ f : RingPoint R Y S).left ⊆ U :=
    (congrArg (fun z : RingPoint R Y S => Set.range z.left ⊆ U) hq).mp
      (openPointEquiv R Y S U q).property
  have hr : Set.range p.left ⊆ f.left ⁻¹ᵁ U := by
    rintro z ⟨a, rfl⟩
    exact hpU ⟨a, rfl⟩
  exact ⟨openPointLift R X S (f.left ⁻¹ᵁ U) p hr,
    openPointMap_lift R X S (f.left ⁻¹ᵁ U) p hr⟩

/-- The point-map image, tested in a target chart, is the actual restricted image. -/
theorem preimage_range_schemePointMap {X Y : Over (Spec (CommRingCat.of R))}
    (f : X ⟶ Y) (U : Y.left.Opens) :
    openPointMap R Y S U ⁻¹'
      Set.range (fun p : RingPoint R X S => (p ≫ f : RingPoint R Y S)) =
    Set.range (fun q : RingPoint R (openOver R X (f.left ⁻¹ᵁ U)) S =>
      (q ≫ restrictedOver R f U : RingPoint R (openOver R Y U) S)) := by
  ext q
  constructor
  · rintro ⟨p, hpq⟩
    have hpU : Set.range (p ≫ f : RingPoint R Y S).left ⊆ U :=
      (congrArg (fun z : RingPoint R Y S => Set.range z.left ⊆ U) hpq).mpr
        (openPointEquiv R Y S U q).property
    have hr : Set.range p.left ⊆ f.left ⁻¹ᵁ U := by
      rintro z ⟨a, rfl⟩
      exact hpU ⟨a, rfl⟩
    let r := openPointLift R X S (f.left ⁻¹ᵁ U) p hr
    have hrp : openPointMap R X S (f.left ⁻¹ᵁ U) r = p :=
      openPointMap_lift R X S (f.left ⁻¹ᵁ U) p hr
    refine ⟨r, ?_⟩
    apply openPointMap_injective R Y S U
    exact (congrFun (restrictedOverPoint_factor R S f U) r).symm.trans
      ((congrArg (fun p : RingPoint R X S => (p ≫ f : RingPoint R Y S)) hrp).trans hpq)
  · rintro ⟨r, rfl⟩
    exact ⟨openPointMap R X S (f.left ⁻¹ᵁ U) r,
      congrFun (restrictedOverPoint_factor R S f U) r⟩

variable [TopologicalSpace S] [IsLocalRing S] [ContinuousMul S] [IsOpenUnits S]

/-- A closed immersion gives an embedding for the actual final scheme-point topologies. -/
theorem isEmbedding_schemeClosedPointMap
    {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y) [IsClosedImmersion f.left] :
    letI : TopologicalSpace (RingPoint R X S) := schemePointTopology R X S
    letI : TopologicalSpace (RingPoint R Y S) := schemePointTopology R Y S
    IsEmbedding (X := RingPoint R X S) (Y := RingPoint R Y S)
      (fun p : RingPoint R X S => (p ≫ f : RingPoint R Y S)) := by
  let : TopologicalSpace (RingPoint R X S) := schemePointTopology R X S
  let : TopologicalSpace (RingPoint R Y S) := schemePointTopology R Y S
  let P : RingPoint R X S → RingPoint R Y S := fun p => p ≫ f
  have hP : Continuous P := schemePointContinuity_proof R S X Y f
  let C : Y.left.affineOpens → TopologicalSpace.Opens (RingPoint R Y S) :=
    fun U => ⟨Set.range (openPointMap R Y S U.val),
      (isOpenEmbedding_schemeAffineChart R S Y U).isOpen_range⟩
  let V : Y.left.affineOpens → Type u :=
    fun U => RingPoint R (openOver R X (f.left ⁻¹ᵁ U.val)) S
  let (U : Y.left.affineOpens) : TopologicalSpace (V U) := by
    let : IsAffine (openOver R X (f.left ⁻¹ᵁ U.val)).left := U.property.preimage f.left
    exact inferInstanceAs (TopologicalSpace (RingPoint R (openOver R X (f.left ⁻¹ᵁ U.val)) S))
  let iV : (U : Y.left.affineOpens) → V U → RingPoint R X S :=
    fun U => openPointMap R X S (f.left ⁻¹ᵁ U.val)
  apply isEmbedding_of_iSup_eq_top_of_preimage_subset_range P hP C ?_ V iV ?_ ?_ ?_
  · intro y hy
    obtain ⟨U, q, hq⟩ := exists_affineOpenPoint R Y S y
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨U, q, hq⟩
  · intro U
    exact (isOpenEmbedding_schemeAffineChart R S X
      ⟨f.left ⁻¹ᵁ U.val, U.property.preimage f.left⟩).continuous
  · intro U
    exact preimage_chart_subset_range R S f U.val
  · intro U
    let : IsAffine (openOver R Y U.val).left := U.property
    let : IsAffine (openOver R X (f.left ⁻¹ᵁ U.val)).left := U.property.preimage f.left
    let : IsClosedImmersion (restrictedOver R f U.val).left :=
      IsZariskiLocalAtTarget.restrict (inferInstance : IsClosedImmersion f.left) U.val
    change IsEmbedding (P ∘ openPointMap R X S (f.left ⁻¹ᵁ U.val))
    have heq : P ∘ openPointMap R X S (f.left ⁻¹ᵁ U.val) =
        openPointMap R Y S U.val ∘
          (fun q : RingPoint R (openOver R X (f.left ⁻¹ᵁ U.val)) S =>
            (q ≫ restrictedOver R f U.val : RingPoint R (openOver R Y U.val) S)) :=
      restrictedOverPoint_factor R S f U.val
    exact heq.symm ▸ ((isOpenEmbedding_schemeAffineChart R S Y U).isEmbedding.comp
      (isEmbedding_affineSchemePointMap R S (restrictedOver R f U.val)))

/-- Hausdorff value rings give a closed embedding for every actual closed immersion. -/
theorem isClosedEmbedding_schemeClosedPointMap [T2Space S]
    {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y) [IsClosedImmersion f.left] :
    letI : TopologicalSpace (RingPoint R X S) := schemePointTopology R X S
    letI : TopologicalSpace (RingPoint R Y S) := schemePointTopology R Y S
    IsClosedEmbedding (X := RingPoint R X S) (Y := RingPoint R Y S)
      (fun p : RingPoint R X S => (p ≫ f : RingPoint R Y S)) := by
  let : TopologicalSpace (RingPoint R X S) := schemePointTopology R X S
  let : TopologicalSpace (RingPoint R Y S) := schemePointTopology R Y S
  refine ⟨isEmbedding_schemeClosedPointMap R S f, ?_⟩
  let P : RingPoint R X S → RingPoint R Y S := fun p => p ≫ f
  change IsClosed (Set.range P)
  apply isOpen_compl_iff.mp
  apply (schemePointTopology_isOpen_iff R Y S _).mpr
  intro U
  let : IsAffine (openOver R Y U.val).left := U.property
  let : IsAffine (openOver R X (f.left ⁻¹ᵁ U.val)).left := U.property.preimage f.left
  let : IsClosedImmersion (restrictedOver R f U.val).left :=
    IsZariskiLocalAtTarget.restrict (inferInstance : IsClosedImmersion f.left) U.val
  have hc := (isClosedEmbedding_affineSchemePointMap R S (restrictedOver R f U.val)).isClosed_range
  change IsOpen ((openPointMap R Y S U.val ⁻¹' Set.range P)ᶜ)
  have hr : openPointMap R Y S U.val ⁻¹' Set.range P =
      Set.range (fun q : RingPoint R (openOver R X (f.left ⁻¹ᵁ U.val)) S =>
        (q ≫ restrictedOver R f U.val : RingPoint R (openOver R Y U.val) S)) :=
    preimage_range_schemePointMap R S f U.val
  exact (congrArg (fun t : Set (RingPoint R (openOver R Y U.val) S) => IsOpen tᶜ)
    hr).mpr hc.isOpen_compl

/-- The grouped closed-immersion target, with Hausdorffness only for closedness. -/
theorem schemeClosedPointProperties_proof
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [TopologicalSpace S] [IsLocalRing S] [ContinuousMul S] [IsOpenUnits S] :
    SchemePointClosedImmersionProperties R S := by
  intro X Y f _
  let : TopologicalSpace (RingPoint R X S) := schemePointTopology R X S
  let : TopologicalSpace (RingPoint R Y S) := schemePointTopology R Y S
  refine ⟨isEmbedding_schemeClosedPointMap R S f, ?_⟩
  intro _
  exact isClosedEmbedding_schemeClosedPointMap R S f

end Langlands.AlgebraicGeometry.PointTopology
