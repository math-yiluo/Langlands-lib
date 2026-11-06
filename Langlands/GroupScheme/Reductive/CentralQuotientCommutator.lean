import Langlands.GroupScheme.Adjoint.CenterQuotientCommutator

/-! # Commutators in the preimage of a unipotent subgroup under a central quotient

This file generalizes the `Preimage` section of `Adjoint/CenterQuotientCommutator` from the
quotient by the full centre to the quotient by any subgroup functor `N ≤ center G`. Let
`q : G ⟶ Q` be an fppf quotient of a smooth affine group `G` with trivial unipotent radical
whose kernel is `N`, and let `j : C ⟶ Q` be a homomorphism from a smooth connected affine
unipotent group. For a rational point `h` of the preimage `H = q⁻¹(C)` whose image in `C` is
central, the commutator with `h` is a homomorphism from `H` into the centre of `G` that kills
the kernel of `H ⟶ C`; it descends to a central homomorphism from `C`, which is trivial.
Hence such an `h` commutes with all points of `H`. The arguments are those of the published
full-centre file; only the two places where the kernel was identified with the centre now use
the inclusion `N ≤ center G`. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry commutatorElement
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CentralQuotient

open CenterQuotient

section Preimage

variable {k : Type u} [Field k] {G Q C : GroupScheme (Spec (CommRingCat.of k))}
  (q : G ⟶ Q) (j : C ⟶ Q) {N : SubgroupFunctor G}

/-- A point killed by a central quotient map is central. -/
theorem mem_center_of_comp_eq_one (hq : RelativeRoot.IsFppfQuotient N q) (hN : N ≤ center G)
    {T : Over (Spec (CommRingCat.of k))} {x : T ⟶ G.X} (hx : x ≫ q.hom.hom = 1) :
    x ∈ (center G).carrier T := by
  apply hN
  rw [← hq.2.2.2, mem_range_kernelι_iff]
  exact hx

/-- Points of the preimage whose images in `C` commute have central commutator in `G`. -/
theorem commutator_mem_center (hq : RelativeRoot.IsFppfQuotient N q) (hN : N ≤ center G)
    {T : Over (Spec (CommRingCat.of k))} (a b : T ⟶ (SubgroupPreimage.groupScheme q j).X)
    (hab : Commute (a ≫ (SubgroupPreimage.projection q j).hom.hom)
      (b ≫ (SubgroupPreimage.projection q j).hom.hom)) :
    ⁅a ≫ (SubgroupPreimage.inclusion q j).hom.hom,
      b ≫ (SubgroupPreimage.inclusion q j).hom.hom⁆ ∈ (center G).carrier T := by
  apply mem_center_of_comp_eq_one q hq hN
  rw [commutatorElement_comp, Category.assoc,
    Category.assoc, (SubgroupPreimage.isPullback q j).w, ← Category.assoc a,
    ← Category.assoc b, ← commutatorElement_comp, commutatorElement_eq_one_iff_commute.mpr hab,
    MonObj.one_comp]

/-- Points of the kernel of the projection of the preimage are central in `G`. -/
theorem mem_center_of_comp_projection_eq_one (hq : RelativeRoot.IsFppfQuotient N q)
    (hN : N ≤ center G) {T : Over (Spec (CommRingCat.of k))}
    (a : T ⟶ (SubgroupPreimage.groupScheme q j).X)
    (ha : a ≫ (SubgroupPreimage.projection q j).hom.hom = 1) :
    a ≫ (SubgroupPreimage.inclusion q j).hom.hom ∈ (center G).carrier T := by
  apply mem_center_of_comp_eq_one q hq hN
  rw [Category.assoc, (SubgroupPreimage.isPullback q j).w, ← Category.assoc, ha,
    MonObj.one_comp]

variable (hq : RelativeRoot.IsFppfQuotient N q) (hN : N ≤ center G)
  (h : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ (SubgroupPreimage.groupScheme q j).X)
  (hcen : h ≫ (SubgroupPreimage.projection q j).hom.hom ∈ (center C).carrier _)

include hq hN hcen in
/-- The commutator of `h` with a point of the preimage is central in `G`, because the image
of `h` in `C` is central. -/
theorem commutator_rational_mem_center {T : Over (Spec (CommRingCat.of k))}
    (y : T ⟶ (SubgroupPreimage.groupScheme q j).X) :
    ⁅toUnit T ≫ h ≫ (SubgroupPreimage.inclusion q j).hom.hom,
      y ≫ (SubgroupPreimage.inclusion q j).hom.hom⁆ ∈ (center G).carrier T := by
  have hab : Commute ((toUnit T ≫ h) ≫ (SubgroupPreimage.projection q j).hom.hom)
      (y ≫ (SubgroupPreimage.projection q j).hom.hom) := by
    rw [Category.assoc]
    exact hcen T (toUnit T) _
  have := commutator_mem_center q j hq hN (toUnit T ≫ h) y hab
  rwa [Category.assoc] at this

/-- The commutator with the fixed rational point `h` of the preimage, on the points of the
preimage. It is multiplicative because its values are central. -/
def commutatorPoints (T : Over (Spec (CommRingCat.of k))) :
    (T ⟶ (SubgroupPreimage.groupScheme q j).X) →* (T ⟶ G.X) where
  toFun x := ⁅toUnit T ≫ h ≫ (SubgroupPreimage.inclusion q j).hom.hom,
    x ≫ (SubgroupPreimage.inclusion q j).hom.hom⁆
  map_one' := by
    rw [MonObj.one_comp, commutatorElement_one_right]
  map_mul' x y := by
    rw [MonObj.mul_comp]
    exact commutatorElement_mul_right_of_commute _ _ _ (commute_of_mem_center
      (commutator_rational_mem_center q j hq hN h hcen y)
      (x ≫ (SubgroupPreimage.inclusion q j).hom.hom))

theorem commutatorPoints_apply (T : Over (Spec (CommRingCat.of k)))
    (x : T ⟶ (SubgroupPreimage.groupScheme q j).X) :
    commutatorPoints q j hq hN h hcen T x =
      ⁅toUnit T ≫ h ≫ (SubgroupPreimage.inclusion q j).hom.hom,
        x ≫ (SubgroupPreimage.inclusion q j).hom.hom⁆ :=
  rfl

theorem commutatorPoints_naturality {T T' : Over (Spec (CommRingCat.of k))} (a : T' ⟶ T)
    (x : T ⟶ (SubgroupPreimage.groupScheme q j).X) :
    commutatorPoints q j hq hN h hcen T' (a ≫ x) = a ≫ commutatorPoints q j hq hN h hcen T x := by
  rw [commutatorPoints_apply, commutatorPoints_apply, comp_commutatorElement,
    ← Category.assoc a (toUnit T), comp_toUnit, Category.assoc]

/-- The commutator homomorphism `x ↦ ⁅h, x⁆` from the preimage to `G`. -/
def commutatorHom : SubgroupPreimage.groupScheme q j ⟶ G :=
  homOfPoints (commutatorPoints q j hq hN h hcen) (commutatorPoints_naturality q j hq hN h hcen)

theorem comp_commutatorHom {T : Over (Spec (CommRingCat.of k))}
    (x : T ⟶ (SubgroupPreimage.groupScheme q j).X) :
    x ≫ (commutatorHom q j hq hN h hcen).hom.hom =
      ⁅toUnit T ≫ h ≫ (SubgroupPreimage.inclusion q j).hom.hom,
        x ≫ (SubgroupPreimage.inclusion q j).hom.hom⁆ :=
  comp_homOfPoints _ _ T x

theorem range_commutatorHom_le_center :
    SubgroupFunctor.range (commutatorHom q j hq hN h hcen) ≤ center G := by
  intro T x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  rw [comp_commutatorHom]
  exact commutator_rational_mem_center q j hq hN h hcen y

include hq hN hcen

/-- **Rational points over central points are central in the preimage.** For a smooth affine
`G` with trivial unipotent radical, an fppf quotient `q` of `G` by a central subgroup functor
with affine target, and a smooth connected affine unipotent `C ⟶ Q`, a rational point of the
preimage `H` with central image in `C` commutes in `G` with every point of `H`. -/
theorem commute_preimage [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (hG : HasTrivialUnipotentRadical G) [IsAffineHom Q.X.hom] [Smooth C.X.hom]
    [IsAffineHom C.X.hom] [ConnectedSpace C.X.left] (hu : IsUnipotent C)
    {T : Over (Spec (CommRingCat.of k))} (x : T ⟶ (SubgroupPreimage.groupScheme q j).X) :
    Commute (toUnit T ≫ h ≫ (SubgroupPreimage.inclusion q j).hom.hom)
      (x ≫ (SubgroupPreimage.inclusion q j).hom.hom) := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsAffine Q.X.left := isAffine_of_isAffineHom Q.X.hom
  have : Flat q.hom.hom.left := hq.1
  have : Surjective q.hom.hom.left := hq.2.1
  have : QuasiCompact q.hom.hom.left := inferInstance
  have : Flat (SubgroupPreimage.projection q j).hom.hom.left :=
    SubgroupPreimage.flat_projection q j
  have : Surjective (SubgroupPreimage.projection q j).hom.hom.left :=
    SubgroupPreimage.surjective_projection q j
  have : QuasiCompact (SubgroupPreimage.projection q j).hom.hom.left :=
    MorphismProperty.of_isPullback (SubgroupPreimage.isPullback_scheme q j) inferInstance
  obtain ⟨Z, z, hzc, hz⟩ := center_hasClosedRepresentative (G := G)
  have : Mono z.hom.hom := hz.1
  set ψ := commutatorHom q j hq hN h hcen with hψ
  have hψc : SubgroupFunctor.range ψ ≤ SubgroupFunctor.range z := by
    rw [hz.2]
    exact range_commutatorHom_le_center q j hq hN h hcen
  let ψ' : SubgroupPreimage.groupScheme q j ⟶ Z :=
    SubgroupFunctor.IsRepresentedBy.factorHom hz ψ (hz.2 ▸ hψc)
  have hψ' : ψ' ≫ z = ψ := SubgroupFunctor.IsRepresentedBy.factorHom_comp hz ψ _
  have hk : kernelι (SubgroupPreimage.projection q j) ≫ ψ' = 0 := by
    apply Grp.hom_ext
    change (kernelι (SubgroupPreimage.projection q j)).hom.hom ≫ ψ'.hom.hom = 1
    apply (cancel_mono z.hom.hom).mp
    have hψψ : ψ'.hom.hom ≫ z.hom.hom = ψ.hom.hom :=
      congrArg (fun g => g.hom.hom) hψ'
    rw [Category.assoc, hψψ, MonObj.one_comp, hψ, comp_commutatorHom,
      commutatorElement_eq_one_iff_commute]
    refine (commute_of_mem_center
      (mem_center_of_comp_projection_eq_one q j hq hN _ ?_) _).symm
    exact (mem_range_kernelι_iff (SubgroupPreimage.projection q j) _).mp
      (SubgroupFunctor.mem_range.mpr ⟨𝟙 _, Category.id_comp _⟩)
  let d : C ⟶ Z := FpqcHomDescent.hom (SubgroupPreimage.projection q j) ψ' hk
  have hd : SubgroupPreimage.projection q j ≫ d = ψ' := FpqcHomDescent.fac _ _ _
  have hcent : IsCentral (d ≫ z) := by
    intro T' v
    rw [← hz.2, Grp.comp_hom_hom, ← Category.assoc]
    exact SubgroupFunctor.mem_range.mpr ⟨_, rfl⟩
  have h1 := hom_eq_one_of_isCentral hG (d ≫ z) hu hcent
  have hψ1 : ψ.hom.hom = 1 := by
    have : ψ = SubgroupPreimage.projection q j ≫ (d ≫ z) := by
      rw [← Category.assoc, hd, hψ']
    rw [this, Grp.comp_hom_hom, h1, MonObj.comp_one]
  have hx := comp_commutatorHom q j hq hN h hcen x
  rw [← hψ, hψ1, MonObj.comp_one] at hx
  exact commutatorElement_eq_one_iff_commute.mp hx.symm

/-- In particular such a rational point commutes in `G` with the rational points of `H`. -/
theorem commute_rational_preimage [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (hG : HasTrivialUnipotentRadical G) [IsAffineHom Q.X.hom] [Smooth C.X.hom]
    [IsAffineHom C.X.hom] [ConnectedSpace C.X.left] (hu : IsUnipotent C)
    (h' : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ (SubgroupPreimage.groupScheme q j).X) :
    Commute (h ≫ (SubgroupPreimage.inclusion q j).hom.hom)
      (h' ≫ (SubgroupPreimage.inclusion q j).hom.hom) := by
  have := commute_preimage q j hq hN h hcen hG hu h'
  have e : toUnit (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ≫ h = h := by
    have e0 : toUnit (Over.mk (𝟙 (Spec (CommRingCat.of k)))) =
        (𝟙 (Over.mk (𝟙 (Spec (CommRingCat.of k)))) : _ ⟶ 𝟙_ _) :=
      toUnit_unique _ _
    rw [e0, Category.id_comp]
  rwa [← Category.assoc, e] at this

omit hcen in
/-- **Rational points over central points commute.** Two rational points of `G` whose images
in `Q` are images of rational points of `C`, the first of which is central in `C`, commute. -/
theorem commute_of_lift [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (hG : HasTrivialUnipotentRadical G) [IsAffineHom Q.X.hom] [Smooth C.X.hom]
    [IsAffineHom C.X.hom] [ConnectedSpace C.X.left] (hu : IsUnipotent C)
    {x x' : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X}
    {c c' : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ C.X}
    (hx : x ≫ q.hom.hom = c ≫ j.hom.hom) (hx' : x' ≫ q.hom.hom = c' ≫ j.hom.hom)
    (hc : c ∈ (center C).carrier _) : Commute x x' := by
  have hl := (SubgroupPreimage.isPullback q j).lift_fst x c hx
  have hl' := (SubgroupPreimage.isPullback q j).lift_fst x' c' hx'
  have hcen' : (SubgroupPreimage.isPullback q j).lift x c hx ≫
      (SubgroupPreimage.projection q j).hom.hom ∈ (center C).carrier _ := by
    rwa [(SubgroupPreimage.isPullback q j).lift_snd]
  have := commute_rational_preimage q j hq hN _ hcen' hG hu
    ((SubgroupPreimage.isPullback q j).lift x' c' hx')
  rwa [hl, hl'] at this

end Preimage

end Langlands.GroupScheme.CentralQuotient
