import Langlands.GroupScheme.IntegralModel.CongruenceTower
import Langlands.BruhatTits.IntegralModels.RelativeComponent
import Mathlib.AlgebraicGeometry.OpenImmersion

/-! # Positive congruence kernels through an open model inclusion -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Sections

variable {B T : Scheme.{u}} (b : T ⟶ B) (G : GroupScheme B)

/-- Equality after restriction is equality of the actual restricted scheme maps. -/
theorem baseChangeSectionHom_eq_iff (x y : Over.mk (𝟙 B) ⟶ G.X) :
    baseChangeSectionHom b G x = baseChangeSectionHom b G y ↔
      b ≫ x.left = b ≫ y.left := by
  constructor
  · intro h
    have h' := congrArg
      (fun z : Over.mk (𝟙 T) ⟶ ((baseChange b).obj G).X =>
        z.left ≫ pullback.fst G.X.hom b) h
    simpa only [baseChangeSectionHom_fst] using h'
  · intro h
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simpa only [baseChangeSectionHom_fst] using h
    · exact (baseChangeSectionHom b G x).w.trans
        (baseChangeSectionHom b G y).w.symm

end Sections

namespace IntegralModel

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
    {G H : GroupScheme (Spec (CommRingCat.of K))}
    {N : IntegralModel R K G} {M : IntegralModel R K H} {f : G ⟶ H}
    (φ : N.Hom M f)

/-- The original model inclusion on positive congruence kernels. -/
def Hom.congruenceKernelMap (n : ℕ+) :
    N.congruenceKernelAt n →* M.congruenceKernelAt n where
  toFun x := ⟨rationalPoints.map φ.hom x, φ.map_mem_congruenceKernelAt n x.property⟩
  map_one' := Subtype.ext (map_one (rationalPoints.map φ.hom))
  map_mul' x y := Subtype.ext (map_mul (rationalPoints.map φ.hom) x.val y.val)

@[simp] theorem Hom.congruenceKernelMap_val (n : ℕ+) (x : N.congruenceKernelAt n) :
    (φ.congruenceKernelMap n x).val = rationalPoints.map φ.hom x := rfl

/-- Restriction reflects congruence through a scheme-monomorphic model map. -/
theorem Hom.mem_congruenceKernelAt_iff
    [Mono φ.hom.hom.hom.left] (n : ℕ+) (y : N.integralSections) :
    rationalPoints.map φ.hom y ∈ M.congruenceKernelAt n ↔
      y ∈ N.congruenceKernelAt n := by
  have hone : rationalPoints.map φ.hom (1 : N.integralSections) =
      (1 : M.integralSections) := map_one _
  change M.reductionAt n (rationalPoints.map φ.hom y) = 1 ↔
    N.reductionAt n y = 1
  rw [← map_one (M.reductionAt n), ← map_one (N.reductionAt n)]
  change baseChangeSectionHom (congruenceBaseMap R n) M.group
      (rationalPoints.map φ.hom y) =
      baseChangeSectionHom (congruenceBaseMap R n) M.group 1 ↔
    baseChangeSectionHom (congruenceBaseMap R n) N.group y =
      baseChangeSectionHom (congruenceBaseMap R n) N.group 1
  rw [baseChangeSectionHom_eq_iff, baseChangeSectionHom_eq_iff]
  rw [← hone]
  change (congruenceBaseMap R n ≫ y.left) ≫ φ.hom.hom.hom.left =
      (congruenceBaseMap R n ≫ (1 : N.integralSections).left) ≫
        φ.hom.hom.hom.left ↔ _
  exact cancel_mono _

/-- A positive congruence section of the target factors through every supplied
open subgroup model. The statement concerns the original sections, not a
replacement generic point. -/
theorem Hom.exists_congruenceKernelAt_preimage
    [IsOpenImmersion φ.hom.hom.hom.left] (n : ℕ+)
    (x : M.integralSections) (hx : x ∈ M.congruenceKernelAt n) :
    ∃ y : N.integralSections,
      y ∈ N.congruenceKernelAt n ∧ rationalPoints.map φ.hom y = x := by
  have hx1 : x ∈ M.congruenceKernel := by
    rw [← M.congruenceKernelAt_one]
    exact M.congruenceKernelAt_antitone (show (1 : ℕ+) ≤ n from one_le) hx
  have hred : M.reduction x = M.reduction 1 := by
    rw [(M.mem_congruenceKernel x).mp hx1, map_one]
  have hres : residueBaseMap R ≫ x.left =
      residueBaseMap R ≫ (1 : M.integralSections).left :=
    (baseChangeSectionHom_eq_iff (residueBaseMap R) M.group x 1).mp hred
  have hclosed : residueBaseMap R
      (IsLocalRing.closedPoint (IsLocalRing.ResidueField R)) =
        IsLocalRing.closedPoint R :=
    IsLocalRing.comap_closedPoint (IsLocalRing.residue R)
  have hxclosed : x.left (IsLocalRing.closedPoint R) =
      (1 : M.integralSections).left (IsLocalRing.closedPoint R) := by
    have hp := congrArg
      (fun g : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶ M.group.X.left =>
        g (IsLocalRing.closedPoint (IsLocalRing.ResidueField R))) hres
    change x.left ((residueBaseMap R)
        (IsLocalRing.closedPoint (IsLocalRing.ResidueField R))) =
      (1 : M.integralSections).left ((residueBaseMap R)
        (IsLocalRing.closedPoint (IsLocalRing.ResidueField R))) at hp
    rw [hclosed] at hp
    exact hp
  have hone : (1 : N.integralSections).left ≫ φ.hom.hom.hom.left =
      (1 : M.integralSections).left :=
    congrArg (fun y : M.integralSections => y.left)
      (map_one (rationalPoints.map φ.hom))
  have hpoint : x.left (IsLocalRing.closedPoint R) ∈
      Set.range φ.hom.hom.hom.left := by
    rw [hxclosed, ← hone, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  have hrange : Set.range x.left ⊆ Set.range φ.hom.hom.hom.left := by
    rintro _ ⟨z, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint z).map x.left.continuous).mem_open
      (IsOpenImmersion.isOpen_range _) hpoint
  let l := IsOpenImmersion.lift φ.hom.hom.hom.left x.left hrange
  have hl : l ≫ φ.hom.hom.hom.left = x.left := IsOpenImmersion.lift_fac _ _ _
  let y : N.integralSections := Over.homMk l (by
    rw [← Over.w φ.hom.hom.hom, ← Category.assoc, hl, Over.w x])
  have hy : rationalPoints.map φ.hom y = x := by
    apply Over.OverMorphism.ext
    exact hl
  exact ⟨y, (φ.mem_congruenceKernelAt_iff n y).mp (hy ▸ hx), hy⟩

/-- The actual open inclusion induces a group equivalence on every positive
congruence kernel over the original local ring. -/
def Hom.openCongruenceKernelEquiv
    [IsOpenImmersion φ.hom.hom.hom.left] (n : ℕ+) :
    N.congruenceKernelAt n ≃* M.congruenceKernelAt n :=
  MulEquiv.ofBijective (φ.congruenceKernelMap n) ⟨by
    intro x y h
    apply Subtype.ext
    apply Over.OverMorphism.ext
    apply (cancel_mono φ.hom.hom.hom.left).mp
    exact congrArg (fun z : M.congruenceKernelAt n => z.val.left) h,
    by
      intro x
      obtain ⟨y, hy, h⟩ := φ.exists_congruenceKernelAt_preimage n x x.property
      exact ⟨⟨y, hy⟩, Subtype.ext h⟩⟩

@[simp] theorem Hom.openCongruenceKernelEquiv_val
    [IsOpenImmersion φ.hom.hom.hom.left] (n : ℕ+) (x : N.congruenceKernelAt n) :
    (φ.openCongruenceKernelEquiv n x).val = rationalPoints.map φ.hom x := rfl

variable {M' N' : IntegralModel R K G}

/-- Compatible identity-generic open models give the same literal positive
congruence subgroup in the supplied generic group. -/
theorem Hom.congruenceSubgroupAt_eq_of_open
    (φ : N'.Hom M' (𝟙 G)) [IsOpenImmersion φ.hom.hom.hom.left] (n : ℕ+) :
    N'.congruenceSubgroupAt n = M'.congruenceSubgroupAt n := by
  apply le_antisymm
  · intro g hg
    have h := φ.map_mem_congruenceSubgroupAt n hg
    simpa [rationalPoints.map] using h
  · rintro g ⟨x, hx, rfl⟩
    obtain ⟨y, hy, h⟩ := φ.exists_congruenceKernelAt_preimage n x hx
    refine ⟨y, hy, ?_⟩
    rw [← h, φ.integralPointMap_naturality]
    simp [rationalPoints.map]

end IntegralModel
end Langlands.GroupScheme

namespace Langlands.BruhatTits.IntegralModels.RelativeComponentModelData

open Langlands.GroupScheme

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    (D : RelativeComponentModelData R K G)

/-- Positive congruence subgroups of the supplied full and neutral models
coincide in the original generic rational-point group. -/
theorem neutral_congruenceSubgroupAt_eq (n : ℕ+) :
    D.neutral.congruenceSubgroupAt n = D.full.congruenceSubgroupAt n := by
  let : IsOpenImmersion D.inclusion.hom.hom.hom.left :=
    D.isRelativeComponent.isOpenImmersion
  exact D.inclusion.congruenceSubgroupAt_eq_of_open n

end Langlands.BruhatTits.IntegralModels.RelativeComponentModelData
