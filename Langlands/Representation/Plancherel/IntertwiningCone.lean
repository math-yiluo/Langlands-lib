import Langlands.GroupScheme.Rational.SubgroupRelativeRoots
import Langlands.Geometry.Building.RealTorusInvariantForm
import Langlands.Representation.Plancherel.SplitTorusRealPartLaws

/-! # Actual-root threshold regions for intertwining parameters -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RelativeRoot

namespace Langlands.Plancherel

variable {k : Type u} [Field k]
  {A T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- The strict root inequalities for an explicit form on the full character space. -/
def rootThresholdRegion (B : LinearMap.BilinForm ℝ (RealTorusSpace.Vstar A))
    (roots : Set (characterLattice A)) (R : ℝ) : Set (RealTorusSpace.Vstar A) :=
  {x | ∀ α ∈ roots, R < B x ((1 : ℝ) ⊗ₜ[ℤ] α)}

theorem mem_rootThresholdRegion (B : LinearMap.BilinForm ℝ (RealTorusSpace.Vstar A))
    (roots : Set (characterLattice A)) (R : ℝ) (x : RealTorusSpace.Vstar A) :
    x ∈ rootThresholdRegion B roots R ↔
      ∀ α ∈ roots, R < B x ((1 : ℝ) ⊗ₜ[ℤ] α) := Iff.rfl

theorem rootThresholdRegion_antitone_threshold
    (B : LinearMap.BilinForm ℝ (RealTorusSpace.Vstar A))
    (roots : Set (characterLattice A)) {R R' : ℝ} (h : R ≤ R') :
    rootThresholdRegion B roots R' ⊆ rootThresholdRegion B roots R :=
  fun _ hx α hα => lt_of_le_of_lt h (hx α hα)

theorem rootThresholdRegion_antitone_roots
    (B : LinearMap.BilinForm ℝ (RealTorusSpace.Vstar A))
    {roots roots' : Set (characterLattice A)} (h : roots ⊆ roots') (R : ℝ) :
    rootThresholdRegion B roots' R ⊆ rootThresholdRegion B roots R :=
  fun _ hx α hα => hx α (h hα)

@[simp] theorem rootThresholdRegion_empty
    (B : LinearMap.BilinForm ℝ (RealTorusSpace.Vstar A)) (R : ℝ) :
    rootThresholdRegion B ∅ R = Set.univ := by
  ext x
  simp [rootThresholdRegion]

/-- An integral positive direction yields a nonempty region for every real threshold.
This asserts nonemptiness in the real space, without a character-realization claim. -/
theorem rootThresholdRegion_nonempty_of_positivePairing
    (hA : IsSplitTorus A.toGrp)
    (B : LinearMap.BilinForm ℝ (RealTorusSpace.Vstar A)) (hB : B.Nondegenerate)
    (roots : Set (characterLattice A)) (ν : cocharacterLattice A)
    (hν : ∀ α ∈ roots, 0 < latticePairing A α ν) (R : ℝ) :
    (rootThresholdRegion B roots R).Nonempty := by
  let _ := hA.finite_realCharacterSpace
  let x := (B.toDual hB).symm ((RealTorusSpace.pair A).flip ((1 : ℝ) ⊗ₜ[ℤ] ν))
  have hx (α : characterLattice A) :
      B x ((1 : ℝ) ⊗ₜ[ℤ] α) = (latticePairing A α ν : ℝ) := by
    rw [LinearMap.BilinForm.apply_toDual_symm_apply]
    change RealTorusSpace.pair A ((1 : ℝ) ⊗ₜ[ℤ] α)
      ((1 : ℝ) ⊗ₜ[ℤ] ν) = _
    simp only [RealTorusSpace.pair_tmul_tmul, one_mul]
  let t : ℝ := max (R + 1) 1
  have ht : 0 ≤ t := le_trans zero_le_one (le_max_right _ _)
  have hRt : R < t := lt_of_lt_of_le (lt_add_one R) (le_max_left _ _)
  refine ⟨t • x, fun α hα => ?_⟩
  have hα1 : (1 : ℝ) ≤ (latticePairing A α ν : ℝ) := by
    have hi : (0 : ℤ) + 1 ≤ latticePairing A α ν :=
      Int.add_one_le_iff.mpr (hν α hα)
    exact_mod_cast hi
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul, hx]
  exact lt_of_lt_of_le hRt (by simpa using mul_le_mul_of_nonneg_left hα1 ht)

section ActualSubgroups

variable {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : A.toGrp ⟶ G)

/-- Threshold region indexed by both actual subgroup supports.
The second input must be identified with the intended opposite radical separately. -/
def intertwiningRegion (B : LinearMap.BilinForm ℝ (RealTorusSpace.Vstar A))
    (U Uop' : SubgroupFunctor G) (R : ℝ) : Set (RealTorusSpace.Vstar A) :=
  rootThresholdRegion B (intertwiningRelativeRoots i U Uop') R

theorem mem_intertwiningRegion_dynamic [Smooth G.X.hom]
    (hA : IsSplitTorus A.toGrp)
    (B : LinearMap.BilinForm ℝ (RealTorusSpace.Vstar A))
    (ν eta : cocharacterLattice A) (R : ℝ) (x : RealTorusSpace.Vstar A) :
    x ∈ intertwiningRegion i B
        (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i))
        (Dynamic.unipotent (CommGroupScheme.groupHom (-eta) ≫ i)) R ↔
      ∀ α ∈ relativeRoots i,
        0 < latticePairing A α ν → latticePairing A α eta < 0 →
          R < B x ((1 : ℝ) ⊗ₜ[ℤ] α) := by
  rw [intertwiningRegion, intertwiningRelativeRoots_dynamic i hA ν eta]
  simp only [mem_rootThresholdRegion, Set.mem_ofPred_eq, and_imp]

theorem intertwiningRegion_dynamic_nonempty [Smooth G.X.hom]
    (hA : IsSplitTorus A.toGrp)
    (B : LinearMap.BilinForm ℝ (RealTorusSpace.Vstar A)) (hB : B.Nondegenerate)
    (ν eta : cocharacterLattice A) (R : ℝ) :
    (intertwiningRegion i B
      (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i))
      (Dynamic.unipotent (CommGroupScheme.groupHom (-eta) ≫ i)) R).Nonempty := by
  apply rootThresholdRegion_nonempty_of_positivePairing hA B hB _ ν _ R
  intro α hα
  rw [intertwiningRelativeRoots_dynamic i hA ν eta] at hα
  exact hα.2.1

section InvariantForm

variable [Mono i.hom.hom.left] [Fintype (relativeWeylGroup i)]

/-- Specialization to the constructed positive invariant form.
No comparison with an ambient or another Levi form is implicit. -/
def invariantIntertwiningRegion (hA : IsSplitTorus A.toGrp)
    (U Uop' : SubgroupFunctor G) (R : ℝ) : Set (RealTorusSpace.Vstar A) :=
  intertwiningRegion i (RealTorusSpace.relativeWeylInvariantForm i hA) U Uop' R

theorem invariantIntertwiningRegion_dynamic_nonempty [Smooth G.X.hom]
    (hA : IsSplitTorus A.toGrp) (ν eta : cocharacterLattice A) (R : ℝ) :
    (invariantIntertwiningRegion i hA
      (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i))
      (Dynamic.unipotent (CommGroupScheme.groupHom (-eta) ≫ i)) R).Nonempty := by
  apply intertwiningRegion_dynamic_nonempty i hA
    (RealTorusSpace.relativeWeylInvariantForm i hA) _ ν eta R
  refine ⟨RealTorusSpace.relativeWeylInvariantForm_separatingLeft i hA, ?_⟩
  intro x hx
  by_contra h
  exact (ne_of_gt (RealTorusSpace.relativeWeylInvariantForm_pos i hA h)) (hx x)

end InvariantForm
end ActualSubgroups

/-- Explicit ambient/local comparison condition for the actual restriction map
and a specified real linear lift. It is not an existence theorem. -/
def CompatibleCharacterForms (f : A ⟶ T)
    (B_A : LinearMap.BilinForm ℝ (RealTorusSpace.Vstar A))
    (B_T : LinearMap.BilinForm ℝ (RealTorusSpace.Vstar T))
    (L : RealTorusSpace.Vstar A →ₗ[ℝ] RealTorusSpace.Vstar T) : Prop :=
  (∀ x, rationalCharacterRestrictReal (CommGroupScheme.groupHom f) (L x) = x) ∧
    ∀ x y, B_T (L x) y =
      B_A x (rationalCharacterRestrictReal (CommGroupScheme.groupHom f) y)

theorem CompatibleCharacterForms.root_inequality_iff
    {f : A ⟶ T} {B_A : LinearMap.BilinForm ℝ (RealTorusSpace.Vstar A)}
    {B_T : LinearMap.BilinForm ℝ (RealTorusSpace.Vstar T)}
    {L : RealTorusSpace.Vstar A →ₗ[ℝ] RealTorusSpace.Vstar T}
    (h : CompatibleCharacterForms f B_A B_T L)
    (x : RealTorusSpace.Vstar A) (β : characterLattice T) (R : ℝ) :
    R < B_T (L x) ((1 : ℝ) ⊗ₜ[ℤ] β) ↔
      R < B_A x ((1 : ℝ) ⊗ₜ[ℤ] characterRestrict (CommGroupScheme.groupHom f) β) := by
  rw [h.2, rationalCharacterRestrictReal_tmul]

theorem CompatibleCharacterForms.mem_rootThresholdRegion_iff
    {f : A ⟶ T} {B_A : LinearMap.BilinForm ℝ (RealTorusSpace.Vstar A)}
    {B_T : LinearMap.BilinForm ℝ (RealTorusSpace.Vstar T)}
    {L : RealTorusSpace.Vstar A →ₗ[ℝ] RealTorusSpace.Vstar T}
    (h : CompatibleCharacterForms f B_A B_T L)
    (roots : Set (characterLattice T)) (R : ℝ) (x : RealTorusSpace.Vstar A) :
    L x ∈ rootThresholdRegion B_T roots R ↔
      x ∈ rootThresholdRegion B_A
        (characterRestrict (CommGroupScheme.groupHom f) '' roots) R := by
  constructor
  · intro hx α hα
    obtain ⟨β, hβ, rfl⟩ := hα
    exact (h.root_inequality_iff x β R).mp (hx β hβ)
  · intro hx β hβ
    exact (h.root_inequality_iff x β R).mpr (hx _ ⟨β, hβ, rfl⟩)

section CharacterParameters

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {M G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

/-- Pullback of the actual-root region along the normalized real part of the
restriction of an actual point character to a specified split component. -/
def characterIntertwiningRegion (hA : IsSplitTorus A.toGrp) (j : A.toGrp ⟶ M)
    (i : A.toGrp ⟶ G) (B : LinearMap.BilinForm ℝ (RealTorusSpace.Vstar A))
    (U Uop' : SubgroupFunctor G) (R : ℝ) : Set (rationalPoints M →* ℂˣ) :=
  {χ | SplitTorus.normalizedRealPart hA (χ.comp (rationalPoints.map j)) ∈
    intertwiningRegion i B U Uop' R}

theorem mem_characterIntertwiningRegion (hA : IsSplitTorus A.toGrp) (j : A.toGrp ⟶ M)
    (i : A.toGrp ⟶ G) (B : LinearMap.BilinForm ℝ (RealTorusSpace.Vstar A))
    (U Uop' : SubgroupFunctor G) (R : ℝ) (χ : rationalPoints M →* ℂˣ) :
    χ ∈ characterIntertwiningRegion hA j i B U Uop' R ↔
      ∀ α ∈ intertwiningRelativeRoots i U Uop',
        R < B (SplitTorus.normalizedRealPart hA (χ.comp (rationalPoints.map j)))
          ((1 : ℝ) ⊗ₜ[ℤ] α) := Iff.rfl

/-- The same region on the published actual valuation-image characters of `M`. -/
def imageCharacterIntertwiningRegion (hA : IsSplitTorus A.toGrp) (j : A.toGrp ⟶ M)
    (i : A.toGrp ⟶ G) (B : LinearMap.BilinForm ℝ (RealTorusSpace.Vstar A))
    (U Uop' : SubgroupFunctor G) (R : ℝ) : Set (rationalImageCharacters M) :=
  {χ | rationalImageCharacterPullback M χ ∈
    characterIntertwiningRegion hA j i B U Uop' R}

end CharacterParameters

end Langlands.Plancherel
