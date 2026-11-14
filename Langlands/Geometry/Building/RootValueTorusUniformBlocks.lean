import Langlands.Geometry.Building.RootValueTorusFieldMultipliers
import Langlands.Geometry.Building.RootValueTorusDouble
import Langlands.GroupScheme.Rational.RootSubgroupCentrality
import Langlands.GroupScheme.Rational.SemigroupRealizationProof
import Langlands.GroupScheme.Rational.SemigroupCommutatorProof
import Langlands.GroupScheme.Rational.CyclicRootFunctorComparisonProof
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-! # Uniform restriction fibres as joins of two scaled depth subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section UniformBlocks

variable {k : Type u} [Field k]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] {j : T.toGrp ⟶ G} [Mono j.hom.hom.left]
  {φ : RootFunctionFamily T G}

/-- The join of the multiplier-scaled depth subgroups for a character and its
double, both at the same lower depth. -/
def torusRestrictedRootDepthBlock (hφ : IsRootDatumValuation j φ)
    (f : S ⟶ T) (a : characterLattice S) (r : ℝ) :
    Subgroup (rationalPoints G) :=
  torusRestrictedRootDepthSubgroup hφ f a r ⊔
    torusRestrictedRootDepthSubgroup hφ f (2 • a) r

/-- At depth zero, the scaled and uniform fibre subgroups agree without a
root-system hypothesis or a restriction on the character. -/
theorem torusRestrictedRootDepthSubgroup_zero_eq_uniform
    (hφ : IsRootDatumValuation j φ) (f : S ⟶ T) (a : characterLattice S) :
    torusRestrictedRootDepthSubgroup hφ f a 0 =
      torusUniformRootDepthSubgroup hφ f a 0 := by
  unfold torusUniformRootDepthSubgroup
  apply le_antisymm
  · refine iSup_le fun c => iSup_le fun hc => iSup_le fun m =>
      iSup_le fun hm => iSup_le fun heq => ?_
    simpa only [mul_zero] using
      (le_iSup (fun c : {c : characterLattice T |
        c ∈ relativeRoots j ∧
          c ∈ RelativeRoot.characterSemigroupPreimage f (RelativeRoot.cyclicTail a 1)} =>
        hφ.filtrationSubgroup c.val 0)
        ⟨c, hc, m, by omega, hm, heq.symm⟩)
  · refine iSup_le fun c => ?_
    obtain ⟨m, _, hm, heq⟩ := c.property.2
    exact le_iSup_of_le c.val (le_iSup_of_le c.property.1
      (le_iSup_of_le m (le_iSup_of_le hm (le_iSup_of_le heq.symm (by
        simp only [mul_zero]
        exact le_rfl)))))

/-- At nonnegative depth, each scaled fibre subgroup lies in the uniform
fibre subgroup. -/
theorem torusRestrictedRootDepthSubgroup_le_uniform
    (hφ : IsRootDatumValuation j φ) (f : S ⟶ T)
    (a : characterLattice S) {r : ℝ} (hr : 0 ≤ r) :
    torusRestrictedRootDepthSubgroup hφ f a r ≤
      torusUniformRootDepthSubgroup hφ f a r := by
  refine iSup_le fun c => iSup_le fun hc => iSup_le fun m =>
    iSup_le fun hm => iSup_le fun heq => ?_
  have hdepth : r ≤ (m : ℝ) * r := by
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  exact (hφ.filtrationSubgroup_antitone c hdepth).trans
    (le_iSup_of_le ⟨c, hc, m, by omega, hm, heq.symm⟩ le_rfl)

/-- The two scaled depth subgroups generate a subgroup of the uniform fibre
at every nonnegative depth. -/
theorem torusRestrictedRootDepthBlock_le_uniform
    (hφ : IsRootDatumValuation j φ) (f : S ⟶ T)
    (a : characterLattice S) {r : ℝ} (hr : 0 ≤ r) :
    torusRestrictedRootDepthBlock hφ f a r ≤
      torusUniformRootDepthSubgroup hφ f a r := by
  apply sup_le
  · exact torusRestrictedRootDepthSubgroup_le_uniform hφ f a hr
  · refine iSup_le fun c => iSup_le fun hc => iSup_le fun m =>
      iSup_le fun hm => iSup_le fun heq => ?_
    have hdepth : r ≤ (m : ℝ) * r := by
      have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
      nlinarith
    have heq' : (m * 2) • a = f ≫ c := by
      rw [mul_comm, mul_nsmul]
      exact heq.symm
    exact (hφ.filtrationSubgroup_antitone c hdepth).trans
      (le_iSup_of_le ⟨c, hc, m * 2, by omega, by omega, heq'⟩ le_rfl)

variable [Smooth G.X.hom]

/-- The intersection of the two scaled factors is the doubled-character
subgroup at twice the depth. -/
theorem torusRestrictedRootDepthSubgroup_inf_double
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs j) (hφ : IsRootDatumValuation j φ)
    (f : S ⟶ T) (a : characterLattice S) (ha : a ≠ 0)
    {r : ℝ} (hr : 0 ≤ r) :
    torusRestrictedRootDepthSubgroup hφ f a r ⊓
      torusRestrictedRootDepthSubgroup hφ f (2 • a) r =
        torusRestrictedRootDepthSubgroup hφ f (2 • a) (2 * r) := by
  have hdouble := torusRestrictedRootDepthSubgroup_double_eq hS hT hE hφ f a ha r
  apply le_antisymm
  · rw [hdouble]
    exact inf_le_inf_left _
      (torusRestrictedRootDepthSubgroup_le_rootGroupPoints hS hT hφ f
        (2 • a) (hS.nsmul_ne_zero ha (by omega)) r)
  · apply le_inf
    · rw [hdouble]
      exact inf_le_left
    · exact torusRestrictedRootDepthSubgroup_antitone hφ f (2 • a) (by linarith)


/-- Exclusion of higher lower roots makes the two scaled factors commute,
so the block carrier is their set product. -/
theorem mem_torusRestrictedRootDepthBlock_iff_exists_mul_of_noHigherRoots
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hφ : IsRootDatumValuation j φ) (f : S ⟶ T)
    (a : characterLattice S) (ha : a ≠ 0)
    (hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots (CommGroupScheme.groupHom f ≫ j))
    (r : ℝ) (g : rationalPoints G) :
    g ∈ torusRestrictedRootDepthBlock hφ f a r ↔
      ∃ x ∈ torusRestrictedRootDepthSubgroup hφ f a r,
        ∃ z ∈ torusRestrictedRootDepthSubgroup hφ f (2 • a) r, x * z = g := by
  have hcentral := RelativeRoot.hasCentralDoubleSubgroup_of_noHigherRoots
    RelativeRoot.semigroupRealization RelativeRoot.semigroupCommutator
    RelativeRoot.cyclicRootFunctorComparison (inferInstance : Smooth G.X.hom)
    hS (CommGroupScheme.groupHom f ≫ j) ha hhigh
  let A := torusRestrictedRootDepthSubgroup hφ f a r
  let D := torusRestrictedRootDepthSubgroup hφ f (2 • a) r
  have hA : A ≤ rootGroupPoints (CommGroupScheme.groupHom f ≫ j) a :=
    torusRestrictedRootDepthSubgroup_le_rootGroupPoints hS hT hφ f a ha r
  have hD : D ≤ rootGroupPoints (CommGroupScheme.groupHom f ≫ j) (2 • a) :=
    torusRestrictedRootDepthSubgroup_le_rootGroupPoints hS hT hφ f (2 • a)
      (hS.nsmul_ne_zero ha (by omega)) r
  have hAD : A ≤ Subgroup.centralizer (D : Set (rationalPoints G)) := by
    intro x hx
    apply Subgroup.mem_centralizer_iff.mpr
    intro z hz
    exact (hcentral.2 (Over.mk (𝟙 _)) z x (hD hz) (hA hx)).eq
  change g ∈ ((A ⊔ D : Subgroup (rationalPoints G)) : Set (rationalPoints G)) ↔ _
  rw [Subgroup.coe_mul_of_left_le_normalizer_right A D
    (hAD.trans (Subgroup.centralizer_le_normalizer (D : Set (rationalPoints G))))]
  rfl

end UniformBlocks

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [Smooth G.X.hom]
  (i : S.toGrp ⟶ G) [Mono i.hom.hom.left]

local notation "b" => algebraBaseMap k K
local notation "S_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) S
local notation "G_K" => baseChanged k K G
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) i
local notation "a_K" a => characterLattice.baseChange b S a

private instance uniformBlocksExtendedAffine : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

variable {T : CommGroupScheme (Spec (CommRingCat.of K))}

/-- At an actual lower root, the uniform upper fibre is generated by the
scaled depth subgroups for that root and its double. This is an equality over
the extension field, with no assertion that its factors descend. -/
theorem torusUniformRootDepthSubgroup_eq_block
    {j : T.toGrp ⟶ G_K} [Mono j.hom.hom.left]
    {φ : RootFunctionFamily T G_K} (hφ : IsRootDatumValuation j φ)
    (hS : IsSplitTorus S.toGrp) (hR : HasRelativeRootSystem i)
    (f : S_K ⟶ T) (hfactor : CommGroupScheme.groupHom f ≫ j = i_K)
    {a : characterLattice S} (ha : a ∈ relativeRoots i)
    {r : ℝ} (hr : 0 ≤ r) :
    torusUniformRootDepthSubgroup hφ f (a_K a) r =
      torusRestrictedRootDepthBlock hφ f (a_K a) r := by
  apply le_antisymm
  · refine iSup_le fun c => ?_
    obtain ⟨m, _, hm, heq⟩ := c.property.2
    have hmroot := nsmul_mem_relativeRoots_of_torusField_restriction
      i hS f hfactor ha c.property.1 hm heq.symm
    rcases hR.eq_one_or_two_of_nsmul_mem ha hmroot with hm1 | hm2
    · subst m
      have heq' : f ≫ c.val = 1 • (a_K a) := heq.symm
      exact le_sup_of_le_left (le_iSup_of_le c.val (le_iSup_of_le c.property.1
        (le_iSup_of_le 1 (le_iSup_of_le (by omega : 0 < (1 : ℕ))
          (le_iSup_of_le heq' (by simp only [Nat.cast_one, one_mul]; exact le_rfl))))))
    · subst m
      have heq' : f ≫ c.val = 1 • (2 • (a_K a)) := by
        rw [one_nsmul]
        exact heq.symm
      exact le_sup_of_le_right (le_iSup_of_le c.val (le_iSup_of_le c.property.1
        (le_iSup_of_le 1 (le_iSup_of_le (by omega : 0 < (1 : ℕ))
          (le_iSup_of_le heq' (by simp only [Nat.cast_one, one_mul]; exact le_rfl))))))
  · exact torusRestrictedRootDepthBlock_le_uniform hφ f (a_K a) hr


end Langlands.Geometry.Building
