import Langlands.Geometry.Building.RootValueTorusFieldRestriction
import Langlands.GroupScheme.Rational.RelativeRootMultiples
import Langlands.GroupScheme.Torus.WeightRestriction

/-! # Root restriction multipliers and uniform nonmultipliable depths -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section UniformDepth

variable {k : Type u} [Field k]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] {j : T.toGrp ⟶ G} [Mono j.hom.hom.left]
  {φ : RootFunctionFamily T G}

/-- The subgroup generated at one uniform depth by all actual roots in a
positive integral restriction fibre. -/
def torusUniformRootDepthSubgroup (hφ : IsRootDatumValuation j φ)
    (f : S ⟶ T) (a : characterLattice S) (r : ℝ) :
    Subgroup (rationalPoints G) :=
  ⨆ c : {c : characterLattice T |
    c ∈ relativeRoots j ∧
      c ∈ RelativeRoot.characterSemigroupPreimage f (RelativeRoot.cyclicTail a 1)},
    hφ.filtrationSubgroup c.val r

end UniformDepth

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

private instance fieldMultipliersExtendedAffine : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

variable {T : CommGroupScheme (Spec (CommRingCat.of K))}

omit [Mono i.hom.hom.left] in
/-- A positive restriction multiplier of an upper root gives an actual lower
root after reflecting the field base change. -/
theorem nsmul_mem_relativeRoots_of_torusField_restriction
    {j : T.toGrp ⟶ G_K} [Mono j.hom.hom.left]
    (hS : IsSplitTorus S.toGrp) (f : S_K ⟶ T)
    (hfactor : CommGroupScheme.groupHom f ≫ j = i_K)
    {a : characterLattice S} (ha : a ∈ relativeRoots i)
    {c : characterLattice T} (hc : c ∈ relativeRoots j)
    {m : ℕ} (hm : 0 < m) (heq : f ≫ c = m • (a_K a)) :
    m • a ∈ relativeRoots i := by
  have haK : (a_K a) ∈ relativeRoots i_K :=
    (mem_roots_baseChange_iff (K := K) G S hS i a).mpr ha
  have hne : f ≫ c ≠ 0 := by
    rw [heq]
    exact (hS.baseChange b).nsmul_ne_zero haK.1 (Nat.ne_of_gt hm)
  have hroot := (rootRestriction f j ⟨c, hc, hne⟩).property
  change f ≫ c ∈ relativeRoots (CommGroupScheme.groupHom f ≫ j) at hroot
  rw [hfactor, heq, ← map_nsmul] at hroot
  exact (mem_roots_baseChange_iff (K := K) G S hS i (m • a)).mp hroot

/-- At a lower root with no doubled root, every positive upper restriction
multiplier equals one. -/
theorem torusField_restriction_multiplier_eq_one_of_not_double
    {j : T.toGrp ⟶ G_K} [Mono j.hom.hom.left]
    (hS : IsSplitTorus S.toGrp) (hR : HasRelativeRootSystem i)
    (f : S_K ⟶ T) (hfactor : CommGroupScheme.groupHom f ≫ j = i_K)
    {a : characterLattice S} (ha : a ∈ relativeRoots i)
    (h2a : 2 • a ∉ relativeRoots i)
    {c : characterLattice T} (hc : c ∈ relativeRoots j)
    {m : ℕ} (hm : 0 < m) (heq : f ≫ c = m • (a_K a)) :
    m = 1 :=
  hR.eq_one_of_nsmul_mem_of_two_not_mem ha h2a
    (nsmul_mem_relativeRoots_of_torusField_restriction i hS f hfactor ha hc hm heq)

/-- For a nonmultipliable lower root, the multiplier-scaled generated
subgroup is exactly the subgroup generated at the original uniform depth.
The real depth is arbitrary. -/
theorem torusRestrictedRootDepthSubgroup_eq_uniform_of_not_double
    {j : T.toGrp ⟶ G_K} [Mono j.hom.hom.left]
    {φ : RootFunctionFamily T G_K} (hφ : IsRootDatumValuation j φ)
    (hS : IsSplitTorus S.toGrp) (hR : HasRelativeRootSystem i)
    (f : S_K ⟶ T) (hfactor : CommGroupScheme.groupHom f ≫ j = i_K)
    {a : characterLattice S} (ha : a ∈ relativeRoots i)
    (h2a : 2 • a ∉ relativeRoots i) (r : ℝ) :
    torusRestrictedRootDepthSubgroup hφ f (a_K a) r =
      torusUniformRootDepthSubgroup hφ f (a_K a) r := by
  unfold torusUniformRootDepthSubgroup
  apply le_antisymm
  · refine iSup_le fun c => iSup_le fun hc => iSup_le fun m =>
      iSup_le fun hm => iSup_le fun heq => ?_
    have hm1 := torusField_restriction_multiplier_eq_one_of_not_double
      i hS hR f hfactor ha h2a hc hm heq
    subst m
    simpa only [Nat.cast_one, one_mul] using
      (le_iSup (fun c : {c : characterLattice T |
        c ∈ relativeRoots j ∧
          c ∈ RelativeRoot.characterSemigroupPreimage f
            (RelativeRoot.cyclicTail (a_K a) 1)} =>
        hφ.filtrationSubgroup c.val r)
        ⟨c, hc, 1, le_rfl, by omega, heq.symm⟩)
  · refine iSup_le fun c => ?_
    obtain ⟨m, _, hm, heq⟩ := c.property.2
    have hm1 := torusField_restriction_multiplier_eq_one_of_not_double
      i hS hR f hfactor ha h2a c.property.1 hm heq.symm
    subst m
    exact le_iSup_of_le c.val (le_iSup_of_le c.property.1
      (le_iSup_of_le 1 (le_iSup_of_le (by omega : 0 < (1 : ℕ))
        (le_iSup_of_le heq.symm (by
          simp only [Nat.cast_one, one_mul]
          exact le_rfl)))))

end Langlands.Geometry.Building
