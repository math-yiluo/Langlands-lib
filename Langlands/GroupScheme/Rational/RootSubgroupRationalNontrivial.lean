import Langlands.GroupScheme.Rational.RootNonmultipliableFactors
import Langlands.GroupScheme.Rational.RootSupportFiniteness
import Langlands.GroupScheme.Rational.RootSubgroupNontrivial
import Langlands.GroupScheme.Rational.RootSubgroupLieImage
import Langlands.GroupScheme.Rational.RootSubgroupMultipleInclusion
import Langlands.GroupScheme.Rational.RootSubgroupVectorTransport

/-! # Nonidentity rational points in every actual relative root subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}

/-- The natural multiples of a nonzero split-torus character are distinct. -/
theorem IsSplitTorus.nsmul_character_injective (hT : IsSplitTorus T.toGrp)
    {a : characterLattice T} (ha : a ≠ 0) :
    Function.Injective (fun n : ℕ => n • a) := by
  obtain ⟨D, hD, ν, hν⟩ := hT.exists_pairing_eq_pos ha
  intro m n h
  have hp := congrArg (fun χ => latticePairing T χ ν) h
  simp only [map_nsmul, LinearMap.smul_apply, hν, nsmul_eq_mul] at hp
  exact_mod_cast mul_right_cancel₀ (by exact_mod_cast hD.ne' : (D : ℤ) ≠ 0) hp

namespace RelativeRoot

variable [IsAffineHom G.X.hom]

/-- Finite actual weight support supplies a root on the positive integral ray
with no second or higher positive multiple. No root-system premise is used. -/
theorem exists_maximal_root_multiple [LocallyOfFiniteType G.X.hom]
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    {a : characterLattice T} (ha : a ∈ relativeRoots i) :
    ∃ N : ℕ, 0 < N ∧ N • a ∈ relativeRoots i ∧ HasNoHigherRoots i (N • a) := by
  have hfinite : {n : ℕ | n • a ∈ relativeRoots i}.Finite :=
    (hT.finite_relativeRoots i).preimage (hT.nsmul_character_injective ha.1).injOn
  obtain ⟨N, hN, hmax⟩ := hfinite.exists_maximal ⟨1, by simpa using ha⟩
  have hNpos : 0 < N := by
    by_contra h
    have hzero : N = 0 := by omega
    exact hN.1 (by rw [hzero, zero_smul])
  refine ⟨N, hNpos, hN, ?_⟩
  intro n hn hroot
  have hprod : n * N ∈ {m : ℕ | m • a ∈ relativeRoots i} := by
    change (n * N) • a ∈ relativeRoots i
    simpa only [smul_smul] using hroot
  have hle : n * N ≤ N := hmax hprod (by nlinarith)
  nlinarith

/-- With all higher positive roots absent, any representative of the actual
root functor is a vector group. The cyclic quotient has trivial actual kernel. -/
theorem isVectorGroup_of_noHigherRoots [Smooth G.X.hom]
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    {a : characterLattice T} (ha : a ≠ 0) (hhigh : HasNoHigherRoots i a)
    {H : GroupScheme (Spec (CommRingCat.of k))} {j : H ⟶ G}
    (hj : (subgroup i a).IsRepresentedBy j) : IsVectorGroup H := by
  let b := AutomorphicAction.conjugation i
  have hfirst : weightFiltration b a 1 = subgroup i a :=
    cyclicRootFunctorComparison k G inferInstance inferInstance T hT i a ha
  have htwo : weightFiltration b a 2 = ⊥ :=
    weightFiltration_two_eq_bot_of_noHigherRoots inferInstance hT i ha hhigh
  have hrep : (weightFiltration b a 1).IsRepresentedBy j := hfirst.symm ▸ hj
  obtain ⟨V, q, c, d, hq, hc, _, _⟩ :=
    (cyclicWeightFiltration k G inferInstance inferInstance T hT b a ha 1
      (by decide)).2 H j hrep
  let : Mono j.hom.hom := hj.1
  have hq0 : IsFppfQuotient ⊥ q := by
    simpa only [show 1 + 1 = (2 : ℕ) from rfl, htwo,
      SubgroupFunctor.comap_bot_of_mono] using hq
  exact hq0.isVectorGroup_of_bot hc.isVectorGroup

/-- A root with no higher positive roots has a nonidentity rational point,
using its nonzero exact Lie image and its actual vector coordinates. -/
theorem exists_rootPoint_of_noHigherRoots [Smooth G.X.hom]
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    {a : characterLattice T} (ha : a ∈ relativeRoots i)
    (hhigh : HasNoHigherRoots i a) :
    ∃ x : rationalPoints G,
      x ∈ (subgroup i a).carrier (Over.mk (𝟙 _)) ∧ x ≠ 1 := by
  obtain ⟨H, j, hj, _⟩ := subgroup_isSmoothConnectedClosed_of_ne_zero hT i a ha.1
  have hvec := isVectorGroup_of_noHigherRoots hT i ha.1 hhigh hj
  have hspan : semigroupWeightSpan (AutomorphicAction.conjugation i)
      (cyclicTail a 1) ≠ ⊥ := by
    intro hzero
    apply ha.2
    apply eq_bot_iff.mpr
    have hle : weightSpace i a ≤
        semigroupWeightSpan (AutomorphicAction.conjugation i) (cyclicTail a 1) := by
      rw [semigroupWeightSpan]
      simpa only [actionWeightSpace_conjugation] using
        (le_iSup (fun χ : cyclicTail a 1 =>
          actionWeightSpace (AutomorphicAction.conjugation i) χ.val)
          ⟨a, 1, by decide, by decide, one_smul ℕ a⟩)
    exact hle.trans (le_of_eq hzero)
  exact exists_rationalPoint_ne_one_of_vector_lieImage hj hspan
    (hasLieImage_subgroup i a hT ha.1) hvec

/-- Every actual relative root subgroup of a smooth affine group acted on by
a split torus contains a nonidentity rational point, over any field. -/
theorem exists_rootPoint_actual [Smooth G.X.hom]
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    {a : characterLattice T} (ha : a ∈ relativeRoots i) :
    ∃ x : rationalPoints G,
      x ∈ (subgroup i a).carrier (Over.mk (𝟙 _)) ∧ x ≠ 1 := by
  obtain ⟨N, hN, hroot, hhigh⟩ := exists_maximal_root_multiple hT i ha
  obtain ⟨x, hx, hx1⟩ := exists_rootPoint_of_noHigherRoots hT i hroot hhigh
  exact ⟨x, subgroup_nsmul_le i a hN _ hx, hx1⟩

/-- Actual relative roots of every smooth affine group with a split-torus
action have nonidentity rational points, without a root-system hypothesis. -/
def RootSubgroupRationalNontrivialStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [Smooth G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (_hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    (a : characterLattice T), a ∈ relativeRoots i →
      ∃ x : rationalPoints G,
        x ∈ (subgroup i a).carrier (Over.mk (𝟙 _)) ∧ x ≠ 1

/-- The unconditional actual rational nontriviality statement. -/
theorem rootSubgroupRationalNontrivial : RootSubgroupRationalNontrivialStatement.{u} :=
  fun _ _ _ _ _ _ hT i _ ha => exists_rootPoint_actual hT i ha

end RelativeRoot

end Langlands.GroupScheme
