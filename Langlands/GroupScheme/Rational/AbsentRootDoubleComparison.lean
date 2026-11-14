import Langlands.GroupScheme.Rational.CyclicRootFunctorComparisonProof
import Langlands.GroupScheme.Rational.RootSubgroupRationalNontrivial
import Langlands.GroupScheme.Rational.WeightSupportCongruence

/-! # Intrinsic root groups when only the doubled root can occur -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom]
    (i : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp)
    (a : characterLattice T) (ha : a ≠ 0)
    (hfirst : a ∉ relativeRoots i)
    (hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots i)

include hT ha hfirst hhigh

/-- If the first and all third-or-higher actual roots on a ray are absent,
the positive ray and doubled ray select exactly the same ambient weights. -/
theorem agreeOnAmbientWeights_cyclicTail_double_of_absent_roots :
    AgreeOnAmbientWeights (AutomorphicAction.conjugation i)
      (cyclicTail a 1) (cyclicTail (2 • a) 1) := by
  intro c hc
  constructor
  · rintro ⟨n, hn, hn0, rfl⟩
    have hnroot : n • a ∈ relativeRoots i :=
      ⟨hT.nsmul_ne_zero ha hn0.ne', by
        simpa only [actionWeightSpace_conjugation] using
          (mem_actionWeightSupport_top_iff (AutomorphicAction.conjugation i) (n • a)).mp hc⟩
    have hn1 : n ≠ 1 := by
      intro hn1
      apply hfirst
      simpa only [hn1, one_smul] using hnroot
    have hn2 : n = 2 := by
      by_contra h
      exact hhigh n (by omega) hnroot
    subst n
    exact ⟨1, le_rfl, by omega, one_nsmul _⟩
  · rintro ⟨n, hn, hn0, rfl⟩
    exact ⟨n * 2, by omega, by omega, (smul_smul n (2 : ℕ) a).symm⟩

variable [Smooth G.X.hom]

/-- The intrinsic original-character subgroup equals the doubled-character
subgroup on every test scheme when only the doubled root can occur. -/
theorem subgroup_eq_double_of_absent_roots :
    subgroup i a = subgroup i (2 • a) := by
  rw [← weightFiltration_one_eq_subgroup hT i a ha,
    ← weightFiltration_one_eq_subgroup hT i (2 • a)
      (hT.nsmul_ne_zero ha (by decide : (2 : ℕ) ≠ 0))]
  exact semigroupSubgroup_eq_of_weightSupport _
    (agreeOnAmbientWeights_cyclicTail_double_of_absent_roots i hT a ha hfirst hhigh)

/-- The actual representatives of the two equal all-test root functors are
canonically isomorphic over their common ambient group. -/
def absentRootDoubleIso
    {U V : GroupScheme (Spec (CommRingCat.of k))}
    {jU : U ⟶ G} {jV : V ⟶ G}
    (hU : (subgroup i a).IsRepresentedBy jU)
    (hV : (subgroup i (2 • a)).IsRepresentedBy jV) : U ≅ V :=
  hU.isoOfIsRepresentedBy
    ⟨hV.1, hV.2.trans (subgroup_eq_double_of_absent_roots i hT a ha hfirst hhigh).symm⟩

include hT ha hfirst hhigh in
/-- The chosen isomorphism retains the actual ambient inclusion. -/
theorem absentRootDoubleIso_hom_comp
    {U V : GroupScheme (Spec (CommRingCat.of k))}
    {jU : U ⟶ G} {jV : V ⟶ G}
    (hU : (subgroup i a).IsRepresentedBy jU)
    (hV : (subgroup i (2 • a)).IsRepresentedBy jV) :
    (absentRootDoubleIso i hT a ha hfirst hhigh hU hV).hom ≫ jV = jU := by
  unfold absentRootDoubleIso
  apply SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp

end Langlands.GroupScheme.RelativeRoot
