import Langlands.GroupScheme.Rational.RelativeRootSignsStatement
import Langlands.GroupScheme.Rational.WeightSemigroupSupport
import Langlands.GroupScheme.Rational.RelativeRootSignSupport
import Langlands.GroupScheme.Rational.DynamicSemigroupProof

/-! # Actual relative-root signs determine the dynamic subgroup functors -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme
namespace RelativeRoot

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- Agreement on actual roots and on the zero character identifies the
generated subgroup functors for the conjugation action. -/
theorem semigroupSubgroup_eq_of_relativeRoot_iff (i : T.toGrp ⟶ G)
    {A A' : AddSubsemigroup (characterLattice T)}
    (hzero : (0 : characterLattice T) ∈ A ↔ (0 : characterLattice T) ∈ A')
    (hroot : ∀ χ ∈ relativeRoots i, χ ∈ A ↔ χ ∈ A') :
    semigroupSubgroup (AutomorphicAction.conjugation i) A =
      semigroupSubgroup (AutomorphicAction.conjugation i) A' := by
  apply le_antisymm
  · apply semigroupSubgroup_mono_on_weightSupport
    exact (rootSupport_imp_iff_actionWeightSupport_imp i
      (fun χ => χ ∈ A) (fun χ => χ ∈ A') hzero.mp).mp
        (fun χ hχ => (hroot χ hχ).mp)
  · apply semigroupSubgroup_mono_on_weightSupport
    exact (rootSupport_imp_iff_actionWeightSupport_imp i
      (fun χ => χ ∈ A') (fun χ => χ ∈ A) hzero.mpr).mp
        (fun χ hχ => (hroot χ hχ).mpr)

/-- Equal signs on actual relative roots identify the generated subgroups for
the nonnegative, zero and strictly positive pairing regions. -/
theorem pairingSemigroupSubgroups_eq_of_relativeRootSigns (i : T.toGrp ⟶ G)
    (zeta eta : cocharacterLattice T)
    (hsign : ∀ α ∈ relativeRoots i,
      (0 ≤ latticePairing T α zeta ↔ 0 ≤ latticePairing T α eta) ∧
      (latticePairing T α zeta = 0 ↔ latticePairing T α eta = 0) ∧
      (0 < latticePairing T α zeta ↔ 0 < latticePairing T α eta)) :
    semigroupSubgroup (AutomorphicAction.conjugation i) (nonnegativeSemigroup zeta) =
        semigroupSubgroup (AutomorphicAction.conjugation i) (nonnegativeSemigroup eta) ∧
    semigroupSubgroup (AutomorphicAction.conjugation i) (zeroSemigroup zeta) =
        semigroupSubgroup (AutomorphicAction.conjugation i) (zeroSemigroup eta) ∧
    semigroupSubgroup (AutomorphicAction.conjugation i) (positiveSemigroup zeta) =
        semigroupSubgroup (AutomorphicAction.conjugation i) (positiveSemigroup eta) := by
  refine ⟨?_, ?_, ?_⟩
  · apply semigroupSubgroup_eq_of_relativeRoot_iff i
    · simp [nonnegativeSemigroup]
    · intro α hα
      exact (hsign α hα).1
  · apply semigroupSubgroup_eq_of_relativeRoot_iff i
    · simp [zeroSemigroup]
    · intro α hα
      exact (hsign α hα).2.1
  · apply semigroupSubgroup_eq_of_relativeRoot_iff i
    · simp [positiveSemigroup]
    · intro α hα
      exact (hsign α hα).2.2

end RelativeRoot

/-- The actual relative-root signs determine all three dynamic subgroup
functors, with exactly the scope of the published statement. -/
theorem relativeRootSignsDetermineDynamic :
    RelativeRootSignsDetermineDynamicStatement.{u} := by
  intro k _ G hG T i hi zeta eta
  let := hG.isAffineHom
  intro hsign
  have hsemigroup :=
    RelativeRoot.pairingSemigroupSubgroups_eq_of_relativeRootSigns i zeta eta hsign
  have hzeta := RelativeRoot.dynamicSemigroupComparison k G hG.smooth
    hG.isAffineHom hG.connectedSpace T hi.isSplitSubtorus.1 i zeta
  have heta := RelativeRoot.dynamicSemigroupComparison k G hG.smooth
    hG.isAffineHom hG.connectedSpace T hi.isSplitSubtorus.1 i eta
  exact ⟨hzeta.1.trans (hsemigroup.1.trans heta.1.symm),
    hzeta.2.1.trans (hsemigroup.2.1.trans heta.2.1.symm),
    hzeta.2.2.trans (hsemigroup.2.2.trans heta.2.2.symm)⟩

end Langlands.GroupScheme
