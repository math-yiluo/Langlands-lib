import Langlands.AlgebraicGeometry.Picard.Rosati
import Langlands.AlgebraicGeometry.Picard.LineBundlePullback
import Langlands.AlgebraicGeometry.Picard.LineBundleQuasicoherent
import Langlands.AlgebraicGeometry.Picard.LineBundleEulerPolynomial
import Langlands.AlgebraicGeometry.Modules.CoherentEulerSequence
import Langlands.AbelianScheme.IsogenySpecialization
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Degrees of the Mumford homomorphisms of `L ^ n ⊗ f^* L` -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.Rosati

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
  Langlands.AlgebraicGeometry.Modules Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- Let `lam` be the actual Mumford homomorphism of an ample line bundle `L` on an abelian
scheme `A` over an algebraically closed field, presented as in
`MumfordMixedEulerTraceStatement`, and let `f` be an actual endomorphism of `A`. For all
sufficiently large `n`, the homomorphism `n • lam + f ≫ lam ≫ f^∨`, where `f^∨` is the
actual dual homomorphism, is an isogeny, and at every point of the dual its degree is the
square of the actual Euler characteristic of `f^* L ⊗ L ^ n`.
Mumford's argument: this homomorphism is the Mumford homomorphism of `L ^ n ⊗ f^* L`,
which is ample for large `n`, and the Riemann--Roch degree formula applies
(Milne, *Abelian Varieties*, Theorem 13.3(a)).
This proposition is a statement target, not a proof. -/
def MumfordEulerDegreeStatement : Prop :=
  ∀ (P : Prerequisites.{u})
    (k : Type u) [Field k] [IsAlgClosed k]
    (A : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
    (W : DualData A) (lam : A ⟶ W.dual P)
    (L : LineBundle A.X.left)
    (B : LineBundle (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
    (evaluationB : tensorObj ((Scheme.Modules.pullback (unitSection A)).obj L.obj)
      B.obj ≅ structureSheaf (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
    (M : LineBundle A.X.left)
    (evaluation : tensorObj
      (LineBundle.normalize P.preservation A.X.hom (unitSection A)
        (unitSection_comp A) L B evaluationB).obj.carrier M.obj ≅
          structureSheaf A.X.left),
    L.IsAmple →
    (groupHom lam).hom.hom =
      mumfordSchemeMapOfLineBundle P.preservation A L B evaluationB M evaluation
        P.square W.hasDual →
    ∀ (f : A ⟶ A), ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      IsIsogeny (n • lam + (f ≫ lam ≫
        dualAbelianSchemeMapFromEvaluation W.hasDual W.geometry P.preservation
          W.inversePoincare W.evaluation P.stability P.composition P.unitCoherence
          P.associativity P.comparison P.symmetry W.hasDual W.geometry W.inversePoincare
          W.evaluation f : A ⟶ W.dual P)) ∧
      ∀ y : (W.dual P).X.left,
        ((hom (n • lam + (f ≫ lam ≫
          dualAbelianSchemeMapFromEvaluation W.hasDual W.geometry P.preservation
            W.inversePoincare W.evaluation P.stability P.composition P.unitCoherence
            P.associativity P.comparison P.symmetry W.hasDual W.geometry W.inversePoincare
            W.evaluation f : A ⟶ W.dual P))).finrank y : ℚ) =
          coherentEulerSequence A.X.hom ((LineBundle.pullback (hom f)).obj L).obj
            (hasFiniteAffineSections_lineBundle _) L n ^ 2

end Langlands.AbelianScheme.Rosati
