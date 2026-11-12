import Langlands.Representation.CompactCoefficient.Classes
import Langlands.Representation.Exponents.LeviSupercuspidalInductionSupport
import Langlands.GroupScheme.Reductive.Basic

/-! Renard VI.2.1, Theorem, (a) ⇔ (b): a smooth representation is supercuspidal if and
only if its matrix coefficients have compact support modulo the centre. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.Aubert.General.RepresentedParabolic

universe u v

open GroupScheme

/-- VI.2.1, Theorem, equivalence of (a) and (b), for every smooth complex representation
`A` of `G(F)` in the represented setting: `A` is supercuspidal (published represented
predicate) if and only if every matrix coefficient `g ↦ ℓ(A(g) v)`, for `v ∈ A` and `ℓ`
a smooth vector of the dual, has support in `C · Z` for some compact `C`, where `Z` is the
centre of `G(F)`. -/
def SupercuspidalCoefficientCriterionStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (A : SmoothRep.{0, u, v} ℂ (rationalPoints G)),
      IsSupercuspidal A ↔
        ∀ (w : A) (ℓ : Module.Dual ℂ A), IsSmoothVector A.representation.dual ℓ →
          ∃ C : Set (rationalPoints G), IsCompact C ∧
            Function.support (matrixCoefficient A.representation ℓ w) ⊆
              C * (Subgroup.center (rationalPoints G) : Set (rationalPoints G))

end Langlands.Aubert.General.RepresentedParabolic
