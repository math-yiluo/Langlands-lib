import Langlands.Representation.Category.Contragredient
import Langlands.Representation.Exponents.LeviSupercuspidalInductionSupport
import Langlands.GroupScheme.Reductive.Basic

/-! Renard VI.2.2, Corollary: a smooth representation is irreducible (resp.
irreducible supercuspidal) if and only if its smooth contragredient is. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe u v

open GroupScheme

/-- VI.2.2, Corollary: for every smooth complex representation `π` of `G(F)`,
`π` is irreducible if and only if its smooth contragredient `π̃` is irreducible, and
`π` is irreducible supercuspidal if and only if `π̃` is irreducible supercuspidal.
Supercuspidality is the published represented predicate (vanishing of the normalized
Jacquet modules along every proper actual rational parabolic). -/
def ContragredientIrreducibilityStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) :=
      Aubert.General.RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (A : SmoothRep.{0, u, v} ℂ (rationalPoints G)),
      (A.IsIrreducible ↔ A.contragredient.IsIrreducible) ∧
      ((A.IsIrreducible ∧ Aubert.General.RepresentedParabolic.IsSupercuspidal A) ↔
        (A.contragredient.IsIrreducible ∧
          Aubert.General.RepresentedParabolic.IsSupercuspidal A.contragredient))

end Langlands.CuspidalSupport
