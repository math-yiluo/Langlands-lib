import Langlands.Representation.Exponents.ArbitraryParabolicUnitaryJacquetPart
import Langlands.Representation.Exponents.ArbitraryParabolicTempered
import Langlands.GroupScheme.Reductive.Basic

/-! # Homomorphisms from the Jacquet module to a tempered representation

Renard 2026, VII.2.4, Proposition (printed p.229/PDF p.235): for tempered `σ` of `M` and
tempered `π` of `G`, `Hom_G(π, i_P^G σ) ≃ Hom_M((r_P^G π)_0, σ)`. The source proof
combines Frobenius reciprocity VI.1.1 with Lemma III.1.10. This module states the second
step: restriction along the inclusion `(r_P^G π)_0 → r_P^G π` is a bijection
`Hom_M(r_P^G π, σ) → Hom_M((r_P^G π)_0, σ)`.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VII.2.4, Jacquet side of the Proposition: for every actual rational parabolic
with rational Levi, matching geometric unipotent radical and split component, every
normalized-exponent tempered `π` of `G(F)` and every normalized-exponent tempered `σ` of
`M(F)`, precomposition with the inclusion of the unitary part is a bijection from
intertwiners `r_P^G π ⟶ σ` to intertwiners `(r_P^G π)_0 ⟶ σ`. -/
def TemperedJacquetUnitaryRestrictionStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P M U : GroupScheme (Spec (CommRingCat.of k)))
      (A : CommGroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P) (a : A.toGrp ⟶ M)
      (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication l r)) (ha : IsSplitComponent a),
      haveI := hl.isConnectedReductive.isAffineHom
      letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
      haveI : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
      haveI : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
      ∀ (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
        (σ : SmoothRep.{0, u, v} ℂ (rationalPoints M)),
        IsNormalizedExponentTempered hG π →
          IsNormalizedExponentTempered hl.isConnectedReductive σ →
            Function.Bijective
              (fun f : (leviJacquetFunctor p l r hp hr hl hmul).obj π ⟶ σ =>
                leviUnitaryJacquetModuleι p l r hp hl hr hmul ha π ≫ f)

end Langlands.Aubert.General.RepresentedParabolic
