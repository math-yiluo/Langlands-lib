import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints
import Langlands.GroupScheme.Reductive.Basic

/-! # Normalized parabolic induction preserves finite type

Renard 2026, VI.7.5, Theorem (printed p.187 / PDF p.193): for every parabolic `P = MN` the
normalized induction `i_P^G` preserves representations of finite type. Finite type is finite
generation of the carrier as a module over the group algebra, as in the published VI.1.3
statement `LeviJacquetFiniteTypeStatement`.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VI.7.5, Theorem: for every actual rational parabolic with rational Levi and
matching geometric unipotent radical, the normalized induction of a smooth representation of
`M(F)` that is finitely generated over `ℂ[M(F)]` is finitely generated over `ℂ[G(F)]`. -/
def LeviInductionFiniteTypeStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P M U : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
      (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication l r)),
      haveI := hl.isConnectedReductive.isAffineHom
      letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
      haveI : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
      haveI : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
      ∀ (ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M)),
        Module.Finite (MonoidAlgebra ℂ (rationalPoints M)) ρ.representation.asModule →
          Module.Finite (MonoidAlgebra ℂ (rationalPoints G))
            ((leviInductionFunctor.{u, v} p l r hp hr hl hmul).obj ρ).representation.asModule

end Langlands.Aubert.General.RepresentedParabolic
