import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints
import Langlands.GroupScheme.Reductive.Basic

/-! # Normalized parabolic restriction preserves finite type

Renard 2026, VI.1.3 Proposition (printed p.136/PDF p.142): for a parabolic `P = MN` of
`G` and a smooth representation `π` of `G` of finite type, the normalized Jacquet module
`r_P^G π` is of finite type. Finite type is finite generation of the carrier as a module
over the group algebra; the Jacquet module is the published transport to `M(F)`.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VI.1.3 Proposition: for every actual rational parabolic with rational Levi and
matching geometric unipotent radical, the normalized Jacquet module of a smooth
representation of `G(F)` that is finitely generated over `ℂ[G(F)]` is finitely generated
over `ℂ[M(F)]`. -/
def LeviJacquetFiniteTypeStatement : Prop :=
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
      ∀ (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)),
        Module.Finite (MonoidAlgebra ℂ (rationalPoints G)) π.representation.asModule →
          Module.Finite (MonoidAlgebra ℂ (rationalPoints M))
            ((leviJacquetFunctor p l r hp hr hl hmul).obj π).representation.asModule

end Langlands.Aubert.General.RepresentedParabolic
