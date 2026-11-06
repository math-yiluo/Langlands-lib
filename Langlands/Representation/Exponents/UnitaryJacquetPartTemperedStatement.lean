import Langlands.Representation.Exponents.ArbitraryParabolicUnitaryJacquetPart
import Langlands.Representation.Exponents.ArbitraryParabolicTempered
import Langlands.GroupScheme.Reductive.Basic

/-! # The unitary part of the Jacquet module of a tempered representation

Renard 2026, VII.2.3 (printed p.229/PDF p.235): for a tempered representation `π` of `G`
and a parabolic `P = MN`, the normalized Jacquet module is the direct sum
`r_P^G π = (r_P^G π)_0 ⊕ (r_P^G π)_+`, and `(r_P^G π)_0` is a tempered representation
of `M`. Temperedness is the published normalized-exponent predicate, applied to `M(F)`
through the Levi-point identification.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VII.2.3: for every actual rational parabolic with rational Levi, matching
geometric unipotent radical and split component, and every normalized-exponent tempered
representation `π` of `G(F)`, the unitary and nonunitary parts of the normalized Jacquet
module are complementary subspaces, and the unitary part, as a representation of the
Levi points, is normalized-exponent tempered. -/
def UnitaryJacquetPartTemperedStatement : Prop :=
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
      ∀ π : SmoothRep.{0, u, v} ℂ (rationalPoints G),
        IsNormalizedExponentTempered hG π →
          IsCompl (unitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule
              (nonunitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule ∧
            IsNormalizedExponentTempered hl.isConnectedReductive
              (leviUnitaryJacquetModule p l r hp hl hr hmul ha π)

end Langlands.Aubert.General.RepresentedParabolic
