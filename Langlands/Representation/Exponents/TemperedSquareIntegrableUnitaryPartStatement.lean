import Langlands.Representation.Exponents.ArbitraryParabolicUnitaryJacquetPart
import Langlands.Representation.Exponents.ArbitraryParabolicTempered
import Langlands.Representation.MatrixCoefficient.ModuloCenter
import Langlands.GroupScheme.Reductive.Basic

/-! # Square-integrability of tempered representations through unitary Jacquet parts

Renard 2026, VII.2.4, Lemma (printed p.230/PDF p.236): a tempered admissible
representation with a central character is square-integrable modulo the center if and
only if the unitary part `(r_P^G π)_0` vanishes for every proper parabolic `P`.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VII.2.4, Lemma: a normalized-exponent tempered representation of `G(F)` on
which the center of `G(F)` acts by a character is square-integrable modulo the center,
for a Haar measure on `G(F) ⧸ Z(G(F))`, if and only if, for every actual rational
parabolic `p` that is not an isomorphism, with rational Levi, matching geometric
unipotent radical and split component, the unitary part of the normalized Jacquet
module is zero. -/
def TemperedSquareIntegrableUnitaryPartStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      [MeasurableSpace (rationalPoints G ⧸ Subgroup.center (rationalPoints G))]
      [BorelSpace (rationalPoints G ⧸ Subgroup.center (rationalPoints G))]
      (haar : MeasureTheory.Measure (rationalPoints G ⧸ Subgroup.center (rationalPoints G)))
      [haar.IsHaarMeasure] (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
      (ω : Subgroup.center (rationalPoints G) →* ℂˣ),
      IsNormalizedExponentTempered hG π → π.HasCentralCharacter ω →
        (IsSquareIntegrableModCenter π.representation haar ↔
          ∀ (P M U : GroupScheme (Spec (CommRingCat.of k)))
            (A : CommGroupScheme (Spec (CommRingCat.of k)))
            (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P) (a : A.toGrp ⟶ M)
            (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
            (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
            (hmul : IsIso (subgroupMultiplication l r)) (ha : IsSplitComponent a),
            ¬ IsIso p → unitaryJacquetPart p l r hp hl hr hmul ha π = ⊥)

end Langlands.Aubert.General.RepresentedParabolic
