import Langlands.Representation.Exponents.MaximalLeviReducibilityUnitaryInputs

/-! # Supercuspidal coefficient norms on the full central quotient

The compact-support consequence of Renard VI.2.1 in the represented-parabolic
interface, specialized to the hypotheses of the unitarizability input.
This module only defines a proposition; it does not prove it.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VI.2.1(a) implies (b): every smooth-dual coefficient norm of an
irreducible supercuspidal representation with unitary central character has
compact support on the quotient by the full center of the rational point group. -/
def SupercuspidalUnitaryCoefficientCompactSupportStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (H : GroupScheme (Spec (CommRingCat.of k))) (hH : IsConnectedReductive H),
    haveI := hH.isAffineHom
    letI : TopologicalSpace (rationalPoints H) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints H)] [NonarchimedeanGroup (rationalPoints H)]
      (ρ : SmoothRep.{0, u, v} ℂ (rationalPoints H)), ρ.IsIrreducible →
      (∀ (P' M' U' : GroupScheme (Spec (CommRingCat.of k)))
        (p' : P' ⟶ H) (l' : M' ⟶ P') (r' : U' ⟶ P')
        (hp' : IsParabolicSubgroup p') (hl' : IsRationalLeviSubgroup l')
        (hr' : LeviSubgroup.IsGeometricUnipotentRadical r')
        (hmul' : IsIso (subgroupMultiplication l' r')),
        ¬ IsIso p' → Subsingleton ((jacquetFunctor p' l' r' hp' hr' hl' hmul').obj ρ)) →
      ∀ (c : UnitaryCentralCharacter ρ.representation)
        (ℓ : SmoothDual ρ.representation) (v : ρ),
        HasCompactSupport (c.coefficientNorm ℓ.1 v)

end Langlands.Aubert.General.RepresentedParabolic
