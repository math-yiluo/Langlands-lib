import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints
import Langlands.Representation.Exponents.LeviSupercuspidalInductionSupport
import Langlands.Representation.Plancherel.RationalUnramifiedCharacterDensity
import Langlands.Representation.Plancherel.RationalCharacterValuation
import Langlands.Representation.Plancherel.UnramifiedCharacters
import Langlands.Representation.Category.Twist
import Langlands.GroupScheme.Reductive.Basic

/-!
# Renard VI.8.4–VI.8.5: irreducibility of induced twists on Zariski open sets

For a rational parabolic `P = MN` of `G` and a smooth representation `ρ` of `M(F)`, the
family `ψ ↦ i_P^G(ρ ⊗ ψ)` is indexed by the unramified characters `ψ ∈ X(M)`. A
Zariski principal open subset of `X(M)` is the nonvanishing locus of a polynomial in
the published canonical torus coordinates on `X(M)`.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Renard.AlgebraicFamily

open Langlands.Aubert.General Langlands.Aubert.General.RepresentedParabolic GroupScheme

/-- VI.8.4 Proposition: let `P = MN` be a rational parabolic of `G` and `ρ` an
irreducible smooth representation of `M(F)`. If `i_P^G(ρ ⊗ ψ₀)` is irreducible for an
unramified character `ψ₀` of `M(F)`, then there is a principal Zariski open subset of
`X(M)` containing `ψ₀` on which every `i_P^G(ρ ⊗ ψ)` is irreducible. -/
def InducedIrreducibilityOpenStatement : Prop :=
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
      ∀ ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M), ρ.IsIrreducible →
        ∀ ψ₀ : Plancherel.unramifiedCharacters
            (fun χ : rationalCharacters M => (Plancherel.rationalNormCharacters M χ).toMul),
          ((leviInductionFunctor p l r hp hr hl hmul).obj
              (ρ.twist ψ₀.val.toMonoidHom
                (Plancherel.unramifiedCharacter_isOpen_ker _ ψ₀))).IsIrreducible →
            ∃ f : MvPolynomial (Fin (Plancherel.rationalImageRank M)) ℂ,
              ψ₀ ∈ Plancherel.rationalUnramifiedPrincipalOpen M hl.isConnectedReductive f ∧
                ∀ ψ ∈ Plancherel.rationalUnramifiedPrincipalOpen M hl.isConnectedReductive f,
                  ((leviInductionFunctor p l r hp hr hl hmul).obj
                    (ρ.twist ψ.val.toMonoidHom
                      (Plancherel.unramifiedCharacter_isOpen_ker _ ψ))).IsIrreducible

/-- VI.8.5 Theorem: let `P = MN` be a rational parabolic of `G` and `ρ` an irreducible
supercuspidal smooth representation of `M(F)`. Then there is a nonzero polynomial `f`
such that `i_P^G(ρ ⊗ ψ)` is irreducible for every `ψ` in the principal Zariski open
subset of `X(M)` defined by `f`. -/
def GenericInducedIrreducibilityStatement : Prop :=
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
      ∀ ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M), ρ.IsIrreducible →
        IsSupercuspidal ρ →
          ∃ f : MvPolynomial (Fin (Plancherel.rationalImageRank M)) ℂ, f ≠ 0 ∧
            ∀ ψ ∈ Plancherel.rationalUnramifiedPrincipalOpen M hl.isConnectedReductive f,
              ((leviInductionFunctor p l r hp hr hl hmul).obj
                (ρ.twist ψ.val.toMonoidHom
                  (Plancherel.unramifiedCharacter_isOpen_ker _ ψ))).IsIrreducible

/-- The two statements above. -/
def GenericIrreducibilityStatements.{u', v'} : Prop :=
  InducedIrreducibilityOpenStatement.{u', v'} ∧ GenericInducedIrreducibilityStatement.{u', v'}

end Langlands.Renard.AlgebraicFamily
