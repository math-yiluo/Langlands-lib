import Langlands.Representation.Families.IrreducibleInducedTwistExistenceStatement
import Langlands.Representation.Category.Subquotients
import Langlands.Representation.Exponents.Jacquet

/-! # Exclusion and persistence of the inducing exponent in quotients of induced twists

For an irreducible admissible `ρ` of an actual rational Levi `M(F)`, a split component
`a : A_M ⟶ M` and an unramified character `ψ`, write `I_ψ = i_P^G(ρψ)`. The two
propositions concern the generalized eigencharacters of `A_M(F)` on the normalized
Jacquet module `r_P(I_ψ / S)` of a quotient of `I_ψ` by an invariant subspace `S`.
These are proof targets, not theorems.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Renard.AlgebraicFamily

open Langlands.Aubert.General Langlands.Aubert.General.RepresentedParabolic GroupScheme

/-- Exclusion: away from a proper Zariski-closed subset of `X(M)`, no `A_M`-exponent of
`ρψ` is an `A_M`-exponent of `r_P(I_ψ / S)` when the invariant subspace `S` of
`I_ψ = i_P^G(ρψ)` is nonzero. This is a proof target, not a theorem. -/
def InducedTwistQuotientExclusionStatement : Prop :=
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
      (hmul : IsIso (subgroupMultiplication l r))
      (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ M),
      IsSplitComponent a →
      haveI := hl.isConnectedReductive.isAffineHom
      letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
      haveI : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
      haveI : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
      ∀ ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M), ρ.IsIrreducible →
        ρ.IsAdmissible →
          ∃ f : MvPolynomial (Fin (Plancherel.rationalImageRank M)) ℂ, f ≠ 0 ∧
            ∀ ψ ∈ Plancherel.rationalUnramifiedPrincipalOpen M hl.isConnectedReductive f,
              ∀ χ : rationalPoints A.toGrp →* ℂˣ,
                IsGeneralizedEigencharacter
                  ((ρ.twist ψ.val.toMonoidHom
                    (Plancherel.unramifiedCharacter_isOpen_ker _ ψ)).representation.comp
                      (rationalPoints.map a)) χ →
                ∀ S : Subrepresentation ((leviInductionFunctor p l r hp hr hl hmul).obj
                    (ρ.twist ψ.val.toMonoidHom
                      (Plancherel.unramifiedCharacter_isOpen_ker _ ψ))).representation,
                  S ≠ ⊥ →
                  ¬ IsGeneralizedEigencharacter
                    (((leviJacquetFunctor p l r hp hr hl hmul).obj
                      (SmoothRep.quotient _ S)).representation.comp
                        (rationalPoints.map a)) χ

/-- Persistence: away from a proper Zariski-closed subset of `X(M)`, every quotient
`I_ψ / S` by a proper invariant subspace `S` of `I_ψ = i_P^G(ρψ)` has an `A_M`-exponent
of `r_P(I_ψ / S)` that is also an `A_M`-exponent of `ρψ`. This is a proof target, not a
theorem. -/
def InducedTwistQuotientPersistenceStatement : Prop :=
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
      (hmul : IsIso (subgroupMultiplication l r))
      (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ M),
      IsSplitComponent a →
      haveI := hl.isConnectedReductive.isAffineHom
      letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
      haveI : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
      haveI : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
      ∀ ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M), ρ.IsIrreducible →
        ρ.IsAdmissible →
          ∃ f : MvPolynomial (Fin (Plancherel.rationalImageRank M)) ℂ, f ≠ 0 ∧
            ∀ ψ ∈ Plancherel.rationalUnramifiedPrincipalOpen M hl.isConnectedReductive f,
              ∀ S : Subrepresentation ((leviInductionFunctor p l r hp hr hl hmul).obj
                  (ρ.twist ψ.val.toMonoidHom
                    (Plancherel.unramifiedCharacter_isOpen_ker _ ψ))).representation,
                S ≠ ⊤ →
                ∃ χ : rationalPoints A.toGrp →* ℂˣ,
                  IsGeneralizedEigencharacter
                    ((ρ.twist ψ.val.toMonoidHom
                      (Plancherel.unramifiedCharacter_isOpen_ker _ ψ)).representation.comp
                        (rationalPoints.map a)) χ ∧
                  IsGeneralizedEigencharacter
                    (((leviJacquetFunctor p l r hp hr hl hmul).obj
                      (SmoothRep.quotient _ S)).representation.comp
                        (rationalPoints.map a)) χ

/-- Both propositions, at the same field and carrier universes. -/
def InducedTwistQuotientExponentStatements : Prop :=
  InducedTwistQuotientExclusionStatement.{u, v} ∧ InducedTwistQuotientPersistenceStatement.{u, v}

end Langlands.Renard.AlgebraicFamily
