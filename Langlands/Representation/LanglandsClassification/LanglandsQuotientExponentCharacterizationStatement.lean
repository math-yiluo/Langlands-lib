import Langlands.Representation.LanglandsClassification.LanglandsClassificationStatement
import Langlands.Representation.Exponents.ArbitraryParabolic
import Langlands.Representation.Category.Subquotients

/-! # The Langlands quotient among the irreducible subquotients (Renard VII.4.2)

Statement only. In the proof of the VII.4.2 Theorem, after part (i), Renard observes that
the Langlands quotient `J(P, σ, ψ)` is characterized among the irreducible subquotients
`π` of `i_P^G(σ ⊗ ψ)` by `ℜ(ψ) ∈ ℜ(Exp(A_M, r_{P̄}^G(π)))`, where `P̄` is the opposite
parabolic.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VII.4.2, remark after the proof of (i): let `(P = MN, σ, ψ)` be a Langlands
triplet with split component `a : A → M`, and let `P̄ = M N̄` be a parabolic with the same
Levi `M` and `P(F) ∩ P̄(F) = M(F)` (the opposite parabolic). An irreducible subquotient
`π` of `i_P^G(σ ⊗ ψ)` is an irreducible quotient of `i_P^G(σ ⊗ ψ)` (that is, the Langlands
quotient) if and only if `ℜ(ψ)` is the normalized real part of some normalized exponent of
`r_{P̄}^G(π)` along `A`. -/
def LanglandsQuotientExponentCharacterizationStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
      [Mono i.hom.hom.left] (ν : cocharacterLattice T) (D : RelativeRootReflectionData i)
      (P M U : GroupScheme (Spec (CommRingCat.of k)))
      (A : CommGroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P) (a : A.toGrp ⟶ M)
      (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication l r)) (ha : IsSplitComponent a)
      (J : Set (characterLattice T)) (f : A ⟶ T)
      (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
      (ψ : leviUnramifiedCharacters l hl)
      (Pbar Ubar : GroupScheme (Spec (CommRingCat.of k)))
      (pbar : Pbar ⟶ G) (lbar : M ⟶ Pbar) (rbar : Ubar ⟶ Pbar)
      (hpbar : IsParabolicSubgroup pbar) (hlbar : IsRationalLeviSubgroup lbar)
      (hrbar : LeviSubgroup.IsGeometricUnipotentRadical rbar)
      (hmulbar : IsIso (subgroupMultiplication lbar rbar)),
      IsLanglandsTriplet i ν D p l a hp hl ha J f σ ψ →
      lbar ≫ pbar = l ≫ p →
      pointImage p ⊓ pointImage pbar = pointImage (l ≫ p) →
        letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
        haveI : NonarchimedeanGroup (rationalPoints M) :=
          leviPoints_nonarchimedeanGroup p l hp hl
        let I := (leviInductionFunctor p l r hp hr hl hmul).obj
          (σ.twist ψ.val.toMonoidHom (Plancherel.unramifiedCharacter_isOpen_ker _ ψ))
        ∀ π : SmoothRep.{0, u, max u v} ℂ (rationalPoints G),
          π.IsIrreducible → SmoothRep.IsSubquotient π I →
          (Classification.IsIrreducibleQuotient I.representation π.representation ↔
            ∃ χ ∈ normalizedJacquetExponents pbar lbar rbar hpbar hlbar hrbar hmulbar ha π,
              Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ =
                leviUnramifiedRealPart l hl a ha ψ)

end Langlands.Aubert.General.RepresentedParabolic
