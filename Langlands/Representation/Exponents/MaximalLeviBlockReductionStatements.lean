import Langlands.Representation.Exponents.MaximalLeviBlockStatements
import Langlands.Representation.Exponents.MaximalLeviSupercuspidalReducibilityStatement

/-! # Reduction statements for Renard VII.1.3, Corollary

Renard 2026, VII.1.3, Corollary (printed p.226/PDF p.232) and its proof (printed
pp.226–227/PDF pp.232–233). `MaximalLeviBlockFullEssSurjStatement` is part (iii) of the
published `MaximalLeviBlockStatements` without its faithfulness conjunct, in the same setting
and encoding. `MaximalLeviBlockStatementsFromInputsStatement` says that the VII.1.3 Theorem
(`MaximalLeviSupercuspidalReducibilityStatement` at carrier universe `max u v`) and
`MaximalLeviBlockFullEssSurjStatement` imply all of `MaximalLeviBlockStatements`. Neither
proposition is assumed or proved here.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VII.1.3, Corollary, part (iii) without faithfulness, in the setting and encoding
of `MaximalLeviBlockStatements`: induction sends `InBlockM` into `InBlockG`, is full on
`InBlockM`, and every object of `InBlockG` is isomorphic to the induction of an object of
`InBlockM`. -/
def MaximalLeviBlockFullEssSurjStatement : Prop :=
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
      ¬ IsIso p →
      (∀ (Q : GroupScheme (Spec (CommRingCat.of k))) (q : Q ⟶ G) (j : P ⟶ Q),
        IsParabolicSubgroup q → j ≫ q = p → IsIso j ∨ IsIso q) →
      haveI := hl.isConnectedReductive.isAffineHom
      letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
      haveI : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
      haveI : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
      ∀ ρ : SmoothRep.{0, u, max u v} ℂ (rationalPoints M), ρ.IsIrreducible →
        (∀ (P' M' U' : GroupScheme (Spec (CommRingCat.of k)))
          (p' : P' ⟶ M) (l' : M' ⟶ P') (r' : U' ⟶ P')
          (hp' : IsParabolicSubgroup p') (hl' : IsRationalLeviSubgroup l')
          (hr' : LeviSubgroup.IsGeometricUnipotentRadical r')
          (hmul' : IsIso (subgroupMultiplication l' r')),
          ¬ IsIso p' → Subsingleton ((jacquetFunctor p' l' r' hp' hr' hl' hmul').obj ρ)) →
        (¬ ∃ (g : rationalPoints G) (φ : M ≅ M),
          φ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso g).hom ∧ g ∉ pointImage (l ≫ p) ∧
          ∃ ψ : Plancherel.unramifiedCharacters
              (fun χ : rationalCharacters M => (Plancherel.rationalNormCharacters M χ).toMul),
            ∃ T : ρ ≃ₗ[ℂ] ρ, ∀ (m : rationalPoints M) (x : ρ),
              T (ρ.representation m x) =
                (((ψ : rationalPoints M →ₜ* ℂˣ) (rationalPoints.map φ.hom m) : ℂˣ) : ℂ) •
                  ρ.representation (rationalPoints.map φ.hom m) (T x)) →
        let IsTwist : SmoothRep.{0, u, max u v} ℂ (rationalPoints M) → Prop := fun σ =>
          ∃ ψ : Plancherel.unramifiedCharacters
              (fun χ : rationalCharacters M => (Plancherel.rationalNormCharacters M χ).toMul),
            ∃ T : ρ ≃ₗ[ℂ] σ, ∀ (m : rationalPoints M) (x : ρ),
              (((ψ : rationalPoints M →ₜ* ℂˣ) m : ℂˣ) : ℂ) • T (ρ.representation m x) =
                σ.representation m (T x)
        let InBlockM : ObjectProperty (SmoothRep.{0, u, max u v} ℂ (rationalPoints M)) :=
          fun X => ∀ σ : SmoothRep.{0, u, max u v} ℂ (rationalPoints M),
            σ.IsIrreducible → SmoothRep.IsSubquotient σ X → IsTwist σ
        let InBlockG : ObjectProperty (SmoothRep.{0, u, max u v} ℂ (rationalPoints G)) :=
          fun Y => ∀ τ : SmoothRep.{0, u, max u v} ℂ (rationalPoints G),
            τ.IsIrreducible → SmoothRep.IsSubquotient τ Y →
              ∃ σ : SmoothRep.{0, u, max u v} ℂ (rationalPoints M), IsTwist σ ∧
                SmoothRep.IsSubquotient τ ((leviInductionFunctor p l r hp hr hl hmul).obj σ)
        ((∀ X : SmoothRep.{0, u, max u v} ℂ (rationalPoints M), InBlockM X →
            InBlockG ((leviInductionFunctor p l r hp hr hl hmul).obj X)) ∧
          (InBlockM.ι ⋙ leviInductionFunctor p l r hp hr hl hmul).Full ∧
          ∀ Y : SmoothRep.{0, u, max u v} ℂ (rationalPoints G), InBlockG Y →
            ∃ X : SmoothRep.{0, u, max u v} ℂ (rationalPoints M), InBlockM X ∧
              Nonempty ((leviInductionFunctor p l r hp hr hl hmul).obj X ≅ Y))

/-- Renard VII.1.3, Corollary, from the VII.1.3 Theorem and the non-faithfulness conjuncts of
part (iii): the Theorem at carrier universe `max u v` and
`MaximalLeviBlockFullEssSurjStatement` imply the full published
`MaximalLeviBlockStatements`. -/
def MaximalLeviBlockStatementsFromInputsStatement : Prop :=
  MaximalLeviSupercuspidalReducibilityStatement.{u, max u v} →
    MaximalLeviBlockFullEssSurjStatement.{u, v} → MaximalLeviBlockStatements.{u, v}

end Langlands.Aubert.General.RepresentedParabolic
