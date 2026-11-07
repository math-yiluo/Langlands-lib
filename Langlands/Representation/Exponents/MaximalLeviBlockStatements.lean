import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints
import Langlands.Representation.Plancherel.RationalCharacterValuation
import Langlands.Representation.Plancherel.UnramifiedCharacters
import Langlands.GroupScheme.Rational.ParabolicPointConjugation
import Langlands.GroupScheme.Reductive.Basic

/-! # The Bernstein component of a non-self-associate supercuspidal of a maximal Levi

Renard 2026, VII.1.3, Corollary (printed p.226/PDF p.232): let `P = MN` be a maximal
parabolic, `D` the inertial class of an irreducible supercuspidal representation `ρ` of
`M` with `w · D ≠ D` for the nontrivial element `w` of `W(M, *)`, and `Ω` the component of
`(M, D)`. Then `i_P^G` sends the irreducible representations in `D` to irreducible
representations, the Jacquet functor detects every nonzero object of `M(G)_Ω` through
`D`, and `i_P^G` is an equivalence from `M(M)_D` onto `M(G)_Ω`.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VII.1.3, Corollary, parts (i)–(iii), for every actual maximal proper rational
parabolic with rational Levi `M` and matching radical, and every irreducible supercuspidal
smooth representation `ρ` of `M(F)` whose inertial class is not fixed by an element of
`G(F)` normalizing the Levi outside the Levi image. Carriers lie in `Type (max u v)`. With
`IsTwist σ` meaning that `σ` is isomorphic to `ρ` twisted by an unramified character, the
block `InBlockM` of `M(F)` asks every irreducible subquotient to be such a twist, and the
block `InBlockG` of `G(F)` asks every irreducible subquotient to be a subquotient of the
induction of such a twist:

* (i) the induction of every unramified twist of `ρ` is irreducible;
* (ii) every nonzero object of `InBlockG` has a normalized Jacquet module with an
  irreducible subquotient that is an unramified twist of `ρ`;
* (iii) induction sends `InBlockM` into `InBlockG`, is full and faithful on `InBlockM`, and
  every object of `InBlockG` is isomorphic to the induction of an object of `InBlockM`. -/
def MaximalLeviBlockStatements : Prop :=
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
        (∀ σ : SmoothRep.{0, u, max u v} ℂ (rationalPoints M), IsTwist σ →
          ((leviInductionFunctor p l r hp hr hl hmul).obj σ).IsIrreducible) ∧
        (∀ Y : SmoothRep.{0, u, max u v} ℂ (rationalPoints G), InBlockG Y → Nontrivial Y →
          ∃ σ : SmoothRep.{0, u, max u v} ℂ (rationalPoints M), σ.IsIrreducible ∧
            SmoothRep.IsSubquotient σ ((leviJacquetFunctor p l r hp hr hl hmul).obj Y) ∧
              IsTwist σ) ∧
        ((∀ X : SmoothRep.{0, u, max u v} ℂ (rationalPoints M), InBlockM X →
            InBlockG ((leviInductionFunctor p l r hp hr hl hmul).obj X)) ∧
          (InBlockM.ι ⋙ leviInductionFunctor p l r hp hr hl hmul).Full ∧
          (InBlockM.ι ⋙ leviInductionFunctor p l r hp hr hl hmul).Faithful ∧
          ∀ Y : SmoothRep.{0, u, max u v} ℂ (rationalPoints G), InBlockG Y →
            ∃ X : SmoothRep.{0, u, max u v} ℂ (rationalPoints M), InBlockM X ∧
              Nonempty ((leviInductionFunctor p l r hp hr hl hmul).obj X ≅ Y))

end Langlands.Aubert.General.RepresentedParabolic
