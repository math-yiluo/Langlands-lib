import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints
import Langlands.Representation.Category.Subquotients
import Langlands.Representation.Filtration.ObjectDefinitions
import Langlands.GroupScheme.Rational.ParabolicPointConjugation
import Langlands.GroupScheme.Reductive.Basic

/-! # Induction from supercuspidal representations and cuspidal data

Renard 2026, VI.5.4, Theorem (printed pp.173–174/PDF pp.179–180): for a parabolic
`P = MN` and an irreducible supercuspidal representation `ρ` of `M`, `i_P^G ρ` has finite
length. For a second such pair `(P' = M'N', ρ')`, the following are equivalent: the cuspidal
data `(M, ρ)` and `(M', ρ')` are associated; `Hom_G(i_P^G ρ, i_{P'}^G ρ') ≠ 0`; the two
induced representations have equivalent Jordan–Hölder series; they have a common
Jordan–Hölder factor. The length bound `l(M)` and the dimension bound on the Hom space are
not stated.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VI.5.4, Theorem, without the two numerical bounds: for actual rational
parabolics `P = MN` and `P' = M'N'` and irreducible supercuspidal smooth representations
`ρ` of `M(F)` and `ρ'` of `M'(F)`, the normalized induction `i_P^G ρ` has a finite
composition series, and the four conditions (association of cuspidal data, a nonzero
intertwiner `i_P^G ρ → i_{P'}^G ρ'`, equal Jordan–Hölder factors with multiplicities, a
common irreducible subquotient) are equivalent. -/
def LeviSupercuspidalInductionAssociationStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P M N P' M' N' : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
      (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication l r))
      (p' : P' ⟶ G) (l' : M' ⟶ P') (r' : N' ⟶ P')
      (hp' : IsParabolicSubgroup p') (hl' : IsRationalLeviSubgroup l')
      (hr' : LeviSubgroup.IsGeometricUnipotentRadical r')
      (hmul' : IsIso (subgroupMultiplication l' r')),
      haveI := hl.isConnectedReductive.isAffineHom
      letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
      haveI : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
      haveI : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
      haveI := hl'.isConnectedReductive.isAffineHom
      letI : TopologicalSpace (rationalPoints M') := leviPointTopology l' hl'
      haveI : LocallyCompactSpace (rationalPoints M') :=
        leviPoints_locallyCompactSpace p' l' hp' hl'
      haveI : NonarchimedeanGroup (rationalPoints M') :=
        leviPoints_nonarchimedeanGroup p' l' hp' hl'
      ∀ (ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M))
        (ρ' : SmoothRep.{0, u, v} ℂ (rationalPoints M')),
        ρ.IsIrreducible →
        (∀ (P₁ M₁ U₁ : GroupScheme (Spec (CommRingCat.of k)))
          (p₁ : P₁ ⟶ M) (l₁ : M₁ ⟶ P₁) (r₁ : U₁ ⟶ P₁)
          (hp₁ : IsParabolicSubgroup p₁) (hl₁ : IsRationalLeviSubgroup l₁)
          (hr₁ : LeviSubgroup.IsGeometricUnipotentRadical r₁)
          (hmul₁ : IsIso (subgroupMultiplication l₁ r₁)),
          ¬ IsIso p₁ → Subsingleton ((jacquetFunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁).obj ρ)) →
        ρ'.IsIrreducible →
        (∀ (P₁ M₁ U₁ : GroupScheme (Spec (CommRingCat.of k)))
          (p₁ : P₁ ⟶ M') (l₁ : M₁ ⟶ P₁) (r₁ : U₁ ⟶ P₁)
          (hp₁ : IsParabolicSubgroup p₁) (hl₁ : IsRationalLeviSubgroup l₁)
          (hr₁ : LeviSubgroup.IsGeometricUnipotentRadical r₁)
          (hmul₁ : IsIso (subgroupMultiplication l₁ r₁)),
          ¬ IsIso p₁ → Subsingleton ((jacquetFunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁).obj ρ')) →
        (∃ n : ℕ, HasCompositionSeriesLength
          (SmoothRep.toRep.obj ((leviInductionFunctor p l r hp hr hl hmul).obj ρ)) n) ∧
        List.TFAE
          [∃ (g : rationalPoints G) (φ : M ≅ M'),
              φ.hom ≫ l' ≫ p' = l ≫ p ≫ (G.innerIso g).hom ∧
              ∃ T : ρ ≃ₗ[ℂ] ρ', ∀ (m : rationalPoints M) (x : ρ),
                T (ρ.representation m x) =
                  ρ'.representation (rationalPoints.map φ.hom m) (T x),
            ∃ (f : (leviInductionFunctor p l r hp hr hl hmul).obj ρ ⟶
                (leviInductionFunctor p' l' r' hp' hr' hl' hmul').obj ρ')
              (x : (leviInductionFunctor p l r hp hr hl hmul).obj ρ),
              SmoothRep.hom f x ≠ 0,
            HaveSameJordanHolderFactors
              (SmoothRep.toRep.obj ((leviInductionFunctor p l r hp hr hl hmul).obj ρ))
              (SmoothRep.toRep.obj ((leviInductionFunctor p' l' r' hp' hr' hl' hmul').obj ρ')),
            ∃ σ : SmoothRep.{0, u, max u v} ℂ (rationalPoints G),
              σ.IsIrreducible ∧
              SmoothRep.IsSubquotient σ ((leviInductionFunctor p l r hp hr hl hmul).obj ρ) ∧
              SmoothRep.IsSubquotient σ ((leviInductionFunctor p' l' r' hp' hr' hl' hmul').obj ρ')]

end Langlands.Aubert.General.RepresentedParabolic
