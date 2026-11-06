import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints
import Langlands.Representation.Category.Subquotients
import Langlands.GroupScheme.Rational.ParabolicPointConjugation
import Langlands.GroupScheme.Reductive.Basic

/-! # Well-definedness of the cuspidal support

Renard 2026, VI.7.1, Lemma (printed p.180/PDF p.186): let `P_i = M_i N_i` (`i = 1, 2`) be
parabolic subgroups of `G`, `(M_i, ρ_i)` cuspidal data and `π` an irreducible smooth
representation of `G` such that `ρ_i` is a composition factor of `r_{P_i}^G π`. Then the
cuspidal data `(M_1, ρ_1)` and `(M_2, ρ_2)` are associated.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VI.7.1, Lemma: for actual rational parabolics `P₁ = M₁N₁` and `P₂ = M₂N₂`, an
irreducible smooth representation `π` of `G(F)`, and irreducible supercuspidal smooth
representations `ρᵢ` of `Mᵢ(F)` that are subquotients of `r_{Pᵢ}^G π`, there are `g ∈ G(F)`
and `φ : M₁ ≅ M₂` realizing conjugation by `g`, and `ρ₁ ≅ ρ₂ ∘ φ`. -/
def LeviCuspidalSupportAssociationStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P₁ M₁ N₁ P₂ M₂ N₂ : GroupScheme (Spec (CommRingCat.of k)))
      (p₁ : P₁ ⟶ G) (l₁ : M₁ ⟶ P₁) (r₁ : N₁ ⟶ P₁)
      (hp₁ : IsParabolicSubgroup p₁) (hl₁ : IsRationalLeviSubgroup l₁)
      (hr₁ : LeviSubgroup.IsGeometricUnipotentRadical r₁)
      (hmul₁ : IsIso (subgroupMultiplication l₁ r₁))
      (p₂ : P₂ ⟶ G) (l₂ : M₂ ⟶ P₂) (r₂ : N₂ ⟶ P₂)
      (hp₂ : IsParabolicSubgroup p₂) (hl₂ : IsRationalLeviSubgroup l₂)
      (hr₂ : LeviSubgroup.IsGeometricUnipotentRadical r₂)
      (hmul₂ : IsIso (subgroupMultiplication l₂ r₂)),
      haveI := hl₁.isConnectedReductive.isAffineHom
      letI : TopologicalSpace (rationalPoints M₁) := leviPointTopology l₁ hl₁
      haveI : LocallyCompactSpace (rationalPoints M₁) :=
        leviPoints_locallyCompactSpace p₁ l₁ hp₁ hl₁
      haveI : NonarchimedeanGroup (rationalPoints M₁) :=
        leviPoints_nonarchimedeanGroup p₁ l₁ hp₁ hl₁
      haveI := hl₂.isConnectedReductive.isAffineHom
      letI : TopologicalSpace (rationalPoints M₂) := leviPointTopology l₂ hl₂
      haveI : LocallyCompactSpace (rationalPoints M₂) :=
        leviPoints_locallyCompactSpace p₂ l₂ hp₂ hl₂
      haveI : NonarchimedeanGroup (rationalPoints M₂) :=
        leviPoints_nonarchimedeanGroup p₂ l₂ hp₂ hl₂
      ∀ (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
        (ρ₁ : SmoothRep.{0, u, v} ℂ (rationalPoints M₁))
        (ρ₂ : SmoothRep.{0, u, v} ℂ (rationalPoints M₂)),
        π.IsIrreducible →
        ρ₁.IsIrreducible →
        (∀ (P' M' U' : GroupScheme (Spec (CommRingCat.of k)))
          (p' : P' ⟶ M₁) (l' : M' ⟶ P') (r' : U' ⟶ P')
          (hp' : IsParabolicSubgroup p') (hl' : IsRationalLeviSubgroup l')
          (hr' : LeviSubgroup.IsGeometricUnipotentRadical r')
          (hmul' : IsIso (subgroupMultiplication l' r')),
          ¬ IsIso p' → Subsingleton ((jacquetFunctor p' l' r' hp' hr' hl' hmul').obj ρ₁)) →
        SmoothRep.IsSubquotient ρ₁ ((leviJacquetFunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁).obj π) →
        ρ₂.IsIrreducible →
        (∀ (P' M' U' : GroupScheme (Spec (CommRingCat.of k)))
          (p' : P' ⟶ M₂) (l' : M' ⟶ P') (r' : U' ⟶ P')
          (hp' : IsParabolicSubgroup p') (hl' : IsRationalLeviSubgroup l')
          (hr' : LeviSubgroup.IsGeometricUnipotentRadical r')
          (hmul' : IsIso (subgroupMultiplication l' r')),
          ¬ IsIso p' → Subsingleton ((jacquetFunctor p' l' r' hp' hr' hl' hmul').obj ρ₂)) →
        SmoothRep.IsSubquotient ρ₂ ((leviJacquetFunctor p₂ l₂ r₂ hp₂ hr₂ hl₂ hmul₂).obj π) →
        ∃ (g : rationalPoints G) (φ : M₁ ≅ M₂),
          φ.hom ≫ l₂ ≫ p₂ = l₁ ≫ p₁ ≫ (G.innerIso g).hom ∧
          ∃ T : ρ₁ ≃ₗ[ℂ] ρ₂, ∀ (m : rationalPoints M₁) (x : ρ₁),
            T (ρ₁.representation m x) =
              ρ₂.representation (rationalPoints.map φ.hom m) (T x)

end Langlands.Aubert.General.RepresentedParabolic
