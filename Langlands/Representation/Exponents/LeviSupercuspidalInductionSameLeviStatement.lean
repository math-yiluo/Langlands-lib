import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints
import Langlands.Representation.Category.Subquotients
import Langlands.Representation.Filtration.ObjectDefinitions
import Langlands.GroupScheme.Reductive.Basic

/-! # Inductions of a supercuspidal representation along parabolics with the same Levi

Renard 2026, VI.5.4, Corollary (printed p.175/PDF p.181): let `ρ` be an irreducible
supercuspidal representation of a Levi subgroup `M` of `G`. (i) For two parabolics `P` and
`Q` with Levi factor `M`, `i_P^G ρ` and `i_Q^G ρ` have equivalent Jordan–Hölder series.
(ii) There is a nonzero intertwining operator between them. (iii) Every irreducible
subquotient of `i_P^G ρ` is a subrepresentation of `i_Q^G ρ` for some parabolic `Q` with Levi
factor `M`.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VI.5.4, Corollary: for an actual rational parabolic `P = MN` and an irreducible
supercuspidal smooth representation `ρ` of `M(F)`, (i) and (ii) for every actual rational
parabolic `Q` with the same Levi embedding `M → G`, the normalized inductions `i_P^G ρ` and
`i_Q^G ρ` have the same Jordan–Hölder factors with multiplicities and there is a nonzero
intertwiner `i_P^G ρ → i_Q^G ρ`; (iii) every irreducible subquotient of `i_P^G ρ` embeds
into `i_Q^G ρ` for some actual rational parabolic `Q` with the same Levi embedding. -/
def LeviSupercuspidalInductionSameLeviStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P M N : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
      (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication l r)),
      haveI := hl.isConnectedReductive.isAffineHom
      letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
      haveI : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
      haveI : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
      ∀ ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M),
        ρ.IsIrreducible →
        (∀ (P₁ M₁ U₁ : GroupScheme (Spec (CommRingCat.of k)))
          (p₁ : P₁ ⟶ M) (l₁ : M₁ ⟶ P₁) (r₁ : U₁ ⟶ P₁)
          (hp₁ : IsParabolicSubgroup p₁) (hl₁ : IsRationalLeviSubgroup l₁)
          (hr₁ : LeviSubgroup.IsGeometricUnipotentRadical r₁)
          (hmul₁ : IsIso (subgroupMultiplication l₁ r₁)),
          ¬ IsIso p₁ → Subsingleton ((jacquetFunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁).obj ρ)) →
        (∀ (Q U : GroupScheme (Spec (CommRingCat.of k)))
          (q : Q ⟶ G) (lQ : M ⟶ Q) (rQ : U ⟶ Q)
          (hq : IsParabolicSubgroup q) (hlQ : IsRationalLeviSubgroup lQ)
          (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
          (hmulQ : IsIso (subgroupMultiplication lQ rQ)),
          lQ ≫ q = l ≫ p →
            HaveSameJordanHolderFactors
              (SmoothRep.toRep.obj ((leviInductionFunctor p l r hp hr hl hmul).obj ρ))
              (SmoothRep.toRep.obj ((leviInductionFunctor q lQ rQ hq hrQ hlQ hmulQ).obj ρ)) ∧
            ∃ (f : (leviInductionFunctor p l r hp hr hl hmul).obj ρ ⟶
                (leviInductionFunctor q lQ rQ hq hrQ hlQ hmulQ).obj ρ)
              (x : (leviInductionFunctor p l r hp hr hl hmul).obj ρ),
              SmoothRep.hom f x ≠ 0) ∧
        ∀ σ : SmoothRep.{0, u, max u v} ℂ (rationalPoints G),
          σ.IsIrreducible →
          SmoothRep.IsSubquotient σ ((leviInductionFunctor p l r hp hr hl hmul).obj ρ) →
          ∃ (Q U : GroupScheme (Spec (CommRingCat.of k)))
            (q : Q ⟶ G) (lQ : M ⟶ Q) (rQ : U ⟶ Q)
            (hq : IsParabolicSubgroup q) (hlQ : IsRationalLeviSubgroup lQ)
            (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
            (hmulQ : IsIso (subgroupMultiplication lQ rQ)),
            lQ ≫ q = l ≫ p ∧
            ∃ f : σ ⟶ (leviInductionFunctor q lQ rQ hq hrQ hlQ hmulQ).obj ρ,
              Function.Injective (SmoothRep.hom f)

end Langlands.Aubert.General.RepresentedParabolic
