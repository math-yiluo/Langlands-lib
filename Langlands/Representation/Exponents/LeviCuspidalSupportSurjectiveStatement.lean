import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints
import Langlands.Representation.Category.Subquotients
import Langlands.GroupScheme.Reductive.Basic

/-! # The cuspidal support map is surjective with finite fibres

Renard 2026, VI.7.1, Proposition (printed p.180/PDF p.186): the cuspidal support map
`Sc : Irr(G) → Ω(G)` is a surjection with finite fibres. The proof shows, for a parabolic
`P` with Levi `M` and an irreducible supercuspidal `ρ` of `M`, that some irreducible `π` has
`ρ` as a quotient of `r_P^G π`, and that only finitely many irreducible `π` have `ρ` as a
composition factor of `r_P^G π`.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VI.7.1, Proposition, in the form proved in the source: for every actual rational
parabolic `P = MN` and every irreducible supercuspidal smooth representation `ρ` of `M(F)`,
(surjectivity) some irreducible smooth representation `π` of `G(F)` admits a surjective
intertwiner `r_P^G π → ρ`, and (finite fibres) there are finitely many irreducible smooth
representations of `G(F)` such that every irreducible `π` having `ρ` as a subquotient of
`r_P^G π` is isomorphic to one of them. -/
def LeviCuspidalSupportSurjectiveStatement : Prop :=
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
        (∀ (P' M' U' : GroupScheme (Spec (CommRingCat.of k)))
          (p' : P' ⟶ M) (l' : M' ⟶ P') (r' : U' ⟶ P')
          (hp' : IsParabolicSubgroup p') (hl' : IsRationalLeviSubgroup l')
          (hr' : LeviSubgroup.IsGeometricUnipotentRadical r')
          (hmul' : IsIso (subgroupMultiplication l' r')),
          ¬ IsIso p' → Subsingleton ((jacquetFunctor p' l' r' hp' hr' hl' hmul').obj ρ)) →
        (∃ π : SmoothRep.{0, u, max u v} ℂ (rationalPoints G),
          π.IsIrreducible ∧
          ∃ f : ((leviJacquetFunctor p l r hp hr hl hmul).obj π).representation.IntertwiningMap
              ρ.representation,
            Function.Surjective f) ∧
        ∃ (n : ℕ) (π₀ : Fin n → SmoothRep.{0, u, v} ℂ (rationalPoints G)),
          ∀ π : SmoothRep.{0, u, v} ℂ (rationalPoints G),
            π.IsIrreducible →
            SmoothRep.IsSubquotient ρ ((leviJacquetFunctor p l r hp hr hl hmul).obj π) →
            ∃ i, Nonempty (π ≅ π₀ i)

end Langlands.Aubert.General.RepresentedParabolic
