/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.PerfectLocusOfRank
public import WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch

/-!
# The seams between the cohomology and the representability strands

The construction of the Picard scheme of a smooth projective curve has two strands: Strand A,
the coherent cohomology of curves and of families (Čech cohomology, Serre's theorems,
semicontinuity, the perfect locus, Riemann–Roch, the twist lemma), and Strand B, the
representability argument (the Hilbert scheme of points, the zero-scheme dictionary, the open
subfunctor `F`, the representability criterion). Strand B uses Strand A at exactly four places,
the *seams*, and Strand A never uses Strand B.

`AlgebraicGeometry.picard_seams` records the four seams: it is the conjunction of the four
Strand A statements, each in the form in which its Strand B consumer uses it.

## Main statements

- `AlgebraicGeometry.picard_seams`: the four seams `S₁`–`S₄`.

## Implementation details

The seams are used as follows: `S₁` (`Scheme.isAmple_of_degree_pos`,
`Scheme.isAffine_compl_of_isAmple`) in the hypothesis check of the Hilbert theorem; `S₂`
(`Scheme.degree_eq_genus`) in the zero-scheme dictionary, whose codomain is `Hilb^g`; `S₃`
(`Scheme.Modules.exists_opens_range_subset_iff_isFiniteLocallyFreeInDegree`, with `i = 0`,
`r = 1`) in the openness of `F`; `S₄` (`Scheme.exists_isInvertible_twist`) in the generation
condition of the representability criterion.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

open Scheme

/-- **The four seams between Strand A and Strand B.** The conjunction of the four cohomological
inputs to the representability of the Picard functor:

* `S₁`: positive degree implies ample, and the complement of an effective divisor with ample
  line bundle is affine;
* `S₂`: `deg ℒ_t = g` for a line bundle `ℒ_t` on `X_K` with `h⁰ = 1` and no higher cohomology;
* `S₃`: the locus of the base over which `Rf_* ℱ` is finite locally free of rank `r` in degree
  `i` is open and detected by base change;
* `S₄`: the twist lemma. -/
theorem picard_seams :
    -- `S₁` (G): positive degree implies ample
    (∀ (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
      [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
      [GlobalSectionsBijective k X] (ℒ : X.Modules) [ℒ.IsInvertible],
      0 < ℒ.degree k → IsAmple (X ↘ Spec (.of k)) ℒ) ∧
    -- `S₁` (H): an effective divisor with ample line bundle has affine complement
    (∀ (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
      [IsProper (X ↘ Spec (.of k))] (J : X.IdealSheafData), J.IsInvertible →
      IsAmple (X ↘ Spec (.of k)) J.toModulesᵛ →
      ∀ (V : Scheme.{u}) (j : V ⟶ X) [IsOpenImmersion j],
        Set.range j.base = (J.support : Set X)ᶜ → IsAffine V) ∧
    -- `S₂`: the degree of the dictionary is the genus
    (∀ (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
      [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
      [GlobalSectionsBijective k X] (K : Type u) [Field K] [Algebra k K]
      (ℒ : (pullback (X ↘ Spec (.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Modules)
      [ℒ.IsInvertible], Modules.finrankH K ℒ 0 = 1 → (∀ q : ℕ, 0 < q → Subsingleton (ℒ.H q)) →
        ℒ.degree K = (arithmeticGenus k X : ℤ)) ∧
    -- `S₃`: openness of the perfect locus, and base change on it
    (∀ (X T : Scheme.{u}) (f : X ⟶ T) (ℱ : X.Modules) [IsProper f]
      [LocallyOfFinitePresentation f] [QuasiCompact f] [HasInjectiveResolutions X.Modules]
      [ℱ.IsFinitePresentation], ℱ.IsFlatOver f → ∀ i r : ℕ,
      ∃ U : T.Opens, (U : Set T) = ℱ.perfectLocusOfRank f i r ∧
        ∀ {T' X' : Scheme.{u}} (g : T' ⟶ T) (g' : X' ⟶ X) (f' : X' ⟶ T')
          [HasInjectiveResolutions X'.Modules], IsPullback g' f' f g →
          (Set.range g.base ⊆ U ↔ Modules.IsFiniteLocallyFreeInDegree
            (fun q ↦ (Modules.higherDirectImage f' q).obj ((Modules.pullback g').obj ℱ)) i r)) ∧
    -- `S₄`: the twist lemma, i.e. the generation condition
    (∀ (k : Type u) [Field k] [IsSepClosed k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
      [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
      [ConnectedSpace X] (K : Type u) [Field K] [Algebra k K]
      (ℒ : (pullback (X ↘ Spec (.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Modules)
      [ℒ.IsInvertible],
      ∃ ℒ₀ : X.Modules, ℒ₀.IsInvertible ∧
        Modules.finrankH K (ℒ ⊗ (Modules.pullback (pullback.fst (X ↘ Spec (.of k))
          (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj ℒ₀) 0 = 1 ∧
        Modules.finrankH K (ℒ ⊗ (Modules.pullback (pullback.fst (X ↘ Spec (.of k))
          (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj ℒ₀) 1 = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k _ X _ _ _ _ ℒ _ hd
    exact isAmple_of_degree_pos ℒ hd
  · intro k _ X _ _ J hJ hample V j _ hj
    exact isAffine_compl_of_isAmple hJ hample j hj
  · intro k _ X _ _ _ _ K _ _ ℒ _ h0 hq
    exact degree_eq_genus K ℒ h0 hq
  · intro X T f ℱ _ _ _ _ _ hℱ i r
    exact Modules.exists_opens_range_subset_iff_isFiniteLocallyFreeInDegree f ℱ hℱ i r
  · intro k _ _ X _ _ _ _ K _ _ ℒ _
    exact exists_isInvertible_twist K ℒ

end AlgebraicGeometry
