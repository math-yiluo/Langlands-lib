# Global affine combinations of lifts along a square-zero thickening

Namespace `Langlands.AlgebraicGeometry.SmoothLifting`. Fix a morphism
`f : X ⟶ S`, a ring `C` with an ideal `I` such that `SqZero I`, a morphism
`x₀ : Spec (C ⧸ I) ⟶ X` and a morphism `s : Spec C ⟶ S`. Neither `X` nor
`S` is assumed affine, and `f` is arbitrary.

`IsGlobalLift f I x₀ s y` says that `y : Spec C ⟶ X` restricts to `x₀`
along `Spec (C ⧸ I) ⟶ Spec C` and satisfies `y ≫ f = s`. `restrC R y` is
the restriction of `y` to a `C`-algebra `R`, and `IsGlobalLift.isLift`
shows that it is a lift on `R` in the sense of the module
`SmoothLifting.Charts`.

## The global combination

`gcomb hI hy₀ hy c` is the affine combination `y₀ + ∑ₖ cₖ (yₖ - y₀)` of
global lifts.
- `exists_gcomb` takes a finite family of charts from `exists_charts`. It
  forms the chart combinations (`Chart.gcombLocal`) on the localizations
  `C[1/gᵢ]`. These agree on overlaps by `Chart.gcombLocal_restr` and
  chart independence (`Chart.comb_eq`), and they are glued with
  `exists_glue`.
- `gcomb_restr` characterizes the result: for every chart and every
  `C`-algebra `R` in which the chart element is a unit, the restriction to
  `R` is the chart combination. The proof covers `Spec R` by the
  localizations at the chart elements (`eq_of_restr_away`).
- `IsGlobalLift.ext_of_charts` says that global lifts are determined by
  their restrictions to a covering chart family.
- `eq_of_restr_away'` is the same principle for an arbitrary family of
  elements generating the unit ideal.

## Functoriality

Let `φ : X ⟶ Y` be a morphism with `φ ≫ fY = f`.
- `IsGlobalLift.comp` and `IsLift.comp` say that `φ` maps lifts of `x₀` to
  lifts of `x₀ ≫ φ`.
- `Chart.rep_comp` and `Chart.comb_comp` compare chart representatives and
  chart combinations along `φ.appLE`, when the source chart maps into the
  target chart.
- `exists_refined_chart` provides such source charts around every point
  of a target chart.
- `gcomb_comp` says that `φ` commutes with global affine combinations.

## Provenance

These are internal lemmas written for Task 6989 by Worker 496. They make
the affine structure of the set of infinitesimal lifts (the torsor
structure in Stacks Project, More on Morphisms, Lemma 37.11.7, Tag 02H6)
explicit and global, without a sheaf of differentials.
