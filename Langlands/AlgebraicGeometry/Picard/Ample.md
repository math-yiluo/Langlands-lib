# Section generation loci and ampleness of line bundles

This module defines the generation locus `X_s` of a global section of a
tensor power of a line bundle and the predicate `IsAmple`. It works for every
scheme `X : Scheme.{u}`. No separation, noetherian or quasi-compactness
assumption is imposed on `X`, except the quasi-compactness that `IsAmple`
itself asserts.

## Generation locus interfaces for an arbitrary module

The open set is the published `Langlands.SchemeModule.trivializationOpen M s`
from `Modules.SectionLocus`, for an actual module sheaf `M : X.Modules` and
`s : GlobalSections M`. That is Mathlib's `Γ(M, ⊤)`. The open is the
supremum of all opens `U` on which the restriction of
`sectionHom M s : structureModule X ⟶ M` to the open subscheme `U` is an
isomorphism. So it is the whole locus where the section-induced map from the
structure sheaf is locally an isomorphism, not a chosen neighbourhood. This
module adds the following results about it, all proved without extra
hypotheses:

- `mem_trivializationOpen_iff`: `x` lies in the open iff some open `U`
  containing `x` satisfies `TrivializesOn M s U`.
- `mem_trivializationOpen_iff_stalk`: `x` lies in the open iff some open
  neighbourhood of `x` consists of points `y` with `IsStalkFrame M s y`, meaning
  the stalk map at `y` is an isomorphism. This uses the published
  `localStalkCriterion`.
- The imported `maximalTrivialization`: the section trivializes on `U` iff
  `U ≤ trivializationOpen M s`. This is the published
  `maximalTrivialization`.
- `trivializesOn_trivializationOpen`: the section trivializes on the whole
  open.
- `trivializationOpenIso`: the resulting isomorphism from the structure
  sheaf of the open subscheme to `M.restrict (trivializationOpen M s).ι`.
  `trivializationOpenIso_hom` states that its forward map is the inverse of
  Mathlib's `restrictUnitIso` composed with the restricted `sectionHom M s`.

Two lemmas compare this open with other descriptions of the locus. Each takes
the needed comparison statement as an explicit hypothesis and proves nothing
beyond it:

- `coe_trivializationOpen_eq_setOf_isStalkFrame` takes `h :
  LineBundleSectionResidueComparison` and `hM : IsLocallyFreeRankOne M`. It
  concludes that the underlying set of the open is the whole set
  `{x | IsStalkFrame M s x}`.
- `coe_trivializationOpen_eq_nonvanishingLocus` takes `h :
  LineBundleResidueOpenComparison` and the same `hM`. It concludes that the
  underlying set equals `nonvanishingLocus M s`, the set of points where the
  section has nonzero value in its residue-field fibre.

These comparison statements are published in `Modules.SectionResidueStatements`.
Their proof is the separate task `2a0d3205-e7bb-4eed-88e5-757a42ca17ad`. They
are never assumed here; they appear only as hypotheses.

## Line-bundle definitions

In the namespace `Langlands.AlgebraicGeometry.Picard.LineBundle`, take
`L : LineBundle X`. This is the published locally free rank-one actual
`X.Modules`. The tensor powers are the published
`Langlands.Scheme.Modules.tensorPow L.obj n`. They are right-associated, with
zeroth power `structureSheaf X` and `(n + 1)`-st power
`tensorObj L.obj (tensorPow L.obj n)`. In particular `tensorPow L.obj 1` is
`L ⊗ 𝒪_X`, which is not literally `L.obj`.

- `L.powSections n` is `GlobalSections (tensorPow L.obj n)`, Mathlib's
  global sections `Γ(X, L^{⊗n})`.
- For `s : L.powSections n`, `L.sectionOpen s` is
  `trivializationOpen (tensorPow L.obj n) s`. This is the generation locus
  `X_s`.
- `L.sectionSubscheme s` is that locus as an actual open subscheme, namely
  `trivializationSubscheme`. `L.sectionInclusion s` is its canonical open
  immersion into `X`, namely `trivializationInclusion`.
- `isAffineOpen_sectionOpen_iff` states that `IsAffineOpen (L.sectionOpen s)`
  is, by definition, `IsAffine (L.sectionSubscheme s)`. The condition is that
  the whole open subscheme `X_s` is affine.

`L.IsAmple` is the proposition

```
CompactSpace X ∧ ∀ x : X, ∃ n : ℕ, 1 ≤ n ∧ ∃ s : L.powSections n,
  x ∈ L.sectionOpen s ∧ IsAffineOpen (L.sectionOpen s)
```

Quasi-compactness of the scheme is compactness of its underlying topological
space. The accessors `IsAmple.compactSpace` and `IsAmple.exists_section`
return the two components.

The affineness condition is on the whole locus `X_s`. It is not on some
chosen affine neighbourhood of `x` on which `s` generates. With that weaker
condition the trivial bundle would be ample on every quasi-compact scheme,
including positive-dimensional proper ones, because the constant section
generates everywhere and every point has an affine neighbourhood. In the
present definition, a section that generates everywhere has `X_s = X`, so it
witnesses ampleness only when `X` itself is affine. This remark is
explanatory and is not a Lean result of this module.

`isAmple_iff_nonvanishingLocus` gives the residue-field formulation under two
explicit hypotheses. The first is `h : LineBundleResidueOpenComparison`. The
second is `hpow : ∀ n, IsLocallyFreeRankOne (tensorPow L.obj n)`. Under them,
`L.IsAmple` holds iff `X` is compact and every `x` has some `n ≥ 1` and
`s : L.powSections n` such that `x ∈ nonvanishingLocus (tensorPow L.obj n) s`,
and some open `U` with underlying set equal to that nonvanishing locus is
affine. Rank one of the tensor powers is not proved here. Its statement is the
separate task `356f47c9-c78c-4158-8e79-f9d86f9debee`.

## Original sources

The registered source is `stacks-invertible-picard-ampleness-2026-10-21`,
directory SHA256
`2a0bbd01484fc7cef97110a88cf4b3e472574fbbb9469d037170744a1462f835`, with files
`01PS.html` and `01CY.html`.

`IsAmple` formalizes Stacks Project Definition 28.27.1, tag
[01PS](https://stacks.math.columbia.edu/tag/01PS), which is EGA II Definition
4.5.3. In that definition `X` is a scheme and `𝓛` is an invertible
`𝒪_X`-module. `𝓛` is ample if `X` is quasi-compact and for every `x ∈ X` there
exist `n ≥ 1` and `s ∈ Γ(X, 𝓛^{⊗n})` such that `x ∈ X_s` and `X_s` is affine.
The quantifier structure, the bound `n ≥ 1`, and affineness of the whole `X_s`
match the Lean definition. The Lean "invertible module" is the published
`LineBundle`, meaning locally isomorphic to the structure sheaf. The tensor
power is the published sheafified `tensorPow`.

The source's `X_s` comes from Stacks Lemma 17.25.10, tag
[01CY](https://stacks.math.columbia.edu/tag/01CY). That lemma defines it as
`{x ∈ X | image s ∉ 𝔪_x 𝓛_x}`, proves that this set is open, and proves that
`s : 𝒪_{X_s} → 𝓛|_{X_s}` is an isomorphism. Here `X_s` is the presentation as
the largest open on which the section-induced map is an isomorphism, so Lemma
17.25.10's isomorphism conclusion holds by construction. In mathematics this
locus is contained in the source's set for any module, and Lemma 17.25.10 gives
equality for invertible modules. For the tensor powers used in `IsAmple`, that
equality is not proved in this module. It is available only through the
explicit hypotheses of `coe_trivializationOpen_eq_nonvanishingLocus` and
`isAmple_iff_nonvanishingLocus`. The residue-field presentation
`nonvanishingLocus` replaces `s_x ∉ 𝔪_x 𝓛_x` by nonvanishing of the pulled-back
section on `Spec κ(x)`. That comparison is part of the separately stated
`LineBundleSectionResidueComparison`.

The source lemma's further section of `𝓛^{⊗ -1}` over `X_s` is not formalized
here. This module does not prove projectivity, existence of ample line bundles,
or any geometric criterion for ampleness. It installs no axioms and assumes no
property of ample bundles as structure.
