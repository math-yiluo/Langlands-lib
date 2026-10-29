# Finite-set section avoidance from a basis of section generation opens

This module defines one proposition, in universe `u`, in the namespace
`Langlands.AlgebraicGeometry.Picard`:
`Langlands.AlgebraicGeometry.Picard.FiniteSectionAvoidanceStatement.{u}`.
It is a derived statement target. The module proves nothing: it does not
prove this proposition, and it does not prove or use any ampleness result.
It imports only `Langlands.AlgebraicGeometry.Picard.Ample` and uses that
module's definitions unchanged.

## Published definitions used

For an arbitrary scheme `X : Scheme.{u}`, a `LineBundle X` is an actual
locally free rank-one module sheaf `L.obj` on `X`. For `L : LineBundle X`:

- `L.powSections n` is
  `Langlands.SchemeModule.GlobalSections
    (Langlands.Scheme.Modules.tensorPow L.obj n)`, the global sections
  `Γ(X, L^{⊗n})` of the actual `n`-th tensor power. The Library's tensor
  powers are right-associated: the zeroth power is the structure module and
  the successor power is `L.obj ⊗ tensorPow L.obj n`.
- `L.sectionOpen s`, for `s : L.powSections n`, is
  `Langlands.SchemeModule.trivializationOpen (tensorPow L.obj n) s`. This is
  the whole generation open `X_s`: the supremum of the opens on which the
  morphism from the structure module sending `1` to `s` restricts to an
  isomorphism. It is not a chosen smaller neighbourhood. The published
  theorems `Langlands.AlgebraicGeometry.Picard.tensorPow_isLocallyFreeRankOne`
  (every tensor power of a line bundle is locally free of rank one) and
  `Langlands.SchemeModule.lineBundleResidueOpenComparison` (for a line
  bundle this open is the residue-field nonvanishing locus) relate it to the
  source's `X_s`. This module neither imports nor assumes them.

## The statement

`FiniteSectionAvoidanceStatement` asserts the following. Let `X` be a scheme
and `L : LineBundle X`. Assume the **section-basis property** for `L`: for
every open `W : X.Opens` and every point `x : X` with `x ∈ W`, there are
`n : ℕ` with `1 ≤ n` and `s : L.powSections n` such that
`x ∈ L.sectionOpen s` and `L.sectionOpen s ≤ W`. Then for every set
`E : Set X` and every open `W : X.Opens` with `E.Finite` and
`E ⊆ (W : Set X)`, there are `n : ℕ` with `1 ≤ n` and `s : L.powSections n`
such that `E ⊆ (L.sectionOpen s : Set X)` and `L.sectionOpen s ≤ W`.

Points of the scope:

- The section-basis property is the only hypothesis besides the finite-set
  data. It concerns all opens of `X` and all of their points, for this one
  line bundle `L`. There is no ampleness, quasi-compactness, separatedness,
  noetherian, affine-neighbourhood, base-field or residue-field hypothesis,
  and no assumed graded prime-avoidance or localization result.
- `X` is an arbitrary scheme and `L` an arbitrary line bundle on it.
- `E` is an arbitrary finite set, possibly empty, and `W` an arbitrary open,
  possibly empty. The exponent is required to be positive (`1 ≤ n`) in every
  case, including the empty set.
- Both inclusions are non-strict and concern the whole generation open:
  `E ⊆ X_s` and `X_s ⊆ W`.
- Nothing is asserted about affineness of `X_s`.

The section-basis hypothesis is literally the conclusion of the published
statement target
`Langlands.AlgebraicGeometry.Picard.AmpleSectionOpenBasisStatement` with its
ampleness premise removed, and the conclusion is literally the conclusion of
`Langlands.AlgebraicGeometry.Picard.AmpleFiniteSetSectionStatement`. Both
targets are in module `Langlands.AlgebraicGeometry.Picard.AmpleSectionOpenStatements`,
which this module does not import. The intended use is that proofs of
`AmpleSectionOpenBasisStatement` and of the present proposition together
give `AmpleFiniteSetSectionStatement` by applying the present proposition
to the basis property for an ample `L`. That deduction is not carried out
here.

## Provenance

This is a derived statement, not a statement of the source. It isolates the
graded prime-avoidance step of the proof of Stacks Project Lemma 28.30.6,
tag [09NV](https://stacks.math.columbia.edu/tag/09NV) (Lemma 30.6 on page 51
of the registered Properties chapter PDF).

Lemma 28.30.6 assumes `L` ample and concludes, for finite `E ⊆ W` with `W`
open, that there are `n > 0` and `s ∈ Γ(X, L^{⊗n})` with `X_s` affine and
`E ⊆ X_s ⊆ W`. Its proof first chooses, by Lemma 28.30.5, an affine open
`U ⊆ W` containing `E`. It then considers the graded ring
`S = ⊕_{n ≥ 0} Γ(X, L^{⊗n})`, the graded prime ideals `𝔭_x` of sections
vanishing at the points `x ∈ E`, and the graded ideal `I` of sections
vanishing on all points of `X \ U`. Since the opens `X_s` form a basis of the
topology, `I ⊄ 𝔭_x` for every `x ∈ E`. Graded prime avoidance (Algebra,
Lemma 10.57.6, as cited by the source) gives a homogeneous `s ∈ I` with
`s ∉ 𝔭_x` for all `x ∈ E`, hence `E ⊆ X_s ⊆ U`. Then `X_s = U ∩ X_s` is
affine by Lemma 28.27.4 (page 41: for affine `U`, `U ∩ X_s` is affine).

The present statement keeps this avoidance step with the open `U` replaced by
`W` itself, and keeps as its hypothesis only the fact used for it: that the
opens `X_s` with `s` homogeneous of positive degree form a basis of the
topology. That fact is item (3) of Stacks Proposition 28.27.13, tag
[01Q6](https://stacks.math.columbia.edu/tag/01Q6), stated there as one of
the equivalent characterizations of ampleness for quasi-compact `X`. Here it
is a hypothesis on an arbitrary scheme. The Lean basis form, "for every open
`W` and `x ∈ W` there is `X_s` with `x ∈ X_s ⊆ W`", is the neighbourhood
formulation of a basis; `n > 0` is expressed as `1 ≤ n`.

Only the finite-covering conclusion `E ⊆ X_s ⊆ W` is requested because that
is exactly the conclusion of the parent target
`AmpleFiniteSetSectionStatement`, which already omits affineness of `X_s`.
The source obtains affineness from the affine open `U` containing `E`, which
Lemma 28.30.5 (page 50) supplies because an ample invertible sheaf exists,
together with Lemma 28.27.4. The present statement assumes neither ampleness
nor such an affine open, and asserts no affineness.

Stacks Lemma 28.30.7, tag [0F20](https://stacks.math.columbia.edu/tag/0F20)
(Lemma 30.7 on pages 51–52 of the PDF), proves a related finite-set assertion
by induction on the number of points: it discards points specializing to
others, then adds sections. It only suggests a possible proof route. Its
setting differs: `X` is quasi-affine, `L` is an arbitrary invertible module,
and the section lies in `Γ(X, L)` itself. Neither its quasi-affine hypothesis
nor its affine conclusion is part of the present statement, and the present
statement is not Lemma 28.30.7.

## Sources and current comments

- `stacks-properties-chapter-2026-10-28`: The Stacks Project Authors,
  *Properties of Schemes* (Chapter 28, tag 01OH), PDF compiled July 14, 2026,
  `literature/Stacks Project — Properties of Schemes chapter (PDF compiled July 14, 2026).pdf`,
  SHA256 `2f5b9ba41e07dd3a888da40496e07afae6caedd550597d96313ab16db4380316`.
  Read for this record: Lemma 30.6 (09NV) and its proof on page 51,
  Lemma 30.7 (0F20) and its proof on pages 51–52, and the statements of
  Lemma 27.4 (01PV, page 41) and Lemma 30.5 (01ZY, page 50) used in the
  proof of Lemma 30.6.
- `stacks-section-open-prerequisites-2026-10-29`: current HTML and comments
  of tags 01Q3, 01Q6, 09NV, 01PW, 01PY and 0F20, retrieved October 29, 2026,
  directory SHA256
  `290fd705ee87e9b334a225352ff3b4d9118789a923dac35712126f59581269cf`.
  Read for this record: `09NV.html`, `0F20.html` and `01Q6.html`, which show
  no comments, and the statement of Proposition 28.27.13 and its eight
  comments in `01Q3.html`. The current text of 09NV and 0F20 agrees with the
  PDF passages used here. The 01Q3 comments ask whether quasi-compactness is
  needed for implication (1) ⇒ (2) and discuss cohomological criteria. They
  do not change item (3), which the present statement uses only as a
  hypothesis. No project errata note for either source was present when
  this record was written.

The Lean statement was specified in its task contract. Worker 869 wrote this
module and its companion.
