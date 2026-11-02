# A common matrix-height exponent for all enveloping derivatives

Authors: Workers 116 and 94. This target strengthens the existing
archimedean differential-growth interface using the same smooth functions,
compact group, enveloping action and matrix/inverse height.

`Langlands.Global.ArchimedeanGL.FiniteUniformDifferentialGrowthStatement K n`
quantifies over any number field `K` in an arbitrary universe and every
natural rank `n`, including zero. For an actual `f : SmoothFunctions K n`
it assumes:

- the complex span of its orbit under the actual standard infinite compact
  group is finite-dimensional, expressed by `IsFiniteVector` for the
  restriction of `smoothRightAction`;
- its orbit under the center of the actual complex enveloping algebra is
  finite-dimensional, expressed by `IsCenterFinite K n f`;
- a supplied nonnegative real constant `C` and natural exponent `d` satisfy
  `‖f.val g‖ ≤ C * matrixHeight K n g ^ d` for every infinite adelic point.

For every element `a` of that enveloping algebra, the conclusion supplies
a nonnegative real `D` with
`‖(envelopingAction K n a f).val g‖ ≤ D * matrixHeight K n g ^ d`
for every point `g`. The supplied `d` is unchanged for every `a`; `D` may
depend on `a`, `f` and the supplied bound. The target quantifies over every
available input bound, rather than only choosing some larger common exponent.
No reproducing kernel, differentiated bound or measure is assumed.

The height is exactly the Library's `matrixHeight`: the maximum of one and
the norms of the matrix and its inverse in `archimedeanGLCoordinates`.
The smooth-function space and actions are those of `ArchimedeanGL`,
`ArchimedeanCompact` and `ArchimedeanEnvelopingAction`. This unit introduces
only a proposition definition.

## Original-source correspondence and derived scope

The source is Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein
Series* (1995), registered as
`moeglin-waldspurger-1995-spectral-decomposition`. Its retained chapter file
is `05.2_pp_18_40_Automorphic_forms_growth_constant_terms.pdf`,
SHA-256 `296dcb3e7170bb0c2689cf0c79136a43cd86976df2b4c51f027cf9365f7fe988`,
inside the registered folder with SHA-256
`1ba99fb90916a687503e88c7191dad43b9c4865b68e6b4221a4f2126f2d2f141`.

I.2.3, printed pp.24–25, defines uniform moderate growth with one exponent
preceding the choice of enveloping derivative. I.2.5, pp.26–27, gives
uniform derivative growth after compact smooth convolution. The reproduction
lemma in I.2.17, p.38, and its application on p.39 give the corresponding
automorphic consequence. The p.39 remark states that this reproduction
lemma is independent of the later automorphic finiteness theorem.
The full chapter was read, with the relevant passages reread for this target.
No source-specific errata note was found in the checked project and pinned
Library notes.

This is a derived archimedean specialization and strengthening of that route,
not the source's full adelic assertion. It uses the Library's particular
matrix height and natural powers. It applies to compact-finite, center-finite
smooth functions on the infinite adelic group, without assuming rational
invariance, a central character or finite adelic data. The exact preservation
of every supplied exponent follows from the existing explicit-exponent
compact-convolution bound, rather than from a literal assertion about this
height in MW95.

## Relation to existing results and remaining obligations

The published `enveloping_hasPolynomialGrowth_of_finite` in
`ArchimedeanFiniteDifferentialGrowth` gives a separate existential
`HasPolynomialGrowth` witness for each derivative. Its statement permits
the exponent to vary. The proposed proof of this stronger target follows
the same actual reproduction and differentiation argument but retains
the exponent through `compactKernelConvolutionBound`. Worker 94 authored
the reused argument and constructions; Worker 116 formulated this
strengthening.

This file supplies no proof. Its proof requires an exact-target child after
publication. A proof of the target would give a common exponent on this
infinite adelic group, and hence on each fixed finite slice when the existing
automorphic interfaces supply the hypotheses. Comparison to uniform global
adelic growth, including control across finite slices, remains separate.
General connected reductive groups, Siegel-domain decay, constant terms,
cuspidal Hilbert-space comparison and the spectral decomposition remain
further program obligations.
