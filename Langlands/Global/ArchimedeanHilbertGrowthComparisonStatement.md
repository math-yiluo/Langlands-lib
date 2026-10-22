# Actual archimedean norm comparison and polynomial growth

This module states a derived comparison obligation for the published concrete
norms. Its four declarations are proposition-valued definitions; it supplies
no proof of the comparison or of the growth equivalences.

## Domain and the two norms

Every declaration has parameters `(K : Type u) [Field K] [NumberField K]`
and `(n : ℕ)`, with arbitrary universe `u` and every natural rank, including
zero. The group is the existing `Langlands.Global.InfiniteAdelicGL K n`,
the invertible `Fin n` matrices over the actual infinite adele ring. It
retains its completion-based topology. The multiplicative homeomorphism
`archimedeanGLCoordinates K n` identifies this topology with that of
invertible matrices over the finite product of real and complex coordinates.
There is no replacement topology or supplied comparison assumption.

Write `M(g) = (archimedeanGLCoordinates K n g).val`. The first norm is the
existing `Langlands.Global.ArchimedeanGL.matrixHeight`, namely

\[
 H(g)=\max(1,\max(\|M(g)\|_{\mathrm{row}},\|M(g)^{-1}\|_{\mathrm{row}})).
\]

Here the entry ring has its finite-product supremum norm. More explicitly,
the norm of an entry is the maximum of its real-place absolute values and
complex-place absolute values, with an empty supremum interpreted as zero.
The matrix norm is the supremum over rows of the sum over columns of these
entry norms, as selected by `Matrix.Norms.Operator` in the published
definition. Thus the supremum over places is taken **inside** the row sum.
It is not the normalized multiplicative absolute value of the infinite
adele ring. The inverse is the actual matrix inverse supplied by the unit.

The second norm is the existing
`Langlands.Global.infiniteAdelicHilbertNorm`. Let `A(g)` be the complex block
matrix of all local standard matrices, using the usual inclusion into
complex numbers at real places and one complex block at each complex place.
The published representation on the actual Euclidean Hilbert space
`ArchimedeanHilbertSpace K n` has orthonormal-coordinate matrix

\[
 \sigma(g)=\operatorname{diag}(1,A(g),(A(g)^{-1})^H).
\]

The superscript `H` denotes conjugate transpose. Its norm is

\[
 h(g)=\sqrt{\operatorname{Re}\operatorname{tr}_{\mathbb C,E}
                 (\sigma(g)^*\sigma(g))},
 \qquad E=\operatorname{ArchimedeanHilbertSpace}(K,n),
\]

where `*` is the actual Hilbert adjoint on continuous complex-linear
endomorphisms and the trace is `LinearMap.trace`. The published theorem
`infiniteAdelicHilbertNorm_sq` gives

\[
 h(g)^2=1+S(g)+S(g^{-1}),\qquad
 S(g)=\sum_{v\ {\rm real}}\sum_{i,j}|M_v(g)_{ij}|^2+
      \sum_{v\ {\rm complex}}\sum_{i,j}|M_v(g)_{ij}|^2.
\]

The local matrices are the published `ArchimedeanGL.realMatrix` and
`ArchimedeanGL.complexMatrix` after the coordinate map, and `i,j : Fin n`.
There is no factor of two at complex places. The scalar block contributes
exactly one. Both norms are at least one. At rank zero the row norms and
the local entry sums are zero, so both norms are exactly one; the
comparison target retains this case.

## Exact comparison and growth targets

All names below belong to `Langlands.Global`.

`ArchimedeanMatrixHilbertComparisonStatement K n` is

\[
 \exists C,D\in\mathbb R,\quad C>0\ \land\ D>0\ \land\
 \forall g\in\operatorname{InfiniteAdelicGL}(K,n),\quad
 H(g)\le C h(g)\ \land\ h(g)\le D H(g).
\]

The constants may depend on `K,n`, but are chosen before `g` and are uniform
over the entire group. Both directions are linear. Neither the inverse
block nor the scalar normalization is removed.

`ArchimedeanHilbertGrowthEquivalenceStatement K n` states, for every function
`f : InfiniteAdelicGL K n → ℂ`,

\[
 \operatorname{ArchimedeanGL.HasPolynomialGrowth}(K,n,f)
 \quad\Longleftrightarrow\quad
 \exists B\in\mathbb R,\ B\ge0\ \land\
 \exists d\in\mathbb N,\ \forall g,\ |f(g)|\le B h(g)^d.
\]

The left side is the existing matrix-height growth predicate with precisely
the analogous quantifiers and `H(g)^d`. There is no continuity or
smoothness assumption on `f`. The growth bound may be zero and the natural
exponent may be zero. The existential witnesses on the two sides need not
be the same.

`AdelicHilbertGrowthEquivalenceStatement K n` states, for every
`f : Langlands.Automorphic.ContinuousRationalFunctions K n`,

\[
 \operatorname{Langlands.Automorphic.HasPolynomialGrowth}(K,n,f)
 \quad\Longleftrightarrow\quad
 \forall b\in\operatorname{FiniteAdelicGL}(K,n),\
 \exists B\in\mathbb R,\ B\ge0\ \land\
 \exists d\in\mathbb N,\ \forall g,\ |f(g,b)|\le B h(g)^d.
\]

Here `f(g,b)` is exactly
`Langlands.Automorphic.infiniteSlice K n b f g`, namely evaluation at
`AdelicGL.pair K n g b`. The ambient functions are continuous and invariant
under rational left translation as already required by their existing
carrier. Both the bound and the exponent are chosen after the finite slice
`b`; no uniformity over finite slices is asserted. Zero bounds and zero
exponents are again allowed.

The single aggregate proof target is
`Langlands.Global.ArchimedeanHilbertGrowthComparisonStatement K n`.
It is the conjunction, in order, of the linear comparison, the infinite
growth equivalence, and the adelic growth equivalence. Its only parameters
are the number field with its instances and the natural rank. All four
declarations return `Prop`.

## Provenance and proof boundary

A. Borel and H. Jacquet, *Automorphic forms and automorphic representations*,
in *Automorphic Forms, Representations and L-Functions*, Proceedings of
Symposia in Pure Mathematics 33, Part 1 (1979), pp. 189–202, §1.2, printed
pp. 189–190 (one-based PDF pages 184–185), defines representation
Hilbert–Schmidt norms and discusses independence of polynomial growth from
the choice of such norm. Its remark adds the inverse-adjoint representation
to control escape to singular endomorphisms. Section 4.2(d), printed p. 195
(PDF page 190), imposes growth separately on each fixed finite slice.

Registered source: `borel-jacquet-1979-automorphic`. Original read:
`/home/taskhub/central-library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part I.pdf`.
SHA256:
`3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
These three original pages were read directly. No source errata note was
present in the Library or shared notes; the retained volume README gave no
errata.

The specific two-sided **linear** comparison here is a derived
finite-coordinate norm-equivalence obligation for the existing constructions,
not a theorem quoted verbatim from that source. The scalar augmentation is
the already published normalization. The intended growth implications
rescale a matrix-growth bound `B` to `B * C^d`, and a Hilbert-growth bound
to `B * D^d`; applying the infinite equivalence separately to each slice
gives the adelic target. These observations explain the formulation, not
an implemented Lean proof. The source uses positive integer exponents;
allowing zero here is compatible with the existing predicates since both
norms are at least one.

The imported Hilbert construction proves invariance under the published
standard compact, while its maximality is a separate statement. This
comparison does not assume or establish that maximality, the other
automorphic conditions, or the full automorphic-space identification.
