# Relative closed-equation quotient spectra and coefficient transport

This module constructs a homeomorphism from the multiplicative spectrum of an
actual relative equation quotient onto the common zero set of its equations in
the relative series spectrum. It also constructs the continuous pullbacks
induced by compatible bounded coefficient maps and proves their naturality.
All declarations are in
`Langlands.Analytic.PresentedAffinoidAlgebra.RelativeRelations`.

## Parameters and actual carriers

Let `K` be a normed field with ultrametric distance, let `A` be an actual
`PresentedAffinoidAlgebra K`, and let `s : PositivePolyradius (Fin m)` be any finite
positive real polyradius. Write

\[
R_A=A\{s^{-1}T\}=\texttt{GeneralizedTateAlgebra s A}.
\]

For an arbitrary set `E : Set R_A`, the imported construction gives

\[
I_E=\overline{(E)},\qquad
Q_E=R_A/I_E=\texttt{QuotientAlgebra K A s E}.
\]

Here `(E)` is `Ideal.span E`. The closure is taken in the weighted norm topology,
and the quotient has its actual quotient norm. The maps `quotientMap`, `baseMap`
and `newCoordinate` are the existing projection, constant inclusion followed by
projection, and images of the new variables. No new carrier or alternative norm
is introduced.

The spectrum `BanachSpectrum R` consists of normalized multiplicative seminorms
bounded above by the norm of `R`, with the topology of pointwise evaluation.
It is defined for normed commutative rings, including the incomplete rings
allowed here.

## Equations, closed ideals and the homeomorphism

`equationLocus K A s E` is the subset

\[
Z(E)=\{x\in\mathcal M(R_A):\ \forall f\in E,\ x(f)=0\}.
\]

`mem_equationLocus_iff` proves that this is equivalent to `I_E ≤ x.kernel`.
For a fixed spectrum point, evaluation as a function of the algebra element is
continuous by the imported joint evaluation theorem. Consequently its kernel
ideal is closed. Generator vanishing first extends to `Ideal.span E`, then to
its closure by `closure_minimal`. The converse uses the imported membership of
each equation in `I_E`.

`equationLocus_eq_zeroLocus` identifies `Z(E)` with the generic ideal zero locus.
It follows that this set is closed and compact; the module also supplies a
`CompactSpace` instance for its subtype.

`spectrumMap` is continuous pullback along `quotientMap`. The generic closed-ideal
quotient spectrum theorem supplies `isClosedEmbedding_spectrumMap` and
`range_spectrumMap`, with range rewritten as `Z(E)`. Its evaluation formula is

\[
\texttt{spectrumMap}(y)(f)=y(\overline f).
\]

`spectrumHomeomorph K A s E` explicitly constructs

\[
\mathcal M(Q_E)\ \simeq_{\mathrm{top}}\ Z(E).
\]

The forward map is `spectrumMap` with its proved locus membership. The inverse
is the generic `BanachSpectrum.descend` applied to a point whose kernel contains
`I_E`. Both inverse identities are checked on series representatives using
surjectivity of `quotientMap`. Forward continuity is inherited from
`spectrumMap`; inverse continuity is proved in the pointwise topology: evaluation
at a quotient element is evaluation at any series representative. In particular,

\[
\texttt{spectrumHomeomorph}^{-1}(x)(\overline f)=x(f).
\]

The displayed forward and inverse formulas are the two corresponding simp lemmas.

## Compatible coefficient maps and naturality

Let `B` and `C` be actual presented algebras over the same `K` and use the same
new polyradius `s`. For equation sets `E`, `F`, `G` in their respective relative
series algebras, let `φ : BoundedAlgHom K A B` satisfy the imported condition
`MapsRelations K s φ E F`. This condition says that the actual coefficientwise
series image of each generator in `E` belongs to the target closed ideal `I_F`.
The imported `transport` then gives the bounded map `Q_E → Q_F`.

`spectrumTransport` is its contravariant continuous spectrum map. For
`y : BanachSpectrum Q_F`, its representative, coefficient and coordinate laws
are

\[
\begin{aligned}
\phi^*(y)(\overline f)&=y(\overline{\phi_*(f)}),\\
\phi^*(y)(\texttt{baseMap}(a))&=
  y(\texttt{baseMap}(\phi(a))),\\
\phi^*(y)(\texttt{newCoordinate}(j))&=
  y(\texttt{newCoordinate}(j)).
\end{aligned}
\]

`equationLocusTransport` restricts pullback along the coefficientwise series map
to a continuous map `Z(F) → Z(E)`. Membership uses the proved fact that a point
of `Z(F)` annihilates all of `I_F`; it does not require the image equation to be
a generator in `F`. Its formula is

\[
(\phi^*x)(f)=x(\phi_*(f)).
\]

The module proves the resulting constant-series and variable formulas. Both
`spectrumTransport` and `equationLocusTransport` preserve identity and reverse
composition as equalities of bundled continuous maps. The proofs reduce to the
corresponding imported quotient or coefficientwise map laws, using spectrum
extensionality.

`spectrumHomeomorph_naturality` proves the commuting square pointwise:

\[
h_E(\phi^*y)=\phi^*(h_F(y)),
\]

where `h_E` and `h_F` are the constructed quotient-to-locus homeomorphisms.
Both sides evaluate to `y` on the same quotient representative.

## Supplied bounded base equivalences

Given `e : BoundedAlgEquiv K A B` and `MapsRelations` for both `e` and `e.symm`,
`spectrumTransportHomeomorph` applies the existing spectrum homeomorphism
construction to the actual quotient equivalence `transportEquiv`. Its forward
and inverse maps are exactly `spectrumTransport` for these two base maps.

`equationLocusHomeomorph` conjugates that homeomorphism by `h_F` and `h_E`,
producing `Z(F) ≃ₜ Z(E)`. The two application lemmas identify its forward and
inverse maps with `equationLocusTransport`. Boundedness of the base equivalence
and its inverse suffices; no norm preservation or isometry is assumed.

## Scope and provenance

No completeness, proper-ideal, nonempty-equation-set, nonempty-variable-block
or nontrivial-valuation hypothesis is added. Nonproper ideals and zero
quotients remain allowed; the homeomorphism makes no nonemptiness assertion.
For complete `K`, the imported relative quotient is complete. Over incomplete
`K`, these are constructions for the specified normed algebras, without an
affinoid classification claim. General presentation independence, the
additional-equation scalar comparison, structure sheaves, analytic domains and
sites are separate obligations.

The registered original is Vladimir Berkovich, *Non-Archimedean analytic
spaces*, Trieste lectures (2009), source
`berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Definitions 1.2.3 and 1.2.5 and Exercise 1.2.4 on printed/PDF page 4 give
bounded multiplicative spectra, the constant-one bound and the evaluation
topology. Section 2.1, page 7, gives the quotient norm. Definition 2.1.6(i)-(ii),
page 8, supplies the relative weighted restricted series and relative affinoid
convention; Definition 2.1.11 on that page describes the contravariant
affinoid-space category. These source passages are motivation and conventions.
The zero-locus homeomorphism, its naturality and coefficient transport laws
implemented here are internal consequences of the imported actual quotient,
generic quotient spectrum descent, joint evaluation continuity and bounded
equivalence constructions. They are not attributed to those numbered source
definitions as stated theorems.
