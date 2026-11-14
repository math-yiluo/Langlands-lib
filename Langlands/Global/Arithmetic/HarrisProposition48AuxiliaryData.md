# One auxiliary place in the internal induction

These internal definitions give the induction a stronger, one-place
scope than the unchanged two-place Proposition 4.8 target. They assert
no existence or inheritance theorem.

`Proposition48Problem.IsAuxiliaryValidAtParity Q b` retains normalized
reciprocity, the split imaginary quadratic subfield, the actual normal
closure and scalar tower, the auxiliary place above the rational prime,
its compatible completion maps, unique places above it and its conjugate,
general position of its prescribed local character, algebraicity at the
specified parity, relative regularity, conjugate inversion and the
prescribed auxiliary component. `IsAuxiliaryValid` uses `[E':E]−1`.
There are no conditions on the primary place `P` or its character `χ`.
The full original validity implies this auxiliary validity; their output
`HasSolution` is exactly the same four-part conclusion.

The original bundle is reused as a data carrier. Its otherwise unused
primary place and character can always be supplied by duplicating the
auxiliary data, implemented by `auxiliaryPadding`. This operation is
not claimed to produce a fully valid two-place problem: the original
distinctness condition would fail. It leaves every field, the auxiliary
place and the global character fixed.

`IsAuxiliaryMackeyChild Q D a R` applies the existing concrete
`IsMackeyChild` relation to the padded parent and child. Consequently
it requires the same field isomorphisms, commuting inclusions into the
closure, quadratic-subfield image, rational prime and exact transported
raw norm character. Its two place clauses coincide and require only the
child's auxiliary place to lie above the parent's auxiliary place.

This distinction avoids an unjustified inheritance assertion. The
original two-place datum has separate identifications of the closure's
completions at `P` and `Ps` with the same local normal closure. It does
not explicitly align their induced Galois-group identifications.
The present route therefore does not require every intermediate field
to have identical local extensions at both places. Only the place used
for general position is inherited by the internal induction.

`IsAuxiliaryParityNormalization` retains the genuine base character,
norm pullback, conjugate inversion, correcting parity and trivial choice
when parities agree from `IsParityNormalization`. Its corrected-validity
clause uses the one-place hypotheses, with the new auxiliary local
character. The actual `IsSolution` and `IsUntwistedSolution` predicates
already use only the auxiliary place, so they are reused unchanged.

Source: M. Harris, *The local Langlands conjecture for GL(n) over a p-adic
field, n < p*, Invent. Math. 134 (1998), 177–210,
`harris-1998-local-langlands`: Section 4 setup, pp.200–201;
Proposition 4.8 proof, p.202, the inherited conditions (i)–(iii) and the
supercuspidal component at the prime above `v(*)₁`
(TeX `math_9611226v1.tex`, lines 1574–1614);
rank-dependent normalization, p.195, and the half-integral twist remark,
p.191, lines 866–875. The one-place induction interface and padding
are derived formalization choices, not statements attributed verbatim
to Harris. No existing declaration is changed.
