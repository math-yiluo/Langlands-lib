# Integral coroot generation on simply connected pinned charts

This internal helper connects the geometric hypothesis of the affine Weil
restriction problem to the full coordinate root datum on a supplied
`AffinePinnedModel`. It does not construct simple factors or a Weil restriction.

`AffineSimplyConnectedPinnedModel` is an affine pinned model together with the
condition that the integral coroot span is the whole coweight lattice. Every
geometric fibre of such a model is algebraically simply connected. Over a
nonempty affine base this integral condition is equivalent to simple
connectedness of every geometric fibre. Without a nonempty-base hypothesis,
the implication from the integral condition still holds. At every specified
point, simple connectedness of that one geometric fibre is already equivalent
to the integral condition.

The proof uses the published necessity and sufficiency of the split coroot
criterion. The full coordinate datum is carried to the actual character and
cocharacter lattices by `CoordinateRootDatum.fieldRealizationEquiv`. Integral
coroot generation is invariant under this equivalence. For sufficiency, the
published semisimplicity criterion first gives semisimplicity: the quotient by
the coroot span is trivial and therefore finite. The split simple-connectedness
criterion then applies to the actual fibre group. The field/residue/geometric
comparisons reduce the remaining assertions to this field calculation.

This is internally derived from published Library results. Its purpose in the
proof of Conrad's Proposition 6.4.4 is to expose the integral simply connected
root datum needed for splitting into irreducible factors. The motivating source
is Brian Conrad, *Reductive group schemes* (2014), registered as
`conrad-2014-reductive-group-schemes`, Proposition 6.4.4 and its proof,
pp.232–233. No factorization or descent theorem is asserted in this module.
