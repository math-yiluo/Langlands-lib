# The actual archimedean Whittaker slice comparison over totally complex fields

Module `Langlands.Global.RankinSelberg.InfiniteWhittakerSliceModelTCStatement`, namespace
`Langlands.Global.RankinSelbergGlobal`. The number-field universe `u` and spectral
presentation universe `uQ` are independent. The totally complex statement returns `Prop`.

## Exact scope

`InfiniteWhittakerSliceModelAt F` takes `F` with `[Field F]`, `[NumberField F]` and
`[CompactSpace (AdeleQuotient F)]`. It is the body of the existing
`InfiniteWhittakerSliceModelStatement` in
[`EqualInfiniteWhittakerSliceReduction`](EqualInfiniteWhittakerSliceReduction.md) after
these field and instance binders. It ranges over every positive rank `r + 1`, one actual
cuspidal operator realization `T`, a spectral presentation `P`, its irreducible admissible
finite components, and a standard adelic additive character `χ`. The character is
continuous, nontrivial, unitary and trivial on the diagonal number field. The given real
and complex parameter families must be parameters of `T` at the corresponding places.

The result is `Nonempty (InfiniteWhittakerSlice.ModelData P hI χ)`, not an existence
statement about a new representation. As in
[`InfiniteWhittakerSliceProduct`](InfiniteWhittakerSliceProduct.md), at each infinite place
one linear model map on the specified place subspace has a vector of value one at the
identity. For each arbitrary fixed finite tensor, tuple of vectors at the other infinite
places and tuple of other infinite group arguments, the actual one-place Whittaker
slice is a scalar multiple of that model map. The scalar in the slice equality may be
zero, and is independent of the variable vector and group argument at the selected place.
The local affine and smooth group-scheme instances are the same as in the parent definition.

`InfiniteWhittakerSliceModelTCStatement` closes this body over such fields `F` with
`[NumberField.IsTotallyComplex F]` inserted after `[NumberField F]`. At such an `F`,
`IsTotallyComplex.isComplex` and `InfinitePlace.not_isReal_iff_isComplex` make the real
place subtype empty. The real parameter family has no entries and the real parameter
conditions are vacuous. The index of `ModelData` is still the sum of the real and complex
place subtypes, so its model, normalization and slice obligations occur only at complex
places.

## Provenance and proof boundary

J. W. Cogdell, *Analytic theory of L-functions for GL_n*, in J. Bernstein and S. Gelbart
(eds.), *An Introduction to the Langlands Program*, Birkhäuser, 2004, pp. 197–228,
`cogdell-2004-analytic-theory-gln`, §1.2, printed pp. 201–202 (PDF pp. 204–205).
These pages give the local Whittaker model/functional comparison and uniqueness, and
explain the factorization for pure tensors via the restricted tensor product of local
functionals. The comparison of slices on the actual Lean spectral presentation, the
identity normalization, and the fieldwise and totally complex formulations are derived
Library interfaces, not separate source theorems. The statement does not supply or prove
the comparison, construct place tests, or assert any integral factorization or functional
equation. In particular the unrestricted comparison and `ArchimedeanFactorizationStatement`
remain unchanged.
