# Positive forms on actual tensor slices and local factors

This internal construction pulls a supplied invariant positive form on a specified
finite automorphic realization to its genuine separated local tensor space,
actual tensor slices, and specified local factors. A genuine tensor presentation
and, for a factor, a nonzero complementary tensor remain explicit inputs.

The field `F : Type uF` is a number field, the matrix rank is any `n : ℕ`, and
coefficients are complex. The local carriers `V v : Type uV` are complex modules;
`uF` and `uV` are independent. No topology or finite dimensionality of those
carriers is required. The representation family `ρ`, exceptional finite set `E`,
reference vectors `e`, and their integral-fixed law `he` are the inputs of the
published `FiniteTensorPresentation`. That presentation also includes nonzero
reference vectors outside `E` and a genuine finite adelic representation
equivalence onto `S : FiniteRealization F n`. The target is an actual invariant
subspace of the existing automorphic form space.

`b : InvariantPositiveForm S.representation` is a supplied positive definite
Hermitian form for its actual finite action. The constructions prove their
invariance; they do not assume forms on the factors.

`sliceInclusion v y` is the subtype inclusion of the actual tensor slice into
the whole local restriction of `S`, using the published containment `slice_le`.
The inherited right actions make it an intertwiner, and subtype injectivity
makes it faithful. Its composition with inclusion into automorphic forms is
literally the slice's original inclusion. After the genuine `sliceEquiv` from
a factor, it is `P.localEquiv v (x ⊗ y)`, retaining the full complementary
tensor construction and the original embedded form.

`separatedUnitaryForm` first restricts `b` along the actual one-place finite
adelic inclusion, retaining the same positive core. It then pulls back through
the genuine `localEquiv` to `V v ⊗ LocalTensorTail F E v e`. Its inner product is

```text
B_sep(x,z) = b(P.localEquiv v x, P.localEquiv v z).
```

No tensor product formula for this positive form is supplied or required.

`sliceUnitaryForm` pulls the restricted form back along `sliceInclusion`.
Injectivity preserves definiteness as well as positivity and invariance. This
construction works for every complementary vector, including zero, when its
actual slice is zero. Its value is `b` evaluated on the two included vectors.

For `hy : y ≠ 0`, the published `sliceEquiv v y hy` is an actual equivariant
linear equivalence from `ρ v` to the slice representation. `factorUnitaryForm`
pulls the slice form back through that equivalence. The definitions of the
pullbacks, slice equivalence and subtype maps give the exact formulas

```text
B_factor(x,z) = B_slice(P.sliceEquiv v y hy x, P.sliceEquiv v y hy z)
              = b(P.localEquiv v (x ⊗ y), P.localEquiv v (z ⊗ y))
              = B_sep(x ⊗ y, z ⊗ y).
```

Thus the actual slice equivalence and the fixed-tail embedding preserve the
constructed forms. The factor form can depend on the supplied `b`, presentation
and complementary vector. The existence theorems extract a supplied global
positive-form witness and supply these constructed slice and factor forms;
the factor theorem retains `y` and `hy`.

`OperatorRealization.UnitaryForm.tensorFactorForm` specializes this construction
to a supplied whole-operator form and a genuine presentation of its actual
finite form image. It first transports the finite part of that same form
through the inverse of the existing faithful finite-image equivalence, then
applies `factorUnitaryForm`. No new local positivity premise is introduced.

Provenance is internal. The module composes the published actual presentation,
local separation, slice containment and equivalence constructions from
`TensorPresentation`, the actual finite-image equivalence and whole-operator
form from `OperatorUnitaryForm`, and the generic injective pullback and
restriction operations in `Representation/Unitary/{Basic,Restriction}`.
The new formulas follow from those concrete maps' definitions. No new
identification with external literature is asserted.

This module proves neither existence of a global positive form nor existence
of a tensor presentation or a nonzero complementary tensor in general. It does
not choose canonical forms, identify different factor families, prove
irreducibility or admissibility, descend forms to arbitrary quotients, or
construct a topology, Hilbert globalization, invariant integral or spectral
occurrence. In particular, whole local restriction and a single local factor
retain their distinct carriers.
