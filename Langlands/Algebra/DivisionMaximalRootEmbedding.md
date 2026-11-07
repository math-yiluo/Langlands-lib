# Maximal-degree roots and original singleton fields

Let `D` be a finite-dimensional central division algebra over `K`, in an
arbitrary common universe. For an original element `a : D`, its actual
singleton subfield is `residueGeneratorSubalgebra K D a`.

`divisionMaximalRootEquiv` takes a monic irreducible polynomial `f` over `K`
whose degree is the reduced degree of `D`, and a root `b` of `f` in that
singleton subfield. It constructs the algebra equivalence from
`AdjoinRoot f` to the singleton subfield given by evaluation at `b`.
Irreducibility makes the source a field, so evaluation is injective.
Its dimension is the degree of `f`, while the published reduced
characteristic polynomial bound puts the dimension of the singleton
subfield at most the same number. Thus the given evaluation map is
surjective and defines the announced equivalence.

`exists_unit_conj_into_field_of_maximal_root` also takes an actual embedding
of a field `L` into `D`, where `L` can have an independent universe. If `f`
has a root in `L` and a root in the singleton field of an original unit
`a : Dˣ`, the equivalence just constructed gives an embedding of the
whole singleton field into `L`. The published field-embedding conjugacy
theorem applied to its original inclusion and this new embedding gives
an actual unit `u : Dˣ` and `y : Lˣ` with
`a = u * ι(y) * u⁻¹`. The unit `y` is the image of the original singleton
field unit represented by `a`.

This is an internal algebraic deduction from the published singleton
degree bound and field-embedding conjugacy, together with Mathlib's
quotient root field and finite-dimensional linear algebra. It supplies
no polynomial or root existence assertion and no local arithmetic
hypothesis or conclusion.
