# Grouping full-torus row weights in quaternionic cocharacter weight spaces

Let `K` be any field, `D` a finite-dimensional division `K`-algebra, `σ` an
involution of the first kind, and `q` a `σ`-quadratic form on the finite row space
`D^n`. For any morphism `i : 𝔾ₘ^I ⟶ O(q)`, this internal unit compares the published
all-test cocharacter weight spaces with the generic finite matrix row
decomposition.

`torusRowWeightSpace σ q i m` is the submodule of rows fixed by the universal
weight idempotent of exponent `m`. Its defining torus morphism is the composite
of `i` and the published inclusion of `O(q)` into the unit group scheme of the
matrix algebra, using its finite `K`-basis.

`mem_cocharacterWeightSpace_iff_rowActionOver` identifies the defining condition
of the published `σ.cocharacterWeightSpace q (groupHom ν ≫ i) c` with the generic
row-action equation on every commutative coefficient algebra. Both use inverse
right multiplication by the actual unit of the isometry point. The proof
unfolds these definitions and reassociates the actual scheme morphisms.

`cocharacterWeightSpace_eq_iSup_torusRowWeightSpace` proves that this weight
space equals
`⨆ m ∈ cocharacterWeightSupport (i ≫ σ.isometryGroupι q) ν c,
  σ.torusRowWeightSpace q i m`.
Here the finite support consists exactly of the occurring regular exponents
whose actual characters pair with `ν` to give `c`.

For one inclusion, the generic Laurent coefficient reconstruction theorem puts
every all-test eigenvector into this finite supremum. For the other, the
all-test character equation on each full-torus row space restricts along `ν` to
the corresponding integer power. The support condition makes that integer equal
to `c`, so each summand lies in the cocharacter weight space.

The provenance is internal and derived from the published isometry inclusion
and cocharacter definition together with the generic row-weight restriction
unit. The argument imposes no centrality, nondegeneracy, smoothness, faithfulness,
or maximality assumption. It retains finite fields and characteristic 2.
It proves the grouping step and leaves the maximal-torus multiplicities and
Witt-index comparison to further arguments.
