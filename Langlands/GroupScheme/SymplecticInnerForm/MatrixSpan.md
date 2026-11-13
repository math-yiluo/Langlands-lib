# Symplectic matrices span the matrix algebra

Over every commutative ring `R`, `span_symplectic` proves that the
`R`-linear span of the standard symplectic matrices on `l ⊕ l` is the full
matrix algebra. The finite index type `l` can be empty. The result includes
characteristic two.

The proof first checks that the linear span of the matrix group is closed
under multiplication, by two span inductions. Subtracting the identity from
the upper and lower symplectic unipotents with a single diagonal entry gives
the two matrix units joining the copies of each index. Their products give
the diagonal matrix units. Sandwiching upper and lower unipotents with
symmetric off-diagonal blocks between these diagonal units gives every
matrix unit between the two copies of `l`. Products then give the remaining
matrix units. Every matrix is the sum of its scalar multiples of these units.
No division or restriction on the coefficient ring is used.

`linearMap_ext_symplectic` follows by induction on this full span: two
`R`-linear maps into any `R`-module agree if they agree on all symplectic
matrices.

These are internal algebraic lemmas for extending an inner action on the
symplectic group to its matrix algebra. They adapt the elementary matrix-span
method of the published `SpecialLinearInnerForm/MatrixSpan` module, using the
published upper and lower matrices from `SymplecticMatrix/Generation`.
They assert neither descent nor classification of inner forms.
