# Scalar tensor pairs and their actual inertia Euler polynomials

This internal construction works over any field `K`, for any group `G`, any
normal subgroup `I`, and any supplied norm character `ν : G →* Kˣ`. The field and
group universes are independent. It uses the actual scalar-character
representations, Weil–Deligne pairs and inertia-fixed monodromy kernels.

`FiniteRepresentation.scalarCharacterTensorEquiv` identifies the tensor of the
scalar representations for `χ` and `η` with the scalar representation for `χ * η`.
Its linear equivalence is the tensor left unitor, which sends `x ⊗ y` to `x * y`.
Tensor-product extensionality reduces equivariance to commutativity and
associativity of multiplication in `K`.
`WeilDeligneRepresentation.scalarCharacterTensorEquiv` lifts that equivalence to
the tensor of the corresponding zero-monodromy pairs; the tensor monodromy
`0 ⊗ 1 + 1 ⊗ 0` is zero.

`scalarCharacter_inertiaKernel_eq_zero` assumes a witness `w ∈ I` with `χ w ≠ 1`.
The fixed-vector equation gives `(χ(w) - 1) * v = 0`, hence `v = 0` in the field.
`eulerPolynomial_scalarCharacter_of_ramified` therefore computes the Euler
polynomial as `1`, by using the empty basis on that zero-dimensional kernel.

`eulerPolynomial_scalarCharacter_of_unramified` instead assumes `χ w = 1` for
every `w ∈ I`. Zero monodromy and the trivial inertia action let the existing
`LocalFactor.WeilDeligne.eulerPolynomial_eq_of_monodromy_eq_zero` comparison replace
the fixed kernel by the full scalar line. The singleton basis and the generic
diagonal Euler-polynomial formula then give `1 - C (χ g) * X` at every `g : G`.

These are internal linear-algebra consequences of the published character,
tensor, kernel and Euler-polynomial constructions. This unit does not assert
reciprocity existence, the comparison with a field-character conductor, a
class-level arithmetic L-factor formula, a JPSS or epsilon comparison, or the
closed correspondence theorem.
