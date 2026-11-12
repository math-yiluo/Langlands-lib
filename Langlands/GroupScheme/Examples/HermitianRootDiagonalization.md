# Diagonal coordinates for anisotropic Hermitian spaces

For an arbitrary field `L`, a ring involution `c` on `L`, and a
finite-dimensional `L`-vector space `V`, this module takes an actual
sesquilinear pairing

```text
h : V →ₗ[L] V →ₛₗ[c.bar.toRingHom] L
```

with `c.bar (h x y) = h y x` and anisotropy
`∀ x, h x x = 0 → x = 0`. The pairing is linear in the first argument
and conjugate linear in the second, matching `DiagonalForm.pairing`.
The universes of the field and vector space are independent. There is no
restriction on the characteristic, and the involution need not be nontrivial.

`orthogonalBasisOfAnisotropic` chooses a basis indexed by
`Fin (Module.finrank L V)` whose distinct basis vectors are orthogonal.
`diagonalFormOfAnisotropic` is the actual `HermitianRoot.DiagonalForm` with
weights `h (b i) (b i)` in this basis; Hermitian symmetry makes each weight
fixed by `c.bar`. `diagonalCoordinatesOfAnisotropic` is the `L`-linear
coordinate equivalence from `V` to the corresponding function space.

`diagonalFormOfAnisotropic_pairing` proves that these coordinates preserve
**every** pairing value:

```text
H.pairing (e x) (e y) = h x y.
```

Consequently the constructed diagonal form is anisotropic and all its weights
are nonzero. `exists_anisotropic_diagonal_coordinates` packages the actual
form, its anisotropy, and the pairing-preserving linear equivalence. The
zero-dimensional space is included: its coordinate index is empty.

The proof first establishes the general helper
`Langlands.Sesquilinear.exists_orthogonal_basis` for a reflexive
sesquilinear form whose second argument is linear and whose self-pairing
vanishes only on zero. A nonzero vector has nonzero self-pairing, so its line
and right orthogonal subspace are complementary. Induction on dimension
restricts the form and anisotropy to that complement and adjoins the chosen
vector with `Basis.mkFinCons`. Reflexivity gives orthogonality in the reverse
direction. For the Hermitian pairing, apply this helper to `h.flip`.
Expanding both arguments in the resulting basis eliminates every off-diagonal
term and gives precisely the existing diagonal pairing formula. Transport
through the coordinate equivalence proves anisotropy of the diagonal form.

This is a derived internal algebraic unit. The induction adapts Mathlib's
`LinearMap.BilinForm.exists_orthogonal_basis` in
`Mathlib.LinearAlgebra.QuadraticForm.Basic`, retaining its Apache 2.0
attribution. Anisotropy provides the nonzero self-pairing directly, so this
adaptation needs no invertibility-of-two premise. The complement and finite
basis constructions use Mathlib's sesquilinear orthogonal submodules and
finite-dimensional linear algebra. No external classification or arithmetic
result is assumed. This module does not construct a Hermitian presentation
of an arbitrary algebraic group, prove a local Hermitian dimension bound,
or prove the rank-one group classification.
