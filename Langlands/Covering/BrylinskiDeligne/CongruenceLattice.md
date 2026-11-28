# The integral lattice cut out by a bilinear congruence

In `Langlands.Covering.BrylinskiDeligne`, let `Y` be an additive commutative
group with its canonical integer module structure, `B : LinearMap.BilinForm ℤ Y`,
and `n : ℕ`. The submodule `congruenceLattice B n` has membership formula

\[
  y \in Y_{B,n} \quad\Longleftrightarrow\quad
    (n: \mathbb Z) \mid B(y,z) \quad\text{for every } z \in Y.
\]

`mem_congruenceLattice` exposes the formula. Bilinearity and closure of
integer divisibility under addition and multiplication give the submodule laws.
`congruenceLatticeInclusion` is the subtype inclusion and
`congruenceLatticeInclusion_injective` proves its injectivity.
`smul_mem_congruenceLattice` and `range_lsmul_le_congruenceLattice` show that
multiplication by `n` takes `Y` into this submodule, since
\(B(ny,z)=nB(y,z)\). `congruenceLattice_one` identifies the submodule with the
top submodule when `n = 1`.

## Rank and index

`congruenceLattice_finite` uses Noetherianity to inherit finite generation
from `Y`. When `Y` is finite free, `congruenceLattice_free` uses freeness of
submodules of finite free modules over the principal ideal domain `ℤ`. For
`0 < n`, multiplication by `n` is injective on the free integral module. Its
factorization through the congruence submodule and the subtype inclusion bound
the two ranks in opposite directions. `congruenceLattice_finrank` gives equality,
and `congruenceLattice_finiteQuotient` applies the finite-quotient result for an
equal-rank submodule of a free integral module. These arguments apply to a
degenerate `B` and to rank zero.

## Equivariance

For an integer-linear equivalence `e : Y ≃ₗ[ℤ] Y` preserving `B` in both
arguments, `apply_mem_congruenceLattice_iff` uses surjectivity of `e` to
change the test vector in the membership formula. `congruenceLatticeEquiv`
restricts `e` to an integer-linear equivalence of the submodule, and
`congruenceLatticeInclusion_equiv_apply` identifies its action after inclusion
with application of `e` in `Y`.

## Source and scope

For `B = QuadraticMap.polarBilin Q` on a cocharacter lattice, the formula gives
\(Y_{Q,n}\) of Gan–Gao, *The Langlands–Weissman program for Brylinski–Deligne
extensions*, §3.4, printed p. 206, and of Weissman, *Split metaplectic groups
and their L-groups*, §1.3, Definition 1.1 and Construction 1.3, printed
pp. 94–95. Gan–Gao use the inclusion of this lattice in `Y` for the split torus
isogeny and use the lattice in the modified root datum in §5.1, printed
pp. 212–213. The construction here uses the same congruence for an arbitrary
integral bilinear form. The polarization, symmetry, and nondegeneracy of the
form are unnecessary for the submodule and its rank and index properties.
