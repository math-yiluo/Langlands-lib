# Factoring the level-zero intertwining domain

The support calculation in Bushnell–Kutzko, *The admissible dual of GL(N)
via compact open subgroups* (1993), Proposition (5.3.2)(i), printed pp. 176–177,
uses the simultaneous version of the relative-unit factorization in (3.1.15)(i),
printed p. 95. The retained source `bushnell-kutzko-1993-admissible-dual-gln`
has SHA-256 `811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.

The projection lemma assumes `F[β]` is a field whose units normalize
the chain and `y ∈ B^×`. It takes a common splitting basis over `E = F[β]`
for the relative chain and its translate by `y⁻¹`. Extending the values of an
endomorphism on this basis `E`-linearly projects onto the centralizer.
The projection preserves every filtration step of either chain. The
field-linear projection lemma records this at the radical step. Indeed a
basis coordinate of a lattice vector belongs to the same lattice, and
scaling a coordinate by an element of `E^×` shifts its depth by an amount
independent of the vector.

For a simple stratum `[𝔄,n,0,β]` and a defining-sequence choice,
`simpleJ_intertwiningDomain_product` assumes that the underlying set of `J`
is the literal intersection `𝔍(β,𝔄) ∩ U⁰(𝔄)`, the level-zero carrier
in (3.1.14). For `d ∈ J ∩ y⁻¹Jy` this puts both `d` and its conjugate in
the `J` lattice. That lattice is contained in the sum of the relative order
and the radical filtration step. The projection's value on `d` is then
congruent to `d` modulo the radical, for the original chain and the
translated chain. Invertibility modulo the radical yields a relative unit
`u ∈ U(𝔅) ∩ y⁻¹U(𝔅)y` with this value. The difference factor `u⁻¹d`
and its conjugate are both principal units in `J`. The carrier equality
puts them in the `J` lattice, so each belongs to the defining generators
of `J¹`. Thus the difference factor is in `J¹ ∩ y⁻¹J¹y`, and its product
with `u` on the left is `d`.
