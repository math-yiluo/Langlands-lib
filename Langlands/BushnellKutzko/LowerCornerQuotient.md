# Finite quotient by the shifted lower corner

For a simple stratum with lower index zero and a chosen defining sequence, let
`m ≥ 1`. Take complementary idempotents `e₁`, `e₂` in the integral centralizer
order and `ζ' ∈ 𝔔⁻¹`. Let `X` be an integral submodule of the endomorphism
algebra containing `𝔥ᵐ` and put

`Y = 𝔥ᵐ⁺¹ / {x ∈ 𝔥ᵐ⁺¹ | e₂ x e₁ ζ' ∈ X}`.

`SplitBlocks.lowerCornerQuotientProperties` proves
`SplitBlocks.LowerCornerQuotientStatement`. Let `K` be the subgroup of `Hᵐ`
whose lower corner lies in `𝔓ᵐ⁺¹`. Then `Y` is finite and the map sending `k`
to the class of `e₂(k − 1)e₁` surjects from `K` onto the multiplicative copy of
`Y`. Its kernel is exactly the condition `e₂(k − 1)e₁ ζ' ∈ X`.

The integral centralizer action places `e₂(k − 1)e₁` in `𝔥ᵐ⁺¹`. The product
bound (8.2.13) places the shifted quadratic term in `𝔥ᵐ`, so lower-corner
projection becomes a homomorphism on the quotient. The units `1 + e₂ x e₁`
give surjectivity, and the lower ambient bound on `𝔥ᵐ` yields finiteness by
comparison with a finite filtration quotient.

The construction uses the lower-corner method of Bushnell–Kutzko,
*The admissible dual of GL(N) via compact open subgroups* (1993).
In the proof of (8.2.26), the full depth-\(m\) group \(H^m\) gives the
lower-corner lattice quotient
\(\mathfrak h^m_{21}/((\mathfrak Q^m)_{21}+\mathfrak h^m_{21}\zeta_1)\),
where \(\zeta_1\) is the first block of the shift. The condition on the
lower corner of \(K\) puts the representatives in \(\mathfrak h^{m+1}\),
and the supplied \(X\) sets the kernel by the shifted membership test.
See (8.2.9), (8.2.12)–(8.2.13) and the proof of (8.2.26), printed
pp. 278–280 and 288–289.
