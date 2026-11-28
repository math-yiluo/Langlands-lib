# Trace characters of the shifted lower-corner quotient

Let `L` be a lattice chain over a nonarchimedean local field, and let `ψ` be a
BK additive character (trivial on the maximal ideal and nontrivial on the
valuation ring). Write `P^i` for the ambient endomorphism filtration, `D`
for the trace dual with respect to `ψ`, and `a_β(y) = βy − yβ`.
For integral endomorphisms `e₁, e₂` and `ζ' ∈ P^(-1)`, set
`s(x) = e₂ x e₁ ζ'`. Let `I, T, X` be submodules over the valuation ring,
with `a_β(I) ⊆ D(X)`. The family `lowerCornerTracePairing` sends `y ∈ I`
to the character of `T / s⁻¹(X)` given by `[x] ↦ ψ(tr(a_β(y) s(x)))`.

`lowerCornerTracePairing_upper_mk` uses commutation of `β` with
`e₁, e₂, ζ'` and cyclicity of trace to express this value as
`ψ(tr(a_β(e₁ ζ' y e₂) x))`. If `X ⊆ P^m`, `T ⊆ P^(m+1)` and
`D(X) = a_β(I) + P^(1−m)`, `LowerCornerTracePairingStatement` asserts
that these characters separate the points of the quotient.
`lowerCornerTracePairingSeparation` proves this by showing that a
representative of a point annihilated by the family has `s(x)` in both
`D(a_β(I))` and `D(P^(1−m))`. The second containment follows from
`s(x) ∈ P^m`. The sum formula and double trace duality give `s(x) ∈ X`.

This is a derived version of the trace-duality step in the character
comparison of Bushnell–Kutzko (8.2.26), printed pp. 288–289 (PDF pp.
300–301). It takes the dual formula as a hypothesis, as supplied for the
H lattice by (3.1.19) and for the J lattice below the cutoff by (3.1.21),
printed pp. 96–97 (PDF pp. 108–109). The source
`bushnell-kutzko-1993-admissible-dual-gln` has SHA-256
`811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.
