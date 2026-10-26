# P-adic additive-conductor scaling and integer-ring annihilator

Worker 568 proves the existing
`Langlands.LocalFactors.PadicAdditiveConductorStatement.{u}` as
`Langlands.HarmonicAnalysis.padicAdditiveConductor`. The field universe,
prime, field, supplied topological data, continuous character, and
nontriviality hypotheses are precisely those of the target.

The proof reuses `Langlands.HarmonicAnalysis.Conductor` and the proved
normalization laws in `Langlands.LocalField.Normalization.Proof`. It
introduces no conductor construction. The existing `additiveConductor`
is the greatest integer index of triviality on `additiveLattice`.

The lattice is the actual fractional ideal `π^(-n) O`. Its membership
criterion is converted from division into an existential integral factor.
For nonzero `a`, valuation multiplicativity and
`v(a) = exp(-ord(a))` give
`a*x ∈ L(n) ↔ x ∈ L(n+ord(a))`, including `x=0`.
Multiplication by a field unit is invertible, so triviality of `ψ(a*·)`
on `L(m)` is triviality of `ψ` on `L(m-ord(a))`. Greatest-element
extremality then gives the asserted conductor shift and uniqueness.

For the annihilator, a vector in the conductor lattice stays there after
multiplication by any integer-ring element, so the defining triviality
annihilates every such product. Conversely, for nonzero `y` annihilating
the integer ring, every `x` in `L(-ord(y))` has `y⁻¹*x` integral. The
annihilation assumption therefore forces the character to be trivial on
that entire lattice. Conductor maximality implies
`-ord(y) ≤ additiveConductor`, which is exactly membership of `y`
in the conductor lattice. Zero is handled separately. The fractional-ideal
membership equivalence yields the exact displayed formula.

The source conventions are André Weil, *Basic Number Theory*, second
edition (1973), Chapter II §5, Definition 4 and Proposition 12,
printed pp.41–42 / PDF pp.58–59 (registered source
`weil-1973-basic-number-theory`, SHA256
`32fff78f8ccc5d6378907941e26746c34e20fc3adf5096508844cfe8a301e33b`),
and John Tate, *Number theoretic background* (1979), §3.2.6,
printed p.13 / PDF p.22 (registered source
`tate-1979-number-theoretic-background`, SHA256
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`).
Both cited originals were read for this proof. The scalar shift is the
direct consequence of these conventions and valuation transport explained
above. No Fourier inversion or self-dual measure is used.

The development module compiled without errors or warnings in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). The subsequent Lake build
and theorem inspection succeeded, diagnostic
`c49aabd8-052d-4118-88a3-8e77fd62181c`. The theorem has the single universe
parameter `u`, its type is the existing named proposition with no extra
parameters, and its transitive axioms are only `propext`, `Classical.choice`,
and `Quot.sound`. A private diagnostic also checked direct assignment of the
unapplied theorem to the named target. These are development checks;
independent semantic acceptance, formal exact-target validation, and
publication remain separate requirements.
