# Whittaker pairing normalization

This derived prerequisite encodes the integral equation in Lemma 1.1 of
Shahidi, *Fourier transforms of intertwining operators and Plancherel measures
for GL(n)* (1984), printed pages 73–74. Its role in the coupled measure
normalization is described in item 1 on printed page 75. The original is
registered as `shahidi-1984-fourier`, SHA256
`a10d5c605d94d4e85d0e5f453d6a8c233d91e3cb60d538f430d8ad900cbb6b29`.

For an actual representation π of GL_(n+1)(F), an invariant positive definite
Hermitian form b, and the standard character χ of the actual upper-unipotent
subgroup N, `whittakerPairingIntegrand ψ n π b v w u` is

    b.inner (π(u) w) v · χ(u).

Shahidi's pairing is linear in the first argument and conjugate-linear in the
second. The Library's `InvariantPositiveForm.inner` uses the opposite
convention, so the arguments are reversed. The multiplier is χ(u), without
conjugation or inversion. The supplied Whittaker functional ℓ belongs to
`glFunctionals ψ n π`, so ℓ(π(u)v) = χ(u)ℓ(v) for the same character.

`IsWhittakerPairingNormalized ψ n π b ℓ dn` requires, for every v,w, that this
complex-valued kernel be integrable with respect to the supplied measure dn
on N and that

    ∫ u, b.inner (π(u) w) v · χ(u) dn = ℓ(v) · conjugate(ℓ(w)).

This is ordinary scalar Bochner integration and imposes no topology, norm or
completion on the algebraic representation space. Integrability is explicit,
so the equation does not obtain a spurious value from Lean's total integral
when a function is not integrable. No measure or form is chosen.

The implemented intrinsic identities check the value at the identity and
linearity in v and conjugate-linearity in w, including additivity. Their proofs
use the representation's linear action, the form's conjugate symmetry,
additivity and scalar law, and the character's identity value. The relation
has projection lemmas for integrability and its integral equation. Finally,
`IsWhittakerPairingNormalized.measure_ne_zero` proves that a nonzero ℓ
excludes dn = 0: the diagonal integral would force ℓ(v) conjugate(ℓ(v)) = 0
for every v and hence ℓ = 0.

The definition is meaningful over any field with a topology and a supplied
measurable structure on N. It does not assert existence in that generality.
In the cited passage π is irreducible admissible generic, unitary and
supercuspidal over a non-archimedean local field, ℓ is nonzero, and dn is Haar.
The source proves that a suitable pairing exists under those hypotheses;
this unit only defines the explicit relation for a supplied pairing and
measure. Haar invariance and regularity, the decomposition dn = dn₁ dn₂,
the Proposition 1.2 quotient measure, and the complete suitable-measure
system remain separate obligations. In particular no quotient integrand
is defined here, so this unit does not resolve the primed-unipotent notation
issue in Proposition 1.2.
