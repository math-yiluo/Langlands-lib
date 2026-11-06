# P-adic Fourier normalization

Worker 1786 proves
`Langlands.LocalFactors.padicFourierNormalization` of exactly the existing
`Langlands.LocalFactors.PadicFourierNormalizationStatement.{u}` in
`Langlands.LocalFactor.Harmonic.Statement`. The theorem retains the arbitrary
prime, carrier universe, p-adic field, supplied topology, continuous nontrivial
circle-valued character, conductor witness, and all Haar measures in that
statement. There are no additional hypotheses.

## Provenance and conventions

This is a proof of the existing source-backed proposition. Its original-source
correspondence is recorded in
[`Statement.md`](Statement.md): Weil, *Basic Number Theory*, Chapter VII
Section 2, Proposition 2 and Corollaries 1–3, especially printed page 108;
Tate, *Number theoretic background*, Sections 3.2 and 3.6; and Deligne,
*Les constantes des equations fonctionnelles des fonctions L*, Sections
3.3–3.4. This proof uses the Library's lattice Fourier and volume theorems,
additive-conductor theorem, and dual-measure existence theorem. The private
helpers are internal deductions for this proof.

The Fourier transform is the actual Mathlib
`Fourier.fourierIntegral ψ⁻¹`, which has integrand `ψ(x*y) f(x)`.
All measures use the Borel measurable space of the supplied topology.
Write `O` for its actual valuation integer ring, `q` for its residue
cardinality, and `n` for the greatest exponent with character trivial on
`π^(-n) O`. The final proof identifies the statement's range presentation
of `O` with the integer-ring set and identifies its conductor witness with
`T.additiveConductor`.

## Implemented proof

The open, compact integer ring has finite strictly positive Haar mass.
Mathlib's Haar proportionality theorem expresses any two additive Haar
measures as a nonnegative scalar multiple of each other. Evaluating this
identity on `O`, whose mass is positive, proves that equal real integer-ring
volumes imply equal measures.

The published `padicLatticeFourier` gives the transform of a lattice
indicator as its Haar volume times the indicator of the conductor
annihilator lattice. Specializing to `O` gives
`FT(1_O) = μ(O) 1_(π^(-n) O)`. If `ν` is dual to `μ`, apply the raw
double-transform identity to `1_O` at zero. The characteristic function
is locally constant and compactly supported. The second lattice transform,
combined with `padicLatticeHaar`, yields
`μ(O) ν(O) = q^(-n)`.

Conversely, the published `padicFourierDuality` supplies a dual Haar measure
`ρ` for the fixed `μ`. The necessary volume identity forces `ν(O)=ρ(O)`;
Haar uniqueness from equal integer-ring volumes gives `ν=ρ`. This proves
the full equivalence for arbitrary Haar measures using the raw inversion
predicate of the target.

For self-duality the criterion becomes `μ(O)^2=q^(-n)`.
The positive number `q^(-n/2)` has this square by the real-power addition
law. Positivity of both quantities selects the unique nonnegative root.
Finiteness of `μ(O)` then converts the real equality to the required
extended-nonnegative measure equality.

Membership in `π^(-n) O` is equivalent to `π^n y ∈ O`, giving the
statement's exact uniformizer form of the indicator transform. If `σ`
is self-dual, its volume is `q^(-n/2)`. The positive multiple
`q^(n/2) μ(O) • σ` has the same integer-ring volume as `μ`, so the
same Haar uniqueness argument proves the corrected fixed-Haar ratio.
The exponent in this ratio is positive, as in the existing target's
correction to the sentence following Tate's equation (3.6.2).

Finally, for a unit `a`, the character `ψ(a*x)` is continuous and
nontrivial and its conductor is `n+ord(a)` by
`padicAdditiveConductor`. Multiplying a Haar measure by
`sqrt(T.normalizedAbs a)` preserves the Haar predicate. Its squared
integer-ring volume is `|a| q^(-n)=q^(-(n+ord(a)))`, since
`|a|=q^(-ord(a))`. The already proved dual-volume criterion therefore
gives the exact raw self-duality conclusion for the scaled character.

## Verification boundary

The module compiles with no warnings in the task's prepared Lean environment.
Inspection of `padicFourierNormalization` reports the single universe
parameter `u` and only `propext`, `Classical.choice`, and `Quot.sound`
among its axioms. Development compilation is separate from independent
semantic review and the submission's exact-target validation.
