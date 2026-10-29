# JPSS finite-spectral-exception mirabolic pairing rigidity

Author: Worker 806.

This module proves `Langlands.Whittaker.mirabolicTwistedPairingRigidity`, whose type
is exactly `MirabolicTwistedPairingRigidityStatement.{uF,uV,uW} F T n` from
`Langlands.Representation.Whittaker.MirabolicPairingStatement`. The theorem holds for
every prime `p`, every `F : PadicField.{uF} p`, every `T : F.TopologicalData` and every
`n`, rank one included, and keeps the three universes independent.

## Statement

Fix a unitary additive character `ψ`. Let `ξ` and `ξ'` be smooth irreducible
complex representations of the actual `mirabolic n F` on independent carriers. There is
one finite set `E : Finset ℂ`, chosen before the exponent and the form, such that the
following holds for every `s : ℂ` with `spectralPoint T.residueCardinality s ∉ E`
(that is, `q^(-s) ∉ E`). A nonzero element of `InvariantBilinear.forms ξ ξ'` at
covariance `g ↦ |det g|^(-s)` forces both `ξ` and `ξ'` to be equivalent to
`mirabolicCompactInduced ψ n`. The exceptional set is finite in `q^(-s)`, not in `s`.
The statement has no admissibility, finite-dimensionality, classification or
central-character hypothesis.

## Proof

The theorem applies
`MirabolicRigidity.mirabolicTwistedPairingRigidity_of_phiMinus` from the helper
module `Langlands.Representation.Whittaker.MirabolicPairingRigidityStep`. That theorem
derives the statement in every rank from three inputs, each required in every rank.
This module supplies them from published proofs:

- `Derivative.Mirabolic.phiMinusIrreducible`, the published proof of
  `PhiMinusIrreducibleStatement`, used in both carrier universes `uV` and `uW`.
  The unnormalized Bernstein–Zelevinsky `Φ⁻` of an irreducible smooth representation
  is irreducible or zero.
- `Derivative.Mirabolic.phiMinusPairingTransfer`, the published proof of
  `PhiMinusPairingTransferStatement`. A nonzero pairing of a radical-generated `ξ`
  with `ξ'` at exponent `s` gives a nonzero pairing of `Φ⁻ ξ` with `Φ⁻ ξ'` at
  exponent `s − 1`.
- `mirabolicFunctionalMultiplicity`, the published proof of
  `MirabolicFunctionalMultiplicityStatement`, used in both carrier universes.

The induction on `n` is documented in the helper module's Markdown. In outline:
`MirabolicPairingRigidityElementary` reduces each rank to its radical-generated case.
In rank one every irreducible representation is the compact model, so `E = ∅`.
In the step from rank `m + 1` to rank `m + 2`, the step applies rigidity in rank
`m + 1` to `Φ⁻ ξ` and `Φ⁻ ξ'`, which are irreducible by the first input, and takes
`E' = {z / q | z ∈ E}`. If `q^(-s) ∉ E'` then `q^(-(s-1)) ∉ E`, so the transferred
pairing makes `Φ⁻ ξ` and `Φ⁻ ξ'` compact models. Functional multiplicity in ranks
`m + 1` and `m + 2` lifts this to `ξ` and `ξ'` through the Whittaker functional
`ℓ ∘ q`. If either `Φ⁻` is zero, the transferred pairing is impossible and `E = ∅`.

## Sources

Jacquet, Piatetski-Shapiro and Shalika (1983), Proposition 1.4 (printed p.380) and
§1.5, Corollary 2 (printed p.384); registered as `jpss-1983-rankin-selberg`. The
original route classifies representations by their index (the rank of the highest
nonzero derivative) and transfers pairings between inducing data. The Lean proof
keeps the induction on the rank through `Φ⁻`. It recognizes the compact model through
Whittaker functionals and functional multiplicity, not through classification by
index or the Bernstein–Zelevinsky equivalence `Φ⁺Φ⁻ ≅ id` (BZ 1976, registered as
`bernstein-zelevinsky-1976-representations-gln`, §5). The spectral bookkeeping
`q^(-(s-1)) = q · q^(-s)` gives the finite exceptional set in `q^(-s)` that JPSS
state.
