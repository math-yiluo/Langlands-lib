# The induction step of mirabolic twisted pairing rigidity

Author: Worker 806.

This module proves conditional results only. Its main theorem,
`Langlands.Whittaker.MirabolicRigidity.mirabolicTwistedPairingRigidity_of_phiMinus`,
derives `MirabolicTwistedPairingRigidityStatement F T n` for every `n` from the
following hypotheses, each supplied for every rank:

- `Derivative.Mirabolic.PhiMinusIrreducibleStatement` (H1): unnormalized `Φ⁻` of an
  irreducible smooth representation is irreducible or zero;
- `Derivative.Mirabolic.PhiMinusPairingTransferStatement` (H2): a nonzero pairing of a
  radical-generated `ξ` with `ξ'` at exponent `s` gives a nonzero pairing of `Φ⁻ ξ`
  with `Φ⁻ ξ'` at exponent `s − 1`;
- `MirabolicFunctionalMultiplicityStatement` (FM), in both carrier universes.

## Route

This follows the induction in Jacquet–Piatetski-Shapiro–Shalika (1983), §1.5,
Corollary 2 (printed p.384), and in the Proposition of §1.4 (printed pp.380–381). The
Lean proof keeps the unnormalized `Φ⁻`. It uses Whittaker functionals and the
functional multiplicity statement to recognise the compact model, instead of the
Bernstein–Zelevinsky equivalence `Φ⁺Φ⁻ ≅ id`.

The induction is on `n`. The module `MirabolicPairingRigidityElementary` reduces each
rank to its radical-generated case `RadicalGeneratedPairingRigidity`, through
`mirabolicTwistedPairingRigidity_of_radicalGenerated`.

- **Rank one (`n = 0`).** The radical-generated case holds with `E = ∅`, since every
  irreducible representation is equivalent to the compact model (`rankOne_equiv`).
- **Step (`radicalGeneratedPairingRigidity_succ`).** Let `ξ`, `ξ'` be irreducible
  representations of `mirabolic (m + 1) F`, with `ξ` radical-generated. Put
  `X = Φ⁻ ξ` and `Y = Φ⁻ ξ'`.
  - If `X` or `Y` is zero, H2 turns any nonzero pairing into a nonzero pairing on a
    zero representation, which is impossible. So `E = ∅` works.
  - Otherwise H1 makes `X` and `Y` irreducible (`isIrreducible_of_dichotomy`). Rigidity
    in rank `m` gives a finite set `E` for `X`, `Y`. Put
    `E' = {z / q | z ∈ E}`, where `q` is the residue cardinality. Suppose
    `q^(-s) ∉ E'`. Then `q^(-(s-1)) = q · q^(-s) ∉ E` (`spectralPoint_sub_one`). A
    nonzero pairing of `ξ`, `ξ'` at `s` gives, by H2, a nonzero pairing of `X`, `Y`
    at `s − 1`. So `X` and `Y` are equivalent to the compact model in rank `m`.
    `nonempty_equiv_of_phiMinus` lifts this to `ξ` and `ξ'`.
- **Recognition (`nonempty_equiv_of_phiMinus`).** Suppose `Φ⁻ ξ` is irreducible and
  equivalent to the compact model in rank `m`. Part 2 of FM in rank `m` gives a
  nonzero Whittaker functional `ℓ` on `Φ⁻ ξ`.
  `exists_functional_ne_zero_of_phiMinus` turns it into the nonzero Whittaker
  functional `ℓ ∘ q` on `ξ`, where `q` is the `Φ⁻` quotient map. This works because
  every upper unipotent `n` of rank `m + 1` factors as `u(c) · successor n₀`
  (`upperUnipotent_eq_radicalElement_mul_successor`), and the standard character
  factors to match (`mirabolicCharacter_succ`). Parts 1 and 2 of FM in rank `m + 1`
  then make the Whittaker functionals on `ξ` a line, so `ξ` is equivalent to the
  compact model.

## Auxiliary declarations

- `spectralPoint_sub_one`: `q^(-(s-1)) = q · q^(-s)`.
- `forms_eq_zero_of_bot_eq_top_left`, `forms_eq_zero_of_bot_eq_top_right`: a form on a
  zero representation vanishes.
- `nonempty_linearEquiv_of_multiples`: a complex vector space with a nonzero vector of
  which every vector is a multiple is isomorphic to `ℂ`.
- `upperUnipotent_mem_plusSubgroup`, `plusProjection_mem_upperUnipotent`,
  `upperUnipotentBlock`: the upper-left block of an upper unipotent matrix.
