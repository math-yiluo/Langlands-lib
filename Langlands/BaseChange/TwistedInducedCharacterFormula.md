# The twisted induced character formula

Module `Langlands.BaseChange.TwistedInducedCharacterFormula`.

`twistedInducedCharacterFormula : TwistedInducedCharacterFormulaStatement` proves the Library
statement of the twisted case of Henniart–Lemaire, Mém. SMF 124 (2011), II.4.5 (3). Let `E/F` be
a cyclic algebra of group `⟨σ⟩` over nonarchimedean local fields, `π_1, …, π_r` irreducible
admissible representations of the blocks `GL_{n_i}(E)` with σ-intertwiners `A_i`, and `δ ∈ GL_n(E)`
norm-associated with a regular semisimple `γ ∈ GL_n(F)`. Let `m` be a Levi class system for `γ`
and `d j ∈ M(E)` σ-conjugates of `δ` whose blocks have exact cyclic norms the blocks of `m j`. If
`b j` is the twisted character value at `d j` of the Levi tensor representation for
`A_1 ⊗ ⋯ ⊗ A_r`, then the twisted character of the normalized product induction for the induced
intertwiner `ι(A)` has value `Σ_j |D_{G/M}(m_j)|_F^{-1/2} b j` at `δ`
(`relativeDiscriminantWeight`).

## Proof

The theorem is `twistedInducedCharacterFormula_of_localDescent TwistedLocalDescent.twistedLocalDescent`:

- `twistedInducedCharacterFormula_of_localDescent`
  (`Langlands.BaseChange.TwistedInducedCharacterFormulaFromLocalDescent`) derives the target from
  `TwistedLocalDescentStatement`, using the reduction `twistedInducedCharacterFormulaReduction`
  and the twisted van Dijk formula `TwistedVanDijk.twistedVanDijk` (II.4.5 (2));
- `TwistedLocalDescent.twistedLocalDescent` (`Langlands.BaseChange.TwistedLocalDescent.Proof`)
  proves the local descent of the twisted constant term: near `δ`, the twisted constant term of a
  test function `φ` splits into pieces supported near the twisted classes of the `d j`, of
  integrals `|D_{G/M,σ}(d j)|^{-1/2} ∫ φ`. The pieces are restrictions of the Library's
  normalized twisted constant term `normalizedTwistedParabolicConstantTerm` to disjoint open
  twisted saturations.
