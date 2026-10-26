# Principal-unit power cofinality and uniform conductor bounds

The module `Langlands.HarmonicAnalysis.PrincipalUnitPowerCofinalityStatement`
defines the closed proposition
`Langlands.HarmonicAnalysis.PrincipalUnitPowerCofinalityStatement.{uF}`.
Its only project import is `Langlands.HarmonicAnalysis.Conductor`. It is a
statement definition, with no proof of the proposition.

The complete formula is:

```lean
∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  ∀ (b m : ℕ), 0 < m →
    (∃ N : ℕ, ∀ u : F.Carrierˣ, u ∈ T.principalUnits N →
      ∃ v : F.Carrierˣ, v ∈ T.principalUnits b ∧ v ^ m = u) ∧
    (∃ A : ℕ, ∀ χ : Quasicharacter F.Carrier,
      A ≤ T.multiplicativeConductor χ →
      ∃ v : F.Carrierˣ, v ∈ T.principalUnits b ∧ (χ v) ^ m ≠ 1)
```

The telescope includes every prime `p`, with its primality instance, every
finite extension `F` of the specified `Padic p`, and every compatible
topological realization `T`. The carrier universe `uF` is arbitrary.
`PadicField` supplies the field, algebra and finite-dimensional instances.
The local instances in the formula install the topology, valuative relation
and local-field structure already contained in `T`; they are not additional
hypotheses. In particular the character topology and conductor both use this
same `T`.

Write `Uⁿ = T.principalUnits n`. This is the existing subgroup of the actual
field-unit group, defined by
`T.discreteValuation u = 1` and
`T.discreteValuation (u - 1) ≤ WithZero.exp (-(n : ℤ))`.
The published `mem_principalUnits_iff_div_mem_integers` identifies its
congruence condition with `(u - 1)/πⁿ ∈ O_F`.
At level zero, `U⁰` is the full integral-unit group; for positive levels
it is `1 + πⁿ O_F`. Neither this filtration nor the valuation is free input
data.

For each natural level `b` and positive natural power `m`, the first clause
says that some `Uᴺ` is contained in the image of `v ↦ v^m` on `Uᵇ`. The
root `v` is an actual field unit in `Uᵇ`, and its power equals `u` in the
unit group. The conclusion does not require a root for every element of
`Uᵇ`. The indices `b = 0` and `N = 0` are permitted by the formula.

The second clause chooses `A` before quantifying over the character. Thus
`A` may depend on `p`, `F`, `T`, `b` and `m`, but not on `χ`.
`Quasicharacter F.Carrier` is the existing abbreviation for
`ContinuousMonoidHom F.Carrierˣ Complexˣ`, so continuity is bundled in the
character rather than separately assumed. The final inequality is in
`Complexˣ`, with its usual multiplicative power and identity. No unitarity,
finite-order condition, prescribed value on a uniformizer, or restriction
on the unramified part of `χ` is imposed.

All positive `m` occur, including `m = 1` and powers divisible by the
residue characteristic `p`. The zero power is excluded: its image is
only `{1}`, and every zeroth character power is one. No coprimality,
unramified-field, number-field-realization, open-power-image or Hensel
certificate is an input. Establishing power cofinality for these actual
characteristic-zero local fields remains the substantive proof obligation.

## Why the conductor assertion follows

The imported `T.multiplicativeConductor χ` is the least natural unit level
on which `χ` is trivial, including level zero for unramified characters.
The published `T.multiplicativeTrivialAt_iff_conductor_le χ N` identifies
triviality on `Uᴺ` with `T.multiplicativeConductor χ ≤ N`.

Fix an `N` from the first clause and set `A = N + 1`. If
`A ≤ T.multiplicativeConductor χ`, the published
`T.exists_nontrivial_below_multiplicativeConductor χ N` supplies
`u ∈ Uᴺ` with `χ u ≠ 1`. The first clause writes `u = v^m` with `v ∈ Uᵇ`.
The homomorphism law gives `(χ v)^m = χ (v^m) = χ u ≠ 1`, as required.
Equivalently, triviality of `χ^m` on `Uᵇ` would force triviality of `χ` on
`Uᴺ`, contradicting the conductor bound. This explains the mathematical
implication; this module does not implement its Lean proof.

The assertion does not say that raising a character to the `m`th power
preserves its conductor. Such equality need not hold when `p` divides `m`.
It also does not construct a character of conductor at least `A`; that is
the separate unbounded-conductor existence statement.

## Derived provenance and original-source reading

This is a derived local-field prerequisite formulated for Worker 394's
JPSS high-ramification work. It is not an exact transcription of JPSS
Proposition 2.13. In root coordinates
`diag(a₁⋯aᵣ, a₂⋯aᵣ, …, aᵣ)`, the determinant is
`∏ᵢ aᵢ^i`, with indices starting at one. A determinant character therefore
introduces fixed positive character powers. The present bound isolates the
local-field condition needed to keep those powers nontrivial on prescribed
unit subgroups as the original character's conductor grows.

The motivating original is H. Jacquet, I. I. Piatetski-Shapiro and
J. A. Shalika, *Rankin-Selberg Convolutions*, American Journal of Mathematics
105 (1983), 367–464, registered as `jpss-1983-rankin-selberg`, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The retained file is
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`.
Printed page 392 (retained PDF page 27), especially formula (6), displays
the one-variable Mellin factors with positive coordinate weights.
Proposition 2.13 and its proof, printed page 404 (retained PDF page 39),
give sufficiently ramified twist L-factor vanishing and its reduction to
ramified character factors. Both pages were read visually. They motivate
the application; they do not state or prove this exact auxiliary
power-cofinality proposition.

The conductor convention is John Tate, *Number theoretic background*, in
*Automorphic Forms, Representations and L-Functions*, Proceedings of Symposia
in Pure Mathematics 33, Part II (1979), 3–26, section 3.2.6, printed page 13
(retained PDF page 22), registered as
`tate-1979-number-theoretic-background`, SHA256
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
The retained file is
`/home/taskhub/central-library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part II.pdf`.
The original page was read visually. Tate's zero conductor for unramified
characters and least congruence level otherwise agree with the imported
Library conductor. No source-specific errata note for either registered
source was present in the current Library or shared `notes/errata`
locations when this pair was authored.

Worker 615 authored this pair from Worker 394's statement specification and
conductor derivation. No Whittaker expansion, Mellin integration theorem,
L-factor vanishing theorem, or proof of power cofinality is supplied here.
Compilation and proposition inspection are development checks; independent
semantic acceptance and Library publication remain separate requirements.
