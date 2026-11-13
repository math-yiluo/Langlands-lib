# Essentially square-integrable representations of `GL_n(F)`

The local Jacquet–Langlands correspondence is a bijection between the
classes of irreducible essentially square-integrable representations
of `GL_n(F)` and the classes of irreducible smooth representations of
`D^×`. This module defines essential square-integrability for
representations of `GL_n(F)` over a general nonarchimedean local field
`F` (the Mathlib class `IsNonarchimedeanLocalField F`), of any
characteristic.

## Sources

- Deligne–Kazhdan–Vignéras 1984 (*Représentations des algèbres
  centrales simples p-adiques*, introduction, printed p. 34, PDF page
  38 of the registered readable original) write `E(G)` for the classes
  of irreducible admissible representations. A superscript `2` adds
  the condition "de carré intégrable", and the main theorem is a
  bijection between `E²(G')` and `E²(G)`. In DKV a square-integrable
  representation has a unitary central character and matrix
  coefficients that are square-integrable modulo the centre.
- Badulescu 2002 (`math0201117.tex`, lines 190–193 and 2780–2782)
  writes `E²(G)` for the equivalence classes of essentially
  square-integrable representations (macro `\ecis`, line 34:
  "représentations essentiellement de carré intégrable") and states
  the correspondence for them (Théorème 1.1, lines 195–203). A
  representation is essentially square-integrable when it is the twist
  of a square-integrable one by a character. On `GL_n(F)` every
  character is `χ ∘ det`, and up to a unitary character, which does
  not affect square-integrability, it is `|det|^s` with `s` real. That
  is the form used below. Badulescu's `E²` classes are irreducible;
  irreducibility is not part of the predicates here and is imposed
  separately where the correspondence is stated.

The Library has the same definitions for the p-adic fields
`PadicField p` with chosen topological data
(`Langlands.PadicField.TopologicalData.IsSquareIntegrable` and
`.IsEssentiallySquareIntegrable` in
`Langlands/Representation/Classification/Tempered.lean`). Those are
restricted to characteristic zero. Badulescu's correspondence is in
positive characteristic as well, so this module gives the same
definitions for every nonarchimedean local field, with the field's own
topology.

## Definitions

Let `F` be a nonarchimedean local field and `n` a natural number.
`GL_n(F)` is the Library's `GeneralLinear n F` with the topology
induced from matrices.

- `determinantNorm F n : GeneralLinear n F →* ℝ≥0ˣ` is
  `g ↦ |det g|`, the composite of the Library's
  `GeneralLinear.determinant` with `Plancherel.fieldNormUnits F`, the
  residue-normalized absolute value `|x| = q^{-v(x)}` on `F^×`
  (`determinantNorm_coe` states it in terms of
  `LocalField.residueNormalizedAbsoluteValue`).
  `determinantNorm_isLocallyConstant` and
  `isOpen_determinantNorm_ker` prove that it is locally constant with
  open kernel, from the Library's
  `Plancherel.fieldNormUnits_isLocallyConstant` and the continuity of
  the determinant.

- `centralQuotientMeasurableSpace F n` is the Borel σ-algebra on the
  quotient `GL_n(F) / Z` of `GL_n(F)` by its centre (with the quotient
  topology), and `centralQuotientBorelSpace F n` records that it is
  Borel. `exists_isHaarMeasure_centralQuotient` proves that this
  quotient carries a Haar measure (it is locally compact, by
  `generalLinear_locallyCompactSpace`), so the predicates below, which
  quantify over all Haar measures, are not vacuous for that reason.

- `IsSquareIntegrable ρ`, for `ρ : Representation ℂ (GeneralLinear n F) V`,
  holds when for every Haar measure `μ` on `GL_n(F) / Z` (with the Borel
  σ-algebra) the Library predicate `IsSquareIntegrableModCenter ρ μ`
  holds: `ρ` is admissible, it has a smooth unitary central character
  (a `UnitaryCentralCharacter ρ`), and for every smooth dual vector `ℓ`
  and every vector `v` the function `gZ ↦ |ℓ(ρ(g) v)|` on `GL_n(F) / Z`
  is in `L²(μ)`. Two Haar measures differ by a positive constant, which
  does not change `L²`-membership, so quantifying over all of them
  agrees with DKV's single fixed Haar measure.

- `IsEssentiallySquareIntegrable ρ` holds when there is a real `s` such
  that `realPowerTwist (determinantNorm F n) (-s) ρ`, the representation
  `g ↦ |det g|^{-s} ρ(g)` on the same space, is square-integrable. Then
  `ρ = |det|^s ⊗ ρ₀` with `ρ₀` square-integrable.

## Properties

- `IsSquareIntegrable.isAdmissible` and
  `IsEssentiallySquareIntegrable.isAdmissible`: such representations
  are admissible. For the second, the twist by `|det|^s` preserves
  admissibility (the Library's `isAdmissible_twist_iff`, using that
  `|det|^s` has open kernel) and undoes the twist by `|det|^{-s}`
  (`realPowerTwist_cancel_neg`).
- `isSquareIntegrable_iff_of_equiv` and
  `isEssentiallySquareIntegrable_iff_of_equiv`: both predicates are
  invariant under equivalence of representations (from the Library's
  `isSquareIntegrableModCenter_iff_of_equiv` and
  `realPowerTwistEquiv`).
- `IsSquareIntegrable.isEssentiallySquareIntegrable`: take `s = 0`.
- `IsEssentiallySquareIntegrable.realPowerTwist`: twisting by
  `|det|^t` preserves essential square-integrability (`s` becomes
  `s + t`).

## Rank one

- `mem_center_generalLinear_one` and `subsingleton_centralQuotient_one`:
  `GL_1(F)` is commutative, so `GL_1(F) / Z` is a point.
- `isSquareIntegrable_trivial_one`: the trivial representation of
  `GL_1(F)` on `ℂ` is square-integrable. It is smooth and
  finite-dimensional, hence admissible; the trivial character of the
  centre is a unitary central character; and every absolute matrix
  coefficient is a constant on a one-point space, which is in `L²` for
  the finite measure `μ`.
- `isEssentiallySquareIntegrable_trivial_one`: hence it is essentially
  square-integrable. This shows that the predicates hold for concrete
  data.
