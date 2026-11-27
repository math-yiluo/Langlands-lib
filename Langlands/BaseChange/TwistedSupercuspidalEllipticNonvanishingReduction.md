# σ-elliptic nonvanishing for σ-stable supercuspidals from the σ-discrete case

The module `Langlands.BaseChange.TwistedSupercuspidalEllipticNonvanishingReduction` states and
proves that the σ-elliptic nonvanishing of twisted traces of σ-discrete series implies the same
for σ-stable irreducible supercuspidal representations.

## Statement

`TwistedSupercuspidalEllipticNonvanishingFromSigmaDiscreteStatement.{u, v, uW}` is the
implication

`SigmaDiscreteEllipticNonvanishingStatement.{u, v, uW} → TwistedSupercuspidalEllipticNonvanishingStatement.{u, v, uW}`

with the same three universe parameters in the premise and in the conclusion (the field `F`, the
field `E` and the representation space `W`). Both propositions are in the Library:

- `SigmaDiscreteEllipticNonvanishingStatement` (module
  `Langlands.BaseChange.SigmaDiscreteEllipticNonvanishingStatement`): for a nonarchimedean local
  field `F` of characteristic zero, a field `E` that is a cyclic `F`-algebra of group `⟨σ⟩` of
  order `l` with its module topology, and `r : ℕ`, every σ-discrete series representation `τ` of
  `GL_{r+1}(E)` (`IsSigmaDiscreteSeries σ (r + 1) τ`, module `Langlands.BaseChange.PseudoCoefficient`:
  admissible, irreducible, tempered, σ-stable, and not isomorphic to a smooth induction of
  σ-stable smooth data from a proper standard block parabolic subgroup), every isomorphism `A` of
  `τ` onto `τ^σ` and every Haar measure `μ` on `GL_{r+1}(E)` admit a Schwartz–Bruhat function `φ`
  supported in the σ-elliptic set with `tr(τ(φ) ∘ A) ≠ 0`.
- `TwistedSupercuspidalEllipticNonvanishingStatement` (module
  `Langlands.BaseChange.TwistedSupercuspidalEllipticNonvanishingStatement`): the same conclusion
  for every irreducible representation `τ` of `GL_n(E)`, `0 < n`, with
  `GeneralLinear.IsSupercuspidal τ`, every σ-intertwiner `A` and every Haar measure `μ`.

The theorem `twistedSupercuspidalEllipticNonvanishingFromSigmaDiscrete` proves the implication.

## Auxiliary results

- `exists_isSquareIntegrable_realPowerTwist`: over a nonarchimedean local field `E` of
  characteristic zero, an irreducible supercuspidal representation `P` of `GL_n(E)`, `0 < n`, has
  a twist `realPowerTwist ((LocalFieldData.ofInstances E).determinantNorm n) t P`, that is
  `P ⊗ |det|^t` for the residue-normalized absolute value of `E` and some real `t`, that is
  irreducible and square-integrable modulo the centre
  (`JacquetLanglands.IsSquareIntegrable`, module `Langlands.JacquetLanglands.EssentiallySquareIntegrable`).
  The Library theorem `exists_unitary_realPowerTwist` (module
  `Langlands.BaseChange.SigmaOrbitRealTwist`) gives a `t` for which the twist is irreducible,
  supercuspidal and unitarizable. The Library's
  `Classification.unitarizableSupercuspidal_isSquareIntegrable` (module
  `Langlands.Representation.Classification.UnitarySupercuspidalInductionTempered`) makes a
  positive-rank unitarizable supercuspidal square-integrable for the canonical topological data
  of a `p`-adic field. A private lemma transports this to arbitrary topological data along
  `PadicField.TopologicalData.eq_canonicalTopologicalData`. It is applied to the `p`-adic model
  `CharZeroLocalField.topologicalData E` of `E`, whose carrier, topology and valuation are those
  of `E` (module `Langlands.LocalField.CharZeroPadicRealization`). For that model, square
  integrability is `JacquetLanglands.IsSquareIntegrable` by definition.
- `realPowerCharacter_determinantNorm_entrywiseAut`: the character `g ↦ |det g|^t` of `GL_n(E)`
  is invariant under the entrywise action of an `F`-automorphism `σ` of `E`, where `E` carries
  the `F`-module topology. This follows from the Library's `determinantNorm_entrywiseAut` (module
  `Langlands.BaseChange.SigmaInducedIntertwiner`), `|det g^σ| = |det g|`.

## Proof of the implication

Fix `F`, `E`, `σ`, `l`, `n = r + 1`, an irreducible supercuspidal `τ` on `W`, a σ-intertwiner `A`
and a Haar measure `μ` on `GL_{r+1}(E)`.

1. *Local-field structure on `E`.* `E` is finite over `F` (the first component of
   `IsCyclicAlgebra`). With the valuative relation `LocalField.FiniteExtension.valuativeRel F E`,
   `E` with its given module topology is a nonarchimedean local field
   (`LocalField.FiniteExtension.isLocalField_of_isModuleTopology`, module
   `Langlands.LocalField.FiniteExtensionModuleTopology`). It has characteristic zero since
   `F → E` is injective. No topology on `E` or `GL_{r+1}(E)` is changed.
2. *A square-integrable twist.* `exists_isSquareIntegrable_realPowerTwist` gives `t` such that
   `τ' = twist χ τ`, with `χ = |det|^t`, is irreducible and square-integrable. The kernel of
   `χ` is open, since the kernel of `|det|` is open (`LocalFieldData.isOpen_ker_determinantNorm`
   and `isOpen_ker_realPowerCharacter`).
3. *`τ'` is a σ-discrete series.* It is admissible (`IsSquareIntegrable.isAdmissible`) and
   tempered (`isTemperedRep_of_isSquareIntegrable`, module
   `Langlands.BaseChange.PseudoCoefficientExistenceReduction`). By
   `realPowerCharacter_determinantNorm_entrywiseAut`, `χ ∘ σ = χ`, so the Library's
   `twistTwistedIntertwiner` (module `Langlands.BaseChange.TwistedPaleyWiener`) makes the same
   linear map `A` a σ-intertwiner `B` of `τ'`. By the Library theorem
   `squareIntegrableNotInduced` (module `Langlands.BaseChange.SquareIntegrableNotInduced`),
   `τ'` is not isomorphic to a smooth induction of any smooth data, σ-stable or not, from a
   proper standard block parabolic subgroup. This covers the last clause of
   `IsSigmaDiscreteSeries`.
4. *Transfer of the test function.* The premise, applied to `τ'`, `B` and `μ`, gives a
   σ-elliptically supported `φ` with `tr(τ'(φ) ∘ A) ≠ 0`. Put `φ' = characterMultiplyTest χ φ`,
   the function `g ↦ χ(g) φ(g)` (module `Langlands.BaseChange.TwistedCharacter.TwistRegularity`).
   It vanishes wherever `φ` does, so it is σ-elliptically supported. By
   `twistedDistribution_twist_eq_comp` (same module), `tr(τ'(φ) ∘ A) = tr(τ(φ') ∘ A)`, since
   `τ'(φ) = ∫ φ(g) χ(g) τ(g) dμ(g) = τ(φ')`. Hence `tr(τ(φ') ∘ A) ≠ 0`.

## Sources

Arthur–Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the Trace Formula*,
Annals of Math. Studies 120 (1989), Chapter 1. §2.3, printed p. 17, calls a representation of
`G(E)` σ-discrete if it is tempered and σ-stable and cannot be induced from a tempered σ-stable
representation of a standard Levi subgroup. Lemma 2.12 (i), printed p. 19, states that for
σ-discrete `Π` the twisted character `Θ_{Π,σ}` does not vanish identically on the σ-elliptic set.
The Library's `SigmaDiscreteEllipticNonvanishingStatement` is the test-function form of that
lemma.

Henniart–Lemaire, *Changement de base et induction automorphe pour `GL_n` en caractéristique non
nulle*, Mém. SMF 124 (2011), II.5.14, Corollaire 2, printed p. 117, states that every essentially
σ-discrete representation of `G(E)` is σ-elliptic. Its proof begins by replacing `Π` with `Πψ`
for an unramified character `ψ` of `G(E)`, so that `Π` may be assumed to be a σ-discrete series.
The implication proved here is that step, in test-function form, for σ-stable irreducible
supercuspidals. A real power of `|det|` is an unramified character invariant under `σ`, and the
twist of the supercuspidal by a suitable one is square-integrable, hence σ-discrete.
