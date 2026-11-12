# Witnessed generators from weakly associated unitary representations

Author: Worker 5134. Module `Langlands.Global.Arithmetic.HenniartWitnessedGenerator`
(namespace `Langlands.VirtualRepresentation.RelativeGlobal`). It is a helper for the
reduction `HenniartGlobalizationReductionStatement`
(`Langlands.Global.Arithmetic.HenniartGlobalizationReduction`) of
`HenniartGlobalizationStatement` (Henniart 2000, §§3.3–3.7). It contains no definitions.

Notation: `E/F` is a Galois extension of number fields with compact adele quotient,
`c` a fundamental-class family, `W_{E/F} = RelativeWeilGroup c F E`, `v` a finite place
of `F`, and `W_{F_v}` the local Weil group of `padicField v`. A `WitnessedGenerator F E c v`
(Library, `VirtualRepresentation/Global/RelativeImages.lean`) bundles an irreducible
unitary representation of `W_{E/F}`, a cuspidal realization with a spectral presentation
weakly associated with it, a local map at `v`, irreducibility and admissibility of the
local component at `v`, and a local unitary element `weilElement`.

## Results

- `isWeaklyAssociated_of_isWeaklyAssociatedClass S T hS Q`: if `S` is weakly associated
  with the isomorphism class of the cuspidal realization `T`, then `S` is weakly
  associated with the spectral system of every presentation `Q` of `T`. Proof: the class
  statement gives one presentation `P` with `S` weakly associated to `P`. The Library
  lemma `sameEulerPolynomials_scale_of_isDeterminantMultiple`, applied to `T` and the
  reflexive determinant-multiple relation, shows that `P` and `Q` have the same Euler
  polynomials after scaling by the trivial Hecke character. Scaling by `1` is the
  identity (`SpectralSystem.scale_one`). Weak association transfers along equal Euler
  polynomials (`IsWeaklyAssociated.of_sameEulerPolynomials`).

- `exists_witnessedGenerator_realizeExact hcalip hacc hasi hc v S hirr hu π hπ w rec ι hι`:
  let `S` be an irreducible unitary representation of `W_{E/F}`, weakly associated with
  a cuspidal class `π`, and let `ι : W_{F_v} → W_{E/F}` be a local relative Weil map for
  a place `w` above `v` and a reciprocity candidate `rec`. Then `S` is continuous and
  some witnessed generator `d` at `v` satisfies
  `realizeExact (includeUnitary d.weilElement) = localExactClass F E c v S hS ι`, the
  class of the restriction of `S` along `ι`. The hypotheses are three published
  propositions: `CuspidalAllLocalIrreduciblePresentationExistenceStatement` (a
  presentation irreducible and admissible at every finite place),
  `AssociatedCentralCharacterStatement` (Henniart 2000, §2.2) and
  `AssociatedSupercuspidalInductionStatement` (Henniart 2000, Théorème 2.4).
  Proof: choose a representative `T` of `π` and a presentation `Q` irreducible at every
  place. Lift `Q` to universe `uP` (`CuspidalSpectralPresentation.universeLift`, which
  keeps the spectral system and local irreducibility and admissibility). The first
  result gives weak association. `hasUnitaryCentralCharacter_of_associatedCentralCharacter`
  gives a unitary central character. `hasi` then gives the supercuspidal induction data
  `B, σ, e`. `WitnessedGenerator.ofUnitaryInduction` builds `d`, and
  `localUnitaryExpansion_spec` gives the equation.

- `exists_unitaryNormPower_uniformizerUnit v z hz`: for every `z ∈ ℂˣ` with `|z| = 1`
  there is `t ∈ ℝ` such that the `v`-component of the Hecke character
  `unitaryNormPower F t = |·|^{it}` takes the value `z` at the canonical uniformizer
  `ϖ` of `F_v`. Proof: `0 < ‖ϖ‖ < 1` (its valuation is `exp(-1)`), so `log ‖ϖ‖ ≠ 0`.
  Take `t := arg z / log ‖ϖ‖`. Then `‖ϖ‖^{it} = exp(i · arg z) = z`.

- `exists_witnessedGenerator_unramifiedTwist htransfer hc d z hz`: assume
  `LocalTransferReciprocityStatement` (Tate 1979, (1.6.1)). For a witnessed generator
  `d` at `v` and `|z| = 1`, some witnessed generator `d'` at `v` has Weil element the
  twist of that of `d` by the unramified character `localUnramifiedCharacter (padicField v) z`
  of `W_{F_v}`. Proof: take `t` from the previous result and `Ω := |·|^{it}`. Let `e` be
  the geometric Weil reciprocity candidate of `F_v` (published
  `geometricWeilReciprocityExistenceUniqueness`). `WitnessedGenerator.exists_heckeTwist`
  (with the published `cuspidalDeterminantMultiple` and
  `presentedDeterminantMultipleAssociation`) gives `d'` whose Weil element is the twist
  of `d.weilElement` by `weilCharacter e μ`, where `μ` is the local component of `Ω`.
  `μ` is unramified (`isUnramifiedCharacter_quasicharacterAt`) with value `z` at `ϖ`, so
  `Correspondence.weilCharacter_eq_localUnramifiedCharacter` identifies `weilCharacter e μ`
  with `localUnramifiedCharacter z`. `Weil.ExactExpansion.unitaryTwist` moves the twist
  through `realizeExact`.

## Provenance

Internal helpers for Henniart (2000), §3.4. There Henniart passes from a representation
weakly associated with a cuspidal automorphic representation to elements of the relative
Weil image at `v`, using Théorème 2.4 and the central character identity of §2.2. He also
removes unramified twists by twisting with Hecke characters `|·|^{it}`. The modules
follow that route with the Library's witnessed generators. No new mathematical object is
defined.
