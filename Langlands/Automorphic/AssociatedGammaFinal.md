# Assembly of the associated gamma comparison

Supporting module for the proof of `AssociatedGammaStatement` (module `Langlands.Automorphic.AssociatedGammaFinal`). It derives
`AssociatedGammaStatement` (Henniart 2000, Théorème 2.3; Henniart 1986, Theorem 4.1) from two
statements taken as hypotheses (see `associatedGamma_of_inputs` below), by assembling the inputs
of the two-twist comparison engine. Every declaration compiles, and `associatedGamma_of_inputs`
uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Results

- `localPairClass_twist_of_trivial`: twisting by a character of `W_{E/F}` that is trivial along
  the local map `ι` leaves the local pair class unchanged. The identity map is an equivalence of
  the local components.
- `reciprocityCharacter_one_apply`, `quasicharacterBase_one`: the trivial Hecke character gives
  trivial characters.
- `hasHeckeGammaCertificate_setups`: given an automorphic setup `D`, an arithmetic setup `A` with
  the same finite additive components, weak associations of `S`, `S'`, `S^∨`, `S'^∨` with the
  spectral systems of `D`, and central characters `ω`, `ω'` with `det S = ω ∘ τ`,
  `det S' = ω' ∘ τ`, there is a gamma certificate (`HasHeckeGammaCertificate`) at every finite
  place `v` for the data of the setups at `v`. The bad set is `{v} ∪ W₁ ∪ W₂`, where outside
  `W₁`, `W₂` the representations match the spectral systems. The engine inputs come from:
  - `commonTwistEulerInputs_families` (global functional equations);
  - `infinityGammaPreservation_families` and `finiteGammaPreservation_families`;
  - `ramifiedGammaStability_families` (stable comparison);
  - `outsideGammaStability_families` (principal-series comparison).

  The gamma factors `G` and `H` at `v` are those of the untwisted families (`χ = 1`). The
  twisted local data of the trivial character are the untwisted ones, by
  `isCharacterTwist_one` and `localPairClass_twist_of_trivial`.
- `isCanonicalFiniteAdditiveComponent_unique`: the finite component of `ψ` at `v` is unique.
- `exists_localWeilData`: at every finite place there are a place `w` of `E` above it, a
  geometric reciprocity candidate of `E_w` (`geometricWeilReciprocityExistenceUniqueness`) and a
  local-to-relative Weil map (`localRelativeWeilMapExistence`, using `IsArithmeticClassFamily`).
- `exists_localSystem`: a normalized reciprocity family (`commonClosureReciprocityExistence`)
  and a local-constant system (`NonabelianSystem.exists_system`) exist over every p-adic field.
- `associatedGamma_of_inputs`: `AssociatedGammaStatement` follows from two hypotheses, the
  completed global Rankin–Selberg equation `CuspidalPairGlobalFunctionalEquationStatement.{u, u}`
  and the stable local comparison
  `StableTwistPairGammaMatchStatement.{u, uV, uE}` (proved in the Library as
  `stableTwistPairGammaMatchStatement`). Every
  other input is a proved Library theorem:
  - `principalSeriesPairGammaMatchStatement` (principal-series comparison);
  - `Correspondence.arithmeticPairEpsilonExistence` (arithmetic pair epsilon factors);
  - `Automorphic.CuspidalPairPartialGamma.localGenericity` (local genericity);
  - `Automorphic.cuspidalAllLocalIrreduciblePresentationExistence`,
    `Automorphic.cuspidalDualPresentationExistence` and
    `Automorphic.cuspidalContragredientExistence` (presentations and contragredients);
  - `presentedContragredientAssociation` and `associatedCentralCharacter` (weak association of
    the duals and central characters).

  This theorem is not a proof of `AssociatedGammaStatement`: the statement is proved only once
  both hypotheses are proved theorems.

## Proof of `associatedGamma_of_inputs`

1. Replace `P`, `P'` by presentations `Q`, `Q'` of `T`, `T'` whose local components are
   irreducible and admissible at every place. Choose contragredients `Td`, `Td'` and their
   presentations `Qd`, `Qd'` with the same property. The local classes at `v` agree with those
   of `P`, `P'` by `localComponent_padicClass_eq`.
2. Weak association transfers to `Q`, `Q'` (`IsWeaklyAssociatedClass.presentation`) and to the
   duals (presented contragredient association). Central characters with `det S = ω ∘ τ` come
   from `associatedCentralCharacter`.
3. `ψ` is nontrivial because its component `ψ_v` is. The global functional equation supplies a
   finite factor choice (additive components and self-dual measures at all finite places) and
   archimedean additive components and parameters.
4. By `isPairGammaMatch_of_heckeGammaCertificate`, it suffices to give a certificate for every
   self-dual measure `ν` of `ψ_v`. Build the setups `D`, `A`:
   - the self-dual measure is replaced by `ν` at `v` (`Function.update`);
   - the local-map data are replaced by `(w, e, ι)` at `v`;
   - the local-constant system is replaced by `(eC, ε)` at `v`.

   Apply `hasHeckeGammaCertificate_setups`, then rewrite the setup data at `v` to the given data.
