# Finite-place factors of twisted relative Weil pairs as Hecke factors

This module does the finite-place comparison in the global assembly of the
twisted relative Weil functional equation. Let `E / F` be a Galois extension of
number fields, `c` a class family with the restriction compatibility `h`, and
`χ` a Hecke character of `F`. Let `S`, `S'` be representations of the relative
Weil group `W_{E/F}`, and let `x = [X]` be the continuous virtual class of a
continuous `X ≃ S ⊗ S'`. Suppose `x` has a twisted degree-zero decomposition:
for every continuous character `η` of `W_{E/F}`,

`η ⊗ x = deg x · [η] + Σ_i r_i Ind_{W_{E/K_i}}^{W_{E/F}}([η|_{W_{E/K_i}} θ_i] - [η|_{W_{E/K_i}} θ'_i])`,

with intermediate fields `K_i` and `θ_i = θh_i ∘ τ_{K_i}`, `θ'_i = θh'_i ∘ τ_{K_i}`
for Hecke characters `θh_i`, `θh'_i` of `K_i`. The Library's
`exists_twist_decomposition` (module `RelativeWeilBrauer`) gives such a
decomposition. Let `ι : W_{F_z} → W_{E/F}` be a local map at a finite place `z`
of `F` (`IsLocalRelativeWeilMap z w e ι` for a place `w` of `E` above `z`).

The module proves that the local factor triple of the twisted pair
`((χ ∘ τ_F) ⊗ S, S')` along `ι` at `z` is a product of Hecke local factors. The
characters involved are `χ` at `z` and `λ_i = (χ ∘ N_{K_i/F}) θh_i`,
`λ'_i = (χ ∘ N_{K_i/F}) θh'_i` at the places `u` of `K_i` above `z`:

- `L(s) = L(s, χ_z)^{deg x} Π_i (Π_{u | z} L(s, λ_{i,u}) / Π_{u | z} L(s, λ'_{i,u}))^{r_i}`,
  wherever these Hecke L-factors are nonzero;
- the dual L-factor is the same expression with `χ⁻¹`, `λ_i⁻¹`, `λ'_i⁻¹`;
- `ε(s) = ε(s, χ_z)^{deg x} Π_i (Π_{u | z} ε(s, λ_{i,u}) / Π_{u | z} ε(s, λ'_{i,u}))^{r_i}`
  for all `s`. The base factor is taken with the additive character `ψf_z`.
  The factors at `u` use the trace components `ψf_z ∘ Tr_{K_{i,u}/F_z}`. All
  measures are arbitrary self-dual Haar measures.

Here the Hecke L-factor `heckeL l v s` is Tate's `PadicAbelian.lFactor` of the
component `l_v` for the completion realization of `K_v`. The Hecke epsilon
factor is the Library's `HeckeFunctionalEquation.finiteEpsilon`.

## Provenance

The provenance is derived. Tate, *Number theoretic background* (Corvallis
1979), (3.5.1) and (3.5.2), printed p. 16 (PDF p. 25), define the global
L-function and epsilon factor of a representation `V` of the Weil group as
products over the places `v` of the local factors of `V_v`. Here `V_v` is `V`
composed with the local map at `v`. The same page explains that, via (2.3.1),
(2.3.5) and inductivity of the local factors, these products are inductive in
degree zero. Their value on a quasicharacter `χ` is Hecke's product of the
local factors `L(χ_v)` and `ε(χ_v, ψ_v, dx_v)`. This module carries out that
argument at one finite place for a twisted degree-zero decomposition. The steps
are the following.

1. Restrict the decomposition along `ι`. The local restriction formula (Tate
   (2.3.5) with (1.6.1)) is the hypothesis `hN2`.
2. Identify every restricted character with the Weil character of a Hecke
   component along a geometric reciprocity map. This uses the transfer
   reciprocity of local maps (Tate (1.6.1), hypothesis `hN3`), transfer-norm
   compatibility (Tate (1.2.2), hypothesis `hN4`), and geometricity of
   common-closure candidates (hypothesis `hgeo`).
3. Apply the published local results. `RelativeWeilLocalEulerBridge` gives
   the L-factors. `RelativeWeilLocalEpsilonTransport` gives the epsilon factors
   for a supplied local-constant system; this is Tate's inductivity, Theorem
   (3.4.1) with (3.4.2) and (3.4.8), printed pp. 14–15.
4. Transport Tate's rank-one factors ((3.1.3) and §3.2) from the canonical
   p-adic packages to the completion realizations used by Hecke's factors.

The hypotheses `hN2`, `hN3`, `hN4` and `hgeo` are published statements
(`LocalInducedRestrictionStatement`, `LocalTransferReciprocityStatement`,
`TransferNormCompatibilityStatement`,
`LocalClassField.CommonClosureGeometricStatement`). This module does not prove
them; every theorem that uses them takes them as explicit hypotheses. The
equivalences, transports and reindexing are internal bookkeeping.

## Representations (`Langlands.FiniteRepresentation`)

- `restrictTwistTensorEquiv φ χ A B`: the restriction along `φ` of the twist
  `χ ⊗ (A ⊗ B)` is equivalent to the tensor product of the restricted twist of
  `A` and the restriction of `B`. The underlying linear map is the identity.
- `restrictDualEquiv φ A`: restriction along `φ` commutes with duals; the
  underlying linear map is the identity.

## Self-dual measures (`Langlands.LocalFactor.PadicAbelian`)

- `isSelfDualMeasure_haarMeasureCongr`: let `T` be a realization of a p-adic
  package equal to the canonical one. A self-dual Haar measure `μ` for `T` and
  an additive character `ψ`, moved to the canonical topology
  (`haarMeasureCongr`), is self-dual (`Correspondence.IsSelfDualMeasure`) for
  every canonical-topology nontrivial additive character `ψ'` with the same
  underlying additive character as `ψ`.

## Completions (`Langlands.Global.CompletionPadic`)

- `quasicharacterBase v χ`: a character of `K_vˣ`, continuous for the completion
  topology, as a quasicharacter of the canonical package `padicField v`. The
  underlying homomorphism is unchanged. This is the selected definition. It is
  the form of `quasicharacterAt v rfl` for `padicField v` itself; that form
  avoids comparing `padicField v` with `padicFieldAt v rfl` definitionally.
- `lFactor_quasicharacterBase`: Tate's L-factor of `quasicharacterBase v χ`
  for the canonical package is Tate's L-factor of `χ` for the completion
  realization. `lFactor_inv_quasicharacterBase` and
  `lFactor_inv_quasicharacterAt` are the forms for the inverse quasicharacter,
  for `padicField v` and for `padicFieldAt v h`.

## Local maps for the Krull topology (`Langlands.ClassField.Global.RelativeWeilGroup`)

The rest of the module makes the discrete topology on `Gal(E/F)` a local
instance (`relativeGaloisTopology`), as in `LocalInducedRestriction`. Two
abbreviations, declared before that instance, keep the Krull topology of
`IsLocalRelativeWeilMap` visible:

- `KrullLocalMap c F E z`: continuous homomorphisms `W_{F_z} → W_{E/F}` for the
  Krull topology;
- `krullLocalPairClass S ι`: the Library's `localPairClass S ι` for such a map.

Each theorem below takes `ι : KrullLocalMap c F E z`. It applies the
discrete-topology results to `discreteLocalMap ι`, which has the same
underlying homomorphism.

## Characters

- `continuousReciprocityCharacter_comp_eq_weilCharacter`: for a Hecke character
  `l` of `K`, a candidate `e` of the package `padicFieldAt v hv` and a local map
  `φ` whose transfer is inverse reciprocity along `e`, `(l ∘ τ_K) ∘ φ` is the
  Weil character of `quasicharacterAt v hv l_v` along `e`.
- `continuousReciprocityCharacter_comp_eq_weilCharacter_base`: the same for
  the package `padicField v`, with `quasicharacterBase v l_v`.

## Components

- `continuousReciprocityCharacter_comp_discreteLocalMap` (base place): under
  `hN3` and `hgeo`, `(l ∘ τ_F) ∘ ι` is the Weil character of
  `quasicharacterBase z l_z` along the base candidate
  `baseReciprocityCandidate (padicField z) eC` of a normalized family `eC`.
  By `hgeo`, that candidate is geometric, so `hN3` applies to it.
- `continuousReciprocityCharacter_tower_comp_eq_weilCharacter` (places above
  `z`): let `φ : W_{K_u} → W_{E/K}` be a local map whose transfer is inverse
  geometric reciprocity of `K_u`. Under `hN4` and `hgeo`,
  `((χ ∘ τ_F)|_{W_{E/K}} · (θh ∘ τ_K)) ∘ φ` is the Weil character of the
  component of `(χ ∘ N_{K/F}) θh` at `u`. The candidate is the transported
  `extensionReciprocityCandidate (padicField z) (towerPadicField z u) _ eC`.
  The proof uses the Library's `continuousReciprocityCharacter_comp_restrictionInclusion`
  (which needs `hN4`) and `continuousReciprocityCharacter_mul`.

## Identity

- `continuousRestrict_continuousTwist_eq_weilCharacter`: under `hN2`, `hN3`,
  `hN4` and `hgeo`, the restriction along `ι` of `(χ ∘ τ_F) ⊗ x` is
  `deg x · [χ_z ∘ rec_z] + Σ_{(i, u)} r_i Ind_{W_{K_{i,u}}}^{W_{F_z}}([λ_{i,u} ∘ rec_u] - [λ'_{i,u} ∘ rec_u])`.
  The sum runs over the Σ-type of pairs `(i, u)` with `u` a place of `K_i`
  above `z`. The reciprocity maps are the candidates of `eC`, and induction is
  along `extensionWeilMap (padicField z) (towerPadicField z u) _`. The proof
  applies `hdec` at `η = χ ∘ τ_F`. It restricts with the Library's
  `exists_continuousRestrict_decomposition`, applied to the local restriction
  formulas given by `hN2`; its local maps `ιu` have geometric transfer. It then rewrites each character with the two
  Components theorems.
- `continuousRestrict_continuousTwist_ofRepresentation`: the restricted twist
  of `[X]` is the class of the restricted twisted representation.

## L-factors

- `lFactor_inv_quasicharacterBase_eq_heckeL`,
  `lFactor_inv_quasicharacterAt_eq_heckeL`: Tate's L-factor of the inverse
  transported component of `l` is `heckeL l⁻¹ v s`.
- `prod_lFactor_quasicharacterAt_eq_prod_heckeL` and its inverse form
  `prod_lFactor_inv_quasicharacterAt_eq_prod_heckeL`: the product over
  `FinitePlacesAbove K z` of Tate's L-factors for the canonical packages
  `towerPadicField z u` is the product over `placesAbove K z` of `heckeL`.
- `eval_arithmeticPairLFactor_eq_heckeL` (L-factor): at every `s` where
  `heckeL χ z s` and every `heckeL λ_i u s`, `heckeL λ'_i u s` (`u ∈ placesAbove (K_i) z`)
  are nonzero, the arithmetic pair L-factor of
  `krullLocalPairClass ((χ ∘ τ_F) ⊗ S) ι` and `krullLocalPairClass S' ι`,
  evaluated at the spectral point `q_z^{-s}`, is
  `heckeL χ z s ^ deg x * Π_i ((Π_{u} heckeL λ_i u s) * (Π_{u} heckeL λ'_i u s)⁻¹) ^ r_i`.
  The proof feeds the Identity theorem and the equivalence
  `restrict ι ((χ ∘ τ_F) ⊗ X) ≃ restrict ι ((χ ∘ τ_F) ⊗ S) ⊗ restrict ι S'` to
  `InertiaEuler.eval_arithmeticPairLFactor_eq_virtualLValue`. It then rewrites
  `virtualLValue` with the transport lemmas and regroups the Σ-type product
  as a product over `i` of products over places.
- `eval_arithmeticPairLFactor_dual_eq_heckeL` (dual L-factor): the same for the
  duals of `(χ ∘ τ_F) ⊗ S` and `S'`, with `χ⁻¹`, `λ_i⁻¹` and `λ'_i⁻¹`, through
  `InertiaEuler.eval_arithmeticPairLFactor_dual_eq_virtualLValue` and
  `restrictDualEquiv`.

## Epsilon factors

- `traceComponents_apply_of_liesOver`: for a place `u` of `K` lying over `z`,
  the trace component `traceComponents ψf u` (module `RelativeWeilAssemblyGlobal`)
  at `y ∈ K_u` is `ψf_z(FiniteExtension.localTrace z u y)`.
- `epsilon_baseFieldHaarMeasure_eq_finiteEpsilon` (base place): let
  `ψf_z = ofCanonicalCharacter z ψz`, `ψ'` a base character of `ψz`, and `μd` a
  bottom-field Haar measure self-dual for `ψ'`. Then Tate's epsilon factor of
  `quasicharacterBase z χ_z`, at the measure on `F_z` corresponding to `μd`, is
  `finiteEpsilon χ ψf μ z s` for every self-dual family `μ`. The proof
  identifies both measures with the Library's `localSelfDualHaar`. It uses
  `Correspondence.isSelfDual_of_isBaseCharacter_iff`,
  `isSelfDualMeasure_haarMeasureCongr` and `Correspondence.eq_localSelfDualHaar`,
  and then `PadicAbelian.epsilon_quasicharacterCongr`.
- `prod_epsilon_quasicharacterAt_eq_prod_finiteEpsilon` (places above `z`): the
  product over `FinitePlacesAbove K z` of Tate's epsilon factors for the
  canonical packages, the standalone trace characters of `ψz` and the
  transported self-dual measures `haarMeasureAt u _ μK_u` is the product over
  `placesAbove K z` of `finiteEpsilon l (traceComponents ψf) μK u s`.
- `epsilonMonomial_eq_finiteEpsilon` (epsilon factor): let `c q_z^{-ms}` be an
  arithmetic pair epsilon factor (`Correspondence.IsArithmeticPairEpsilonFactor`)
  of the twisted pair along `ι`. It is taken for a local-constant system
  `(eC, εz, hεz)` and the additive character `ψz`, with `ψf_z = ofCanonicalCharacter z ψz`.
  Then for all `s`, `c q_z^{-ms}` is
  `finiteEpsilon χ ψf μ z s ^ deg x * Π_i ((Π_u finiteEpsilon λ_i (traceComponents ψf) μK_i u s) * (Π_u finiteEpsilon λ'_i (traceComponents ψf) μK_i u s)⁻¹) ^ r_i`.
  The proof evaluates the epsilon factor on its own admissible datum and applies
  `SystemEpsilon.conditionalPairEpsilonValue_eq_epsilon_of_virtualIdentity` to
  the identity. It then rewrites the factors with the two lemmas above.

## Factors

- `localFactors_eq_heckeFactors`: let `f` be the factor triple of the twisted
  pair along `ι` at `z` (`IsArithmeticPairLocalFactors` for
  `krullLocalPairClass ((χ ∘ τ_F) ⊗ S) ι`, `krullLocalPairClass S' ι` and their
  duals). Then `f.lFactor`, `f.dualLFactor` and `f.epsilonFactor` are the three
  Hecke products above; the two L-factor identities are conditional on
  nonvanishing. This combines the three main theorems. Its conclusion has the
  shape of the per-place step in Worker 1795's global assembly.

No semisimplicity is assumed. These results are supporting lemmas for the global
assembly. The module does not prove the task's target statement, and its
conclusions depend on the four hypotheses named above.
