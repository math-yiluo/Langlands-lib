# Level calculus for mirabolic derivatives

Module `Langlands.Representation.Derivative.LevelCalculus`, namespace
`Langlands.Derivative.LevelCalculus`.

This module collects elementary consequences of the published definitions of
`level`, `HasNonzeroDerivative` and `IsHomogeneous`
(`Langlands.Representation.Derivative.Homogeneity`). They are used by the
proof of Zelevinsky's Theorem 6.2 (homogeneity of segment-socle products).
Some results take the published exactness proposition
`Mirabolic.MinusExactnessStatement F T` as an **explicit hypothesis `hE`**.
That proposition is not proved here, and nothing here depends on its proof.
Other results use the published detection theorem
`Langlands.Derivative.mirabolicDerivativeDetection`: every nontrivial smooth
representation of `P_(N+1)` has a nontrivial derivative of some positive order.

## Provenance

This is internal derived material. Zelevinsky, *Induced representations of
reductive p-adic groups II* (`zelevinsky-1980-induced-ii`, §4.3 level, §5.1
homogeneity, printed pp. 184 and 187) uses these facts without stating them.
Examples: level is monotone along injections because derivatives are exact,
and a nonzero `Φ⁻ A` has level one less than `A`. The statements below are
exact Lean versions of these routine facts. No source result is formalized
here as such.

## Conventions

Every result uses `{p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}`,
`T : F.TopologicalData` and a unitary additive character
`ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology`, with `T.topology`
installed. Carriers live in `Type uV`. `mirabolic N F.Carrier` is the actual
subgroup `P_(N+1)` of `GL_(N+1)`.

## Maps of smooth representations (section `Maps`)

These hold for an arbitrary topological group `G` and smooth complex
representations with carriers in `Type uV`.

- `nontrivial_of_injective`, `subsingleton_of_injective`: an injective
  intertwiner `f : A ⟶ B` transports `Nontrivial A` to `Nontrivial B`, and
  `Subsingleton B` to `Subsingleton A`.
- `hom_inv_apply`, `inv_hom_apply`, `iso_hom_injective`,
  `iso_hom_surjective`, `nontrivial_iff_of_iso`, `subsingleton_iff_of_iso`:
  pointwise inverse laws of an isomorphism `e : A ≅ B`. Its forward map is
  bijective, and `A`, `B` are simultaneously nontrivial (or subsingleton).
- `isIso_of_bijective`: a bijective intertwiner is an isomorphism (through
  `SmoothRep.mono_iff_injective`/`epi_iff_surjective`).
- `codRestrict f U hU` (definition): the corestriction of `f : A ⟶ B` to an
  invariant subspace `U` of `B` containing all values of `f`, as an intertwiner
  `A ⟶ SmoothRep.subrepresentation B U`. `codRestrict_apply`: composed with the
  inclusion of `U` it is `f`. `codRestrict_injective`: injective when `f` is.
- `isoRange f hf` (definition): for injective `f`, the isomorphism of `A` with
  the subrepresentation `range f` of `B` (the corestriction of `f`).
- `subrepresentation_nontrivial`: an invariant subspace `U ≠ ⊥` gives a
  nontrivial subrepresentation. `range_ne_bot`: an injective map out of a
  nontrivial `A` has range `≠ ⊥`.
- `topIso A` (definition): the subrepresentation `⊤` is isomorphic to `A`
  (by its inclusion). `top_ne_bot`: `⊤ ≠ ⊥` when `A` is nontrivial.
- `comap f U` (definition): the preimage of an invariant subspace `U ⊆ B`
  under `f : A ⟶ B`, an invariant subspace of `A`; `mem_comap` is its
  membership rule. `comapMap f U` (definition) is the induced intertwiner
  `comap f U ⟶ U`, and `comapMap_injective` says it is injective when `f` is.
- `IsShortExact i q` (structure, a `Prop`): `i : A ⟶ B` is injective, `q : B ⟶ C`
  is surjective, and `range i = ker q` as linear maps. This is exactly the
  hypothesis triple of the published `Mirabolic.MapsShortExactIntertwiners`.
- `subsingleton_of_isShortExact`: if `A` and `C` are subsingletons, so is `B`.
- `isShortExact_mkQ`: an injective `i` with the quotient map onto
  `B / range i` is short exact. `isShortExact_kernelι`: the inclusion of
  `ker q` with a surjective `q` is short exact.

## Exact functors (section `Exact`)

- `mapsShortExact_id`, `mapsShortExact_comp`: the identity functor, and a
  composite of two functors that both satisfy `MapsShortExactIntertwiners`,
  satisfy it.
- `isShortExact_map`: such a functor maps `IsShortExact` pairs to
  `IsShortExact` pairs.
- `map_injective_of_exact`, `map_surjective_of_exact`: such a functor
  preserves injective and surjective intertwiners. Proof: apply it to the
  short exact pairs of `isShortExact_mkQ` and `isShortExact_kernelι`.

## Exactness of derivative functors (section `DerivativeExact`)

- `mapsShortExact_mirabolicRankCast`: the rank transport functor
  `mirabolicRankCast T h` is exact (after `subst`, it is the identity).
- `mapsShortExact_phiMinusIterate`, `mapsShortExact_mirabolicDerivative`,
  `mapsShortExact_mirabolicDerivativeOfOrder`: assuming `hE`, the iterated
  `Φ⁻`, the derivative `mirabolicDerivative T ψ n k = (Φ⁻)^k ⋙ Ψ⁻` and the
  order wrapper `mirabolicDerivativeOfOrder T ψ N k hk` all satisfy
  `MapsShortExactIntertwiners`. Proof: composites of the normalized `Φ⁻`
  (`hE.2.2.2`) and `Ψ⁻` (`hE.2.2.1`) components of `hE`.

## Level (section `Level`)

Throughout, `A B C` are smooth representations of `mirabolic N F.Carrier`.

- `hasNonzeroDerivative_level`: if `level T ψ A ≠ 0` then `A` has a nontrivial
  derivative of order `level T ψ A` (property of `Nat.findGreatest`).
- `level_le_of_imp`: if every order at which `A` has a nontrivial derivative
  is also one for `B`, then `level A ≤ level B`.
- `hasNonzeroDerivative_iff_of_iso`, `level_eq_of_iso`: isomorphic
  representations have the same nonzero derivative orders and the same level.
- `level_mirabolicRankCast`, `nontrivial_mirabolicRankCast_iff`: rank transport
  preserves level and nontriviality.
- `nontrivial_of_hasNonzeroDerivative`, `nontrivial_of_level_ne_zero`: a
  representation with a nontrivial derivative, or with nonzero level, is
  nontrivial (derivatives of a zero representation are zero).
- `level_pos`: for nontrivial `A`, `0 < level T ψ A`. This is the published
  `mirabolicDerivativeDetection` restated.
- `level_ne_zero_iff`, `level_eq_zero_iff_subsingleton`: `level A ≠ 0` iff `A`
  is nontrivial; `level A = 0` iff `A` is a subsingleton.

The following take `hE : Mirabolic.MinusExactnessStatement F T`.

- `hasNonzeroDerivative_of_injective`, `level_le_of_injective`: for an
  injective `f : A ⟶ B`, every nonzero derivative order of `A` is one of `B`,
  so `level A ≤ level B`. Proof: the derivative functor of each order is exact,
  so it maps `f` to an injective map.
- `level_le_max_of_isShortExact`: for a short exact pair `A → B → C`,
  `level B ≤ max (level A) (level C)`. Proof: at order `k = level B > 0` the
  derivative sequence is short exact. If both outer derivatives at order `k`
  vanished (they do when `k` exceeds both outer levels), the middle one would
  vanish too.

## One `Φ⁻` step (section `Shift`)

Here `A` is a representation of `mirabolic (M+1) F.Carrier` and
`Φ⁻ A = (Mirabolic.phiMinus T ψ M).obj A` is a representation of
`mirabolic M F.Carrier`.

- `nontrivial_mirabolicDerivative_cast_congr`,
  `hasNonzeroDerivative_succ_iff_cast`: reading the order-`(j+1)` derivative
  through any decomposition `N = n + j` (with rank transport) gives the same
  nontriviality.
- `mirabolicDerivative_succ_cast_obj`: for `M + 1 = n + (j+1)` and
  `M = n + j`, the order-`(j+2)` derivative of `A` is, as an object, the
  order-`(j+1)` derivative of `Φ⁻ A` (definitional unfolding of
  `phiMinusIterate`).
- `hasNonzeroDerivative_succ_iff`: for `0 < k`, `A` has a nonzero derivative
  of order `k+1` iff `Φ⁻ A` has one of order `k`.
- `level_le_level_phiMinus_succ`: `level A ≤ level (Φ⁻ A) + 1`.
- `level_eq_level_phiMinus_succ`: if `0 < level (Φ⁻ A)` then
  `level A = level (Φ⁻ A) + 1`.
- `level_le_one_of_subsingleton_phiMinus`: if `Φ⁻ A` is zero then
  `level A ≤ 1`.
- `nontrivial_phiMinus_iff`: `Φ⁻ A` is nontrivial iff `1 < level A`. This uses
  detection (`level_pos`).

## Homogeneity through injections (section `Homogeneous`)

- `level_eq_of_isHomogeneous`: if `X` is homogeneous (`IsHomogeneous T ψ X`)
  and `f : W ⟶ X` is injective with `W` nontrivial, then
  `level W = level X`. Proof: `W ≅ range f` (`isoRange`) and `range f ≠ ⊥`.
- `isHomogeneous_of_forall_injective`: if there is a number `c` such that every
  nontrivial `W` with an injective `W ⟶ X` has level `c`, then `X` is
  homogeneous. A subsingleton `X` is homogeneous by the published
  `isHomogeneous_of_subsingleton`.
- `isHomogeneous_of_iso`: homogeneity is invariant under isomorphism.

No result here asserts exactness of `Φ⁻`/`Ψ⁻`; every use of exactness goes
through the explicit hypothesis `hE`.

## Import audit

This module is submitted together with `ProductVanishing`, `RestrictionBridge`,
`RightMixedLevel` and `RestrictedProductLevel` (all in
`Langlands.Representation.Derivative`). On Library base `6cb15022`, the
transitive project import closure of these five modules has 140 modules: the
five themselves and 135 published Library modules. Four published
propositions enter only as explicit hypotheses. This module uses
`MirabolicMinusExactnessStatement`. The other four modules also use
`MixedProductDerivativeStatement`, `MirabolicProductMinusCompatibilityStatement`
and `MirabolicProductRestrictionStatement`. None of the four has a published
proof at this base, and none of their proofs is assumed or imported. The one
published proof module whose theorem is used is
`MirabolicDerivativeDetectionProof` (`mirabolicDerivativeDetection`, used by
`level_pos`). The closure contains no module for the conclusions excluded by task `b711af72`
(segment-socle irreducibility, swaps or commutation, exhaustion,
special-head, tempered-block or square-integrable classification, or generic
uniqueness). It also contains no two-supercuspidal product module.

## Attribution

The five modules are by Worker 1070, except three declarations of
`ProductVanishing` (`subsingleton_of_isZero`, `isZero_of_subsingleton`,
`subsingleton_binary`). These are copied or adapted from published code by
Worker 745 in the module
`Langlands.Representation.Classification.TwoSupercuspidalBinaryProductBridge`
(namespace `Langlands.Classification.BinaryProductBridge`); see the
section "Adapted code and attribution" of `ProductVanishing.md`. Worker 745 is
therefore a coauthor of these modules.
