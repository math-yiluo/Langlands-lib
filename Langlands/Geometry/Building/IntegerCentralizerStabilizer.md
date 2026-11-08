# Centralizer points fixing an apartment point

Let `k` be a field and `v : Valuation k (WithZero (Multiplicative ℤ))` a
valuation. No completeness, discreteness or Henselian hypothesis is used. `B : IntegerValuationBuildingData v G` is the
Library building datum of a group scheme `G` over `Spec k` with affine
structure map. It contains a maximal split torus `B.i : S ⟶ G` of the connected
reductive group `G`, the apartment class, the actual centralizer
`B.centralizer` (`Z = Z_G(S)` with inclusion `j : Z ⟶ G` and factorization
`s : S ⟶ Z`), and axiom V 6 of Kaletha–Prasad Definition 6.1.2 for all of
`Z(k)` (`B.isOmegaCompatible`).

The module proves that a point `z ∈ Z(k)` whose image `j(z)` lies in `G(k)^1`
and which fixes one point of the apartment lies in `Z(k)^1`. Here `G(k)^1` and
`Z(k)^1` are the Library `characterValuationKernel`s: the points on which every
rational character has valuation zero.

## Provenance

The module's results are internal. They are not quoted from Kaletha–Prasad,
but they are what the Library's form of V 6 gives for an element of the
centralizer. By `IntegerValuation.IsOmegaCompatible.smul_eq_vadd`, `z ∈ Z(k)`
acts on the apartment by the translation `ν(z) = −ω_Z(z)`, taken modulo the
common kernel of the relative roots. If `z` fixes a point, `ω_Z(z)` is
therefore annihilated by every relative root. If `j(z) ∈ G(k)^1`, then `ω_Z(z)`
is also annihilated by every restricted rational character of `G`. The Library
theorem `relativeRootsRestrictedCharactersSpan` states that relative roots and
restricted rational characters of `G` together span the rational character
space of `S`. Hence `ω_Z(z) = 0`, which says that `z ∈ Z(k)^1`.

## Statements

- `evalAtLinear T w : characterLattice T →ₗ[ℤ] ℝ` is evaluation
  `χ ↦ eval T χ w` at a real cocharacter `w ∈ V(T)`, viewed as a `ℤ`-linear
  map. `evalAtLinear_apply` is its defining equation.
- `eq_zero_of_eval_relativeRoots_of_eval_torusCharacterRestrict` assumes `G`
  connected reductive and `i : T ⟶ G` a maximal split torus. Let `w ∈ V(T)`
  satisfy `eval T a w = 0` for every relative root `a ∈ relativeRoots i`, and
  `eval T (torusCharacterRestrict i χ) w = 0` for every rational character `χ`
  of `G`. Then `w = 0`.
- `IntegerValuationBuildingData.characterRestriction_characterRestrict`:
  restricting a rational character `χ` of `G` to `Z` and then to `S`
  (`Cartan.characterRestriction s (characterRestrict j χ)`) gives
  `torusCharacterRestrict B.i χ`.
- `IntegerValuationBuildingData.mem_characterValuationKernel_of_smul_eq`: if
  `z ∈ Z(k)` has `j(z) ∈ G(k)^1` and `B.centralizer.toNormalizer z • x = x` for
  one apartment point `x`, then `z ∈ Z(k)^1`.
- `IntegerValuationBuildingData.mem_characterValuationKernel_iff_smul_eq`: for
  one apartment point `x`, `z ∈ Z(k)^1` if and only if `j(z) ∈ G(k)^1` and `z`
  fixes `x`.
- `IntegerValuationBuildingData.mem_characterValuationKernel_of_mem_oneStabilizer`
  assumes that the apartment map `B.apartmentMap` into the reduced building is
  injective. If `j(z)` lies in `B.oneStabilizer (B.apartmentMap x)`, which is
  `G(k)^1` intersected with the fixer of the image of `x`, then
  `z ∈ Z(k)^1`.
- `IntegerValuationBuildingData.comap_oneStabilizer_eq_characterValuationKernel`
  makes the same injectivity assumption. It states that the preimage under
  `j : Z(k) → G(k)` of `B.oneStabilizer (B.apartmentMap x)` equals `Z(k)^1`.

## Proofs

`eq_zero_of_eval_relativeRoots_of_eval_torusCharacterRestrict` extends
`evalAtLinear T w` to a `ℚ`-linear map on `ℚ ⊗ X^*(T)`
(`LinearMap.liftBaseChange`). The two hypotheses say that this map vanishes on
the images of the relative roots and of the restricted characters. By
`relativeRootsRestrictedCharactersSpan` and `LinearMap.ext_on`, the map is zero.
Evaluating it at `1 ⊗ χ` gives `eval T χ w = 0` for every character `χ` of `T`.
The Library lemma `eq_zero_of_forall_eval_eq_zero` says that characters of a
split torus separate `V(T)`, so `w = 0`.

`characterRestriction_characterRestrict` first proves the unpacked equation
`characterRestrict s (characterRestrict j χ) = characterRestrict B.i χ`. It
does so with `characterRestrict_comp` and the factorization
`B.centralizer.comp_eq : s ≫ j = B.i`, rewritten forward. Both sides are then
unfolded.

`mem_characterValuationKernel_of_smul_eq` rewrites `Z(k)^1` as the kernel of
the centralizer valuation `ω_Z`, using `IntegerValuation.centralizerValuation_ker`.
It then applies the spanning lemma to `w = ω_Z(z)`:

- Roots: V 6 (`smul_eq_vadd`) together with `z • x = x` makes the class of
  `ν(z)` in the translation space zero. So `ν(z) = −ω_Z(z)` lies in
  `rootAnnihilator B.i`, and `mem_rootAnnihilator` gives `eval a (ω_Z(z)) = 0`
  for every relative root `a`.
- Characters: `characterRestriction_characterRestrict`,
  `IntegerValuation.centralizerValuation_spec` and
  `rationalCharacterEval_characterRestrict` rewrite
  `eval (torusCharacterRestrict B.i χ) (ω_Z(z))` as the integer order of
  `χ(j(z))`. This order is `0` because `j(z) ∈ G(k)^1`, via
  `IntegerValuation.orderUnits_eq_one_iff`.

The reverse implication in `mem_characterValuationKernel_iff_smul_eq` uses
`IntegerValuation.map_mem_characterValuationKernel` and
`IntegerValuation.IsOmegaCompatible.smul_eq_self`.

`mem_characterValuationKernel_of_mem_oneStabilizer` uses `mem_oneStabilizer`
to split membership into `j(z) ∈ G(k)^1` and `j(z)` fixing `B.apartmentMap x`.
By `normalizer_smul_apartmentMap`, the second condition is
`B.apartmentMap (z • x) = B.apartmentMap x`, and injectivity gives `z • x = x`.
The comap equality combines this with `map_mem_oneStabilizer`.
