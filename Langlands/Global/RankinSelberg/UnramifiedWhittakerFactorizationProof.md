# Proof: factorization of a global Whittaker function at one unramified place

The theorem
`Langlands.Global.RankinSelbergGlobal.UnramifiedWhittaker.unramifiedWhittakerFactorization`
proves `Langlands.Global.RankinSelbergGlobal.UnramifiedWhittakerFactorizationStatement`.
Its universe parameters are `u` (the number field) and `uQ` (the local factors of the
spectral presentation). The only axioms are `propext`, `Classical.choice` and `Quot.sound`.

The statement Markdown cites Cogdell 2004, §2.2 (p.206, p.215), and Shintani 1976 (p.180–181).
The Lean proof does not use a restricted tensor product decomposition. It follows the
"intrinsic" argument sketched in the statement Markdown: fix `g` with `g_v = 1`, and look at
the linear functional `ℓ_g : y ↦ W_y(g)` on the space of `T`. This functional is a
`θ`-Whittaker functional for the local action of `GL_(r+1)(F_v)` at `v`. The function
`h ↦ W_x(g · ι_v h)` is the Whittaker coefficient `h ↦ ℓ_g(π_v(h) x)` of the spherical vector
`x` for `ℓ_g`. Shintani's uniqueness theorem (already in the Library) then makes it
`ℓ_g(x) · W°(h; a) = W_x(g) · W°(h; a)`.

## Structure of the module

The file `UnramifiedWhittakerFactorizationProof.lean` has three sections and the main theorem.

### Section `Local`: independence of the uniformizer

`sphericalWhittaker_eq_of_isUniformizingElement`: for two uniformizing elements `ϖ`, `ϖ'` of
the same valuation and a character `θ` trivial on the integral unipotent subgroup,
`sphericalWhittaker hϖ' θ q x = sphericalWhittaker hϖ θ q x`.

Proof. `torus ϖ λ = torus ϖ' λ · (torus (ϖ⁻¹ϖ') λ)⁻¹`
(`torus_eq_torus_mul`), and `torus (ϖ⁻¹ϖ') λ` is integral because `ϖ⁻¹ϖ'` is a unit
(`torus_quotient_mem`; the valuations agree by
`RankinSelberg.UnramifiedPairTorus.valuation_eq_of_isUniformizingElement`). So the function
for `ϖ'` has the same values as the function for `ϖ` on the tori `torus ϖ λ`: by right
`GL(𝒪)`-invariance (`sphericalWhittaker_mul_integral`) and the torus formula
(`sphericalWhittaker_torus`), the value is `δ^(1/2)(λ) s_λ(x)` for antitone `λ` and `0`
otherwise. The Library's `eq_cellFunction` says that a left `θ`-equivariant, right
`GL(𝒪)`-invariant function whose values on the tori `torus ϖ λ` vanish for non-antitone `λ`
is the cell function of `ϖ` with those values. Applied to the function for `ϖ'`, this gives
the cell function of `ϖ` with the values above, which by definition is the function for `ϖ`.

### Section `Coefficient`: Shintani's uniqueness from Hecke scalars

Here `K` is any `PadicField`, with the Hecke operator local instances
(`heckeFieldTopology`, …) of `Langlands.Representation.Unramified.HeckeOperators`.

`coefficientMap_eq_smul_of_corner`: let `ρ` be a smooth representation of
`GL_(r+1)(K)`, `b` a `GL_(r+1)(𝒪_K)`-fixed vector, and suppose that every standard Hecke
operator acts on `b` by the scalar of the Satake parameter `x`:
`PairedHecke.corner K ρ hρ (standardHeckeElement K r i) b = standardHeckeScalar K
(Eigenvalues.ofTuple x) i • b` for all `i : Fin (r + 2)`. Let `θ` be a character trivial on
the integral unipotent subgroup such that for each `i : Fin r` some `z` with
`|z| · |ϖ₀| ≤ 1` has `θ(adjacentUnit i z) ≠ 1`, where `ϖ₀` is the canonical uniformizer. Then for every `θ`-functional `ℓ` and every
uniformizing element `ϖ`, the Whittaker coefficient of `b` is
`(coefficientMap ρ ℓ b).val = ℓ.val b • sphericalWhittaker hϖ θ q x`.

Proof. Reduce to the canonical uniformizer `uniformizerUnit` by the previous section, and
apply `Conductor.coefficientMap_eq_smul_sphericalWhittaker` with residue representatives
`residueLift K`. Its hypotheses are:

* the coset-sum relations for `1 ≤ k ≤ r + 1`: these are
  `standardHecke_cornerAction_eq_sum` (the corner action of the `k`-th standard Hecke
  element is the sum over the minuscule cosets) combined with the hypothesis on `b`;
* the central relation `ρ(ϖ⁻¹ · 1) b = (∏ x_i)⁻¹ b`: the top Hecke element acts by
  `standardHecke_cornerAction_last` through `ρ(ϖ · 1)`, its scalar is `∏ x_i`
  (`standardHeckeScalar_last` and `elementaryCoefficient_ofTuple_top`), and
  `torus ϖ (−1, …, −1) · standardDiagonal (last) = 1`
  (`torus_neg_one_mul_standardDiagonal_last`).

The residue field has `q = residueCardinality` elements (`card_residueField`).

### Section `Global`: the functional `y ↦ W_y(g)`

* `isStandardAdditiveCharacter_complex`: the complex character of a unitary character
  of `𝔸` trivial on `F` is standard (continuous, nontrivial, trivial on `F`, norm one).
* `localPoint F v h` abbreviates the adelic point `ι_v h` of the statement. The lemmas
  `ofFinite_localInclusion_comm` and `commute_localPoint` show that a point with trivial
  `v`-component commutes with every `ι_v h`. The entry lemmas
  (`ofFinite_localInclusion_apply_of_ne`, `_diag`, `_zero`) compute the adelic entries of
  `ι_v h`: an off-diagonal entry is the adele with `h_(ij)` at `v` and `0` elsewhere. With
  them, `localPoint_mem_unipotentAdelic` shows that `ι_v u` is adelic upper unipotent for
  upper unipotent `u`.
* `genericCharacter_localPoint`: the global generic character of `ψ` at `ι_v u` equals the
  standard character `θ = standardCharacter ψv r` at `u`. Both are products over the
  superdiagonal entries (`addChar_map_sum`), and each factor agrees by
  `IsCanonicalFiniteAdditiveComponent ψ v ψv`. `genericCharacter_inv` gives the same for
  `ψ⁻¹` and the inverse character.
* Linearity: `cuspFunction_add`, `cuspFunction_smul`, and
  `integrable_coefficientIntegrand` (the integrand of the Whittaker coefficient descends to
  a continuous function on the compact quotient `N(F)\N(𝔸)`, so it is integrable for the
  normalized probability measure) give `cuspWhittaker_add` and `cuspWhittaker_smul`.
  `whittakerFunctional F ψ hψ T g` is the resulting element of `Module.Dual ℂ T.Space`.
* `cuspFunction_finiteRepresentation` and `cuspWhittaker_finiteRepresentation`: the
  finite adelic action of `T` is right translation of the cusp form, hence of its Whittaker
  function.
* `whittakerFunctional_mem`: if `g_v = 1`, then `whittakerFunctional g` is a `θ`-functional
  for the local representation `T.realization.localRepresentation v`, for every `θ` that
  agrees with the generic character on the points `ι_v u`. Indeed
  `W_(π_v(u) y)(g) = W_y(g · ι_v u) = W_y(ι_v u · g) = θ(u) W_y(g)` by the commutation and
  the left `N(𝔸)`-equivariance `Unfolding.cuspWhittaker_mul_left`.
* `cuspWhittaker_mul_localPoint`: the factorization at `v` for one character `θ`. The vector
  `x` is fixed by `GL_(r+1)(𝒪_v)` (`FiniteAdelicGL.localIntegral_eq_sphericalSubgroup`
  identifies the two integral subgroups). The Hecke scalars on `x` are those of `a`: this is
  `CuspidalSpectralPresentation.corner_eq_smul` at `v ∉ P.exceptional`, rewritten along the
  hypothesis `Eigenvalues.ofTuple a = P.spectralSystem.eigenvalues v _`. Then
  `coefficientMap_eq_smul_of_corner` with `ℓ = whittakerFunctional g`, evaluated at `h`, is
  `W_x(g · ι_v h) = W_x(g) · sphericalWhittaker hϖ θ q a h`.

### The main theorem

After introducing the data, `FiniteAdditiveSupport ψ S` at `v ∉ S` gives a canonical
component `ψz` with additive conductor `0`. By
`RankinSelberg.HighlyRamified.hasIntegerConductor_of_additiveConductor_eq_zero` it has
integer conductor. `ψv` and `ψz` are both canonical components of `ψ` at `v`, so they agree
pointwise, and `ψv` has integer conductor too (`Conductor.HasIntegerConductor`). Then:

* `θ = standardCharacter ψv r` is trivial on the integral unipotent subgroup
  (`Iwasawa.isIntegrallyTrivial_standardCharacter`). For each `i : Fin r`, some `z`
  with `|z| · |ϖ₀| ≤ 1` has `θ⁻¹(adjacentUnit i z) ≠ 1`
  (`Conductor.exists_adjacentUnit_ne_one`), hence also `θ(adjacentUnit i z) ≠ 1`.
* The first conjunct is `cuspWhittaker_mul_localPoint` for `ψ.complex`, with the
  compatibility `genericCharacter_localPoint`.
* The second conjunct is `cuspWhittaker_mul_localPoint` for `ψ.complex⁻¹`, which is standard
  by `Unfolding.isStandardAdditiveCharacter_inv`, with
  `θ⁻¹ = inverseStandardCharacter ψv r`
  (`Iwasawa.isIntegrallyTrivial_inverseStandardCharacter`, `exists_adjacentUnit_ne_one`
  directly), and the compatibility `genericCharacter_inv` plus
  `genericCharacter_localPoint`.

## Implementation notes

* The carrier of `padicField v` is `v.adicCompletion F` (`FiniteCompletion F v`), so the
  Hecke local instances, stated for `F.Carrier` of a variable `PadicField`, do not fire for
  it. The `Global` section declares one local instance, `uwfpLocalValuativeRel v`, which is
  the canonical valuative relation of `padicField v` on `FiniteCompletion F v`. The
  canonical topology is passed explicitly (`@Whittaker.standardCharacter _ _ …topology`),
  as in the statement.
* The scheme local instances of the `Global` section repeat those of the statement module.
  The additive-group local instances on the spaces of automorphic functions are the
  submodule instances, as in `Langlands.Automorphic.ContragredientSphericalSpectrum`.
* No result here is new mathematics beyond the source. The local lemmas only restate the
  Library's Shintani uniqueness (`Conductor.coefficientMap_eq_smul_sphericalWhittaker`) in
  terms of the Library's spherical Hecke scalars, for an arbitrary uniformizer.
