# Proof of the central sign identity over the infinite places and `S`

This module proves the Library proposition
`Langlands.Global.RankinSelbergGlobal.ArchimedeanCentralSignStatement.{u, uQ}` (module
`Langlands.Global.RankinSelberg.ArchimedeanCentralSignStatement`). The proof is the theorem

```
theorem Langlands.Global.RankinSelbergGlobal.archimedeanCentralSign :
    ArchimedeanCentralSignStatement.{u, uQ}
```

Both universe parameters stay free, and the theorem adds no hypothesis.

## Statement proved

Let `F` be a number field with `𝔸_F/F` compact. Let `T'` be an actual cuspidal realization of
`GL_(t+1)` over `F`, and `P'` a spectral presentation of `T'` whose local components are
irreducible and admissible. Let `S` be a finite set of finite places with
`P'.exceptional ⊆ S`. Let `ψv` be a family of nontrivial additive characters of the
completions at the finite places, and let `ζ : S → ℂ^×`. Assume that for each `v ∈ S` some
nonzero Whittaker functional `ℓ` on the local component `σ_v` of `P'` at `v` satisfies
`RankinSelberg.HasModelMinusOneScalar σ_v ℓ (ζ v)`: every function `W` in the Whittaker model
of `ℓ` satisfies `W(-g) = ζ_v W(g)`. Then

`(∏_(v real) realMinusOneScalar T' v) · (∏_(w complex) complexMinusOneScalar T' w) · ∏_(v ∈ S) ζ_v = 1`.

This is the identity `∏_(v ∈ S ∪ ∞) ω'_v(−1) = ω'(−1) = 1` in the proof of Theorem 4.1 of
J. W. Cogdell, *Analytic theory of L-functions for GL_n* (2004), printed p.220 (source
`cogdell-2004-analytic-theory-gln`). Here `ω'` is the central character of `T'`.

## Idea

The proof takes the central character `χ` of `T'` from the Library
(`OperatorRealization.existsUnique_hasCentralCharacter`, which needs only irreducibility). It
then shows that each factor of the product is a value of `χ`:

* at a real or complex place `v`, the scalar of `-1` is `χ(ε_v)`, where `ε_v` is the
  archimedean idele that is `-1` at `v` and `1` at the other infinite places;
* at `v ∈ S`, `ζ_v = χ(ι_v(-1))`, where `ι_v(-1)` is the idele that is `-1` at `v` and `1`
  elsewhere;
* at the finite places outside `S`, `χ` is trivial on the integral units.

The idele `-1 ∈ F^×` is the product of the `ε_v`, of the `ι_v(-1)` for `v ∈ S`, and of the
integral unit idele that is `1` on `S` and `-1` off `S`. Since `χ` is trivial on `F^×`
(`centralIdeleCharacter_principal`), the product of the factors is `1`.

The proof does not use any eigenspace or Schur argument at the infinite places: the central
character already shows that `-1` at each infinite place acts on `T'.Space` by a scalar, so
the `if` in the definitions of `realMinusOneScalar` and `complexMinusOneScalar` takes its
scalar branch.

## The Lean proof

The module is in the namespace `Langlands.Global.RankinSelbergGlobal.CentralSign`, except for
the main theorem.

### Functions of a realization determined by their values

* `eq_smul_of_evaluate`: in an operator realization, if the function of `g` is `c` times the
  function of `f` at every point, then `g = c • f`. It uses the injectivity of
  `toContinuous` and of `toContinuousMap`.
* `smul_cancel`: if `a • f₀ = b • f₀` and the function of `f₀` does not vanish at some point,
  then `a = b`.
* `local_eq_smul_of_evaluate`: the same as `eq_smul_of_evaluate`, for a local realization at a
  finite place.

### Scalar ideles at the infinite places

* `placeSign w` is the unit `Pi.mulSingle w (-1)` of the infinite adeles: `-1` at `w` and `1`
  at the other infinite places.
* `prod_placeSign` shows that the product of all `placeSign w` is `-1`
  (`Finset.univ_prod_mulSingle`). `prod_real_mul_prod_complex_placeSign` splits this product
  into the real and the complex places (`Fintype.prod_subtype_mul_prod_subtype`, with complex
  places identified as the places that are not real).
* `scalar_infiniteIdelesInclusion`: the adelic scalar matrix of the image of an archimedean
  idele `z` is the image under `AdelicGL.ofInfinite` of the archimedean scalar matrix of `z`.
  The proof compares entries.
* `realPlaceCompactInclusion_neg_one` and `complexPlaceCompactInclusion_neg_one`: the element
  `-1` of the compact group at a real (orthogonal) or complex (unitary) place `v`, embedded in
  `GL_n` of the infinite adeles, is the scalar matrix of `placeSign v`. Both sides are compared
  through the injective coordinate map `archimedeanGLCoordinates`, using the Library's
  coordinate formulas `realMatrix_realPlaceCompactInclusion`,
  `complexMatrix_realPlaceCompactInclusion`, `realMatrix_complexPlaceCompactInclusion` and
  `complexMatrix_complexPlaceCompactInclusion`, and checking each place and entry.
* `ofInfinite_realPlaceCompactInclusion_neg_one` and
  `ofInfinite_complexPlaceCompactInclusion_neg_one` combine the two previous facts: the adelic
  image of that `-1` is `AdelicGL.scalar` of the idele `infiniteIdelesInclusion (placeSign v)`.

### The local component at a finite place

* `generalLinear_scalar_neg_one`: the local scalar matrix of `-1` is `-1`.
* `ofFinite_localInclusion_neg_one`: the adelic image of the local element `-1` at `v` is the
  scalar matrix of the idele `finiteIdeleInclusion v (-1)`
  (`AdelicGL.scalar_finiteIdeleInclusion`).

### Density: integral units outside `S`

* `integralUnitIdeles_mem_of_units` is a variant of the Library's
  `IdeleDensity.integralUnitIdeles_mem`. Let `H` be a closed subgroup of the ideles. Assume
  `H` contains the integral unit group at every finite place outside `S`. Then `H` contains
  every integral unit idele that is `1` on `S`. The Library version assumes the whole local
  unit group outside `S`; here only the integral units are available. The proof is the same
  density argument. The preimage of `H` under the continuous map `integralUnitIdeles` is
  closed. Every basic neighbourhood of `u` in the product topology fixes finitely many
  coordinates `T`, and contains the finite product `∏_(v ∈ T) Pi.mulSingle v (u v)`. That
  product lies in the preimage, because its factors at `v ∈ S` are trivial and the others lie
  in `H` by assumption.
* `centralIdeleCharacter_integralUnitIdeles`: `χ` is trivial on every integral unit idele `u`
  that is `1` on `S`. Apply the previous lemma to the closed subgroup
  `T.realization.centralCharacterSubgroup 1`. Its hypothesis is the Library's
  `CuspidalOperatorRealization.finiteIdeleInclusion_units_mem_centralCharacterSubgroup` with
  the trivial Hecke character, which uses `v ∉ P.exceptional` (from `P.exceptional ⊆ S`) and the
  spherical vector at `v`. So `u` acts trivially. Comparing with the central character formula
  `centralCharacter_evaluate` at a point where some function of `T` does not vanish
  (`exists_evaluate_ne_zero`) gives `χ(u) = 1`.

### The scalars at the infinite places and at the places of `S`

* `realPlace_neg_one_apply` and `complexPlace_neg_one_apply`: the element `-1` at a real or
  complex place `v` acts on `T.realization.Space` by `χ(infiniteIdelesInclusion (placeSign v))`.
  By `evaluate_realPlaceCompactRepresentation` (or its complex form), the function of the
  translate at `x` is the function of `f` at `x · ofInfinite(-1)`. The previous section
  rewrites `ofInfinite(-1)` as a scalar matrix. Scalar matrices commute with `x`
  (`AdelicGL.scalar_commute`), and `centralCharacter_evaluate` gives the factor. To keep
  elaboration fast, this step is an explicit `congrArg`/`Eq.trans` chain, not a `rw`.
* `realMinusOneScalar_eq` and `complexMinusOneScalar_eq`: the previous lemma supplies the
  hypothesis of `realMinusOneScalar_spec` (or `complexMinusOneScalar_spec`), so `-1` acts by
  `realMinusOneScalar T v`. Comparing the two actions on a vector `f₀` whose function does not
  vanish somewhere (`smul_cancel`) gives `realMinusOneScalar T v = χ(placeSign v)`, and the same
  for complex places.
* `localComponent_neg_one_apply`: on the local component `P.localComponent v` at a finite place
  `v`, the element `-1` acts by `χ(finiteIdeleInclusion v (-1))`. The local component has
  central character `χ`, because it lies inside the realization (`localComponent_le_image`).
  The computation is the same as at the infinite places, with
  `LocalRealization.evaluate_representation`, `ofFinite_localInclusion_neg_one`,
  `AdelicGL.scalar_commute` and `LocalRealization.centralCharacter_evaluate`.

### The idele identity

`diagonalUnits_neg_one_eq`: the principal idele `-1` equals

`infiniteIdelesInclusion(-1) · ∏_(v ∈ S) finiteIdeleInclusion v (-1) · integralUnitIdeles(u_S)`,

where `u_S` is `1` on `S` and `-1` off `S`. The proof uses the idele extensionality lemma
`IdeleDensity.idele_ext`. It compares the archimedean part (`infPart`) and each finite
coordinate (`coord w`), using the Library's formulas for `infPart` and `coord` of the three
kinds of ideles. At a finite place `w`, the product over `S` contributes `-1` exactly when
`w ∈ S`, and the integral unit idele contributes `-1` exactly when `w ∉ S`.

### The main theorem

`archimedeanCentralSign` does the following.

1. It takes the central character `χ` of `T'` from `existsUnique_hasCentralCharacter`.
2. It applies `χ` to `diagonalUnits_neg_one_eq S`. With `centralIdeleCharacter_principal` and
   `centralIdeleCharacter_integralUnitIdeles`, this gives
   `χ(infiniteIdelesInclusion(-1)) · χ(∏_(v ∈ S) ι_v(-1)) = 1`.
3. For `v ∈ S`, it shows `ζ_v = χ(ι_v(-1))` with `RankinSelberg.HasModelMinusOneScalar.unique`
   (the functional `ℓ` is nonzero). It remains to check that `χ(ι_v(-1))` is also a minus-one
   scalar of the model of `ℓ`. A model function has the form `g ↦ ℓ(σ_v(g) y)`. Then
   `σ_v((-1) g) y = σ_v(-1)(σ_v(g) y) = χ(ι_v(-1)) · σ_v(g) y` by
   `localComponent_neg_one_apply`, and `ℓ` is linear.
4. It writes `infiniteIdelesInclusion(-1)` as the image of
   `(∏_(v real) placeSign v) · (∏_(w complex) placeSign w)`
   (`prod_real_mul_prod_complex_placeSign`). It then uses that `χ ∘ infiniteIdelesInclusion` is
   multiplicative.
5. It rewrites each factor of the target product with `realMinusOneScalar_eq`,
   `complexMinusOneScalar_eq` and step 3, and concludes with step 2.

## Relation to the literature

Cogdell's argument (p.220) uses the product formula for the central character, `ω'(−1) = 1`,
and the triviality of `ω'_v(−1)` at the unramified places. The Lean proof follows this
argument. The product formula is `centralIdeleCharacter_principal`. Triviality at the unramified
places comes from the Library's statement that integral unit scalars fix the spherical vectors
of `T'` (`finiteIdeleInclusion_units_mem_centralCharacterSubgroup`), together with the density
lemma above, which is needed because infinitely many places lie outside `S`. The local scalars
at the infinite places and at the places of `S` are identified with values of the global
central character. This is how they enter the formula.
