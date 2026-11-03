# Points of a torus over a splitting field

Module `Langlands.GroupScheme.Torus.CocharacterSplitting`, namespace
`Langlands.GroupScheme.CocharacterSplitting`. It imports
`Langlands.GroupScheme.Torus.CocharacterDatum` and uses
`CharacterRestrictionFiniteIndex.rationalCharacters_ext_affine` from the
Library module `Langlands.GroupScheme.Rational.CharacterRestrictionFiniteIndex`.

Setting: `k` is a field, `K` a field extension of `k`, `Z` a commutative group
scheme over `Spec k`, `I` a finite type, and
`e : (GroupScheme.baseChange (baseMap K)).obj Z.toGrp ≅ splitTorus (Spec K) I`
a splitting of `Z` over `K`, where `baseMap K : Spec K ⟶ Spec k`. Points of `Z`
over a `k`-algebra `S` are the `Lie.AffinePoints Z.toGrp S`. Cocharacter data
(`IsDatum`, `IsMult`, `monomial`, `expMap`) are those of
`Langlands.GroupScheme.Torus.CocharacterDatum`.

## Definitions

- `precompEquiv ε`: precomposition with an isomorphism `ε : T' ≅ T` of test
  objects, as a group isomorphism on points of a group scheme.
- `baseMap K`: `Spec K ⟶ Spec k`.
- `testScheme K S`: the spectrum of a `K`-algebra `S`, over `Spec K`;
  `testIso K S` identifies its image over `Spec k` with the spectrum of `S`
  as a `k`-algebra (for a scalar tower `k → K → S`).
- `pointsEquiv e S`: for a `K`-algebra `S`, the group isomorphism
  `Z(S) ≃* (I → Sˣ)` given by the splitting: pass to points of the base
  change `Z_K` (`baseChangePointsEquiv`), apply `e` (`isoPointsEquiv`), and
  read off the coordinates of the split torus
  (`splitTorus.algebraPointsEquiv`).
- `weight e χ : I → ℤ`: the exponent vector of a character `χ` of `Z` in the
  splitting, namely `splitTorus.characterLatticeEquiv` applied to the base
  change of `χ` composed with `e.inv`.
- `splitPoint e c`: for `c : I → Λ`, the point of `Z` over `K[Λ]` whose split
  coordinates are the monomials `X^(c i)`.

## Statements

- `baseChangePointsEquiv_symm_naturality`: the inverse of the pullback point
  equivalence is natural in the test object.
- `testIso_hom_comp_map`: compatibility of `testIso` with `K`-algebra maps.
- `pointsEquiv_naturality`: for a `K`-algebra map `f : S → S'`,
  `pointsEquiv e S' (f_* x) = fun i => f (pointsEquiv e S x i)`.
- `characterValue_eq`: for a `K`-algebra `S`,
  `χ(x) = ∏ᵢ (pointsEquiv e S x i) ^ (weight e χ i)`
  (`splitTorus.exponentValue`).
- `characterValue_equivCharacterLattice`: the value of a rational character,
  read through `rationalCharacters.equivCharacterLattice`, is its evaluation
  `characterEval` transported along `Γ(Spec S) ≅ S` (true by definition).
- `eq_zero_of_weight_eq_zero` (`Z` affine): a rational character of weight
  zero in the splitting is zero.
- `restrictScalars_mapDomainAlgHom`, `units_map_mapDomainAlgHom_monomial`:
  exponent changes on `K[Λ]` and their effect on monomials.
- `pointsEquiv_expMap_splitPoint`, `isMult_splitPoint`,
  `characterValue_splitPoint` (`χ(splitPoint e c) = X^(∑ᵢ weight e χ i • c i)`),
  `isDatum_splitPoint`: `splitPoint e c` is a cocharacter datum for `χ` of
  weight `∑ᵢ weight e χ i • c i`.
- `exists_isDatum` (`Z` affine): every nonzero rational character `χ` of `Z`
  has a cocharacter datum of some nonzero weight `m : PUnit → ℤ` over
  `K[PUnit → ℤ]`.
- `pow_affineMap_eq`: if a `K`-algebra map `φ : S → S` satisfies
  `s ^ n = (φ s) ^ n` for all `s`, then `y ^ n = (φ_* y) ^ n` for every point
  `y` of `Z` over `S`.
- `pow_affineMap_eq_of_tensor` (`Z` affine; Frobenius on points): for a
  `k`-algebra map `g : A → A` such that `x ^ n = ((id ⊗ g) x) ^ n` for all
  `x : K ⊗[k] A`, every point `u` of `Z` over `A` satisfies
  `u ^ n = (g_* u) ^ n`.

## Proofs

- `pointsEquiv_naturality` combines `testIso_hom_comp_map`,
  `baseChangePointsEquiv_symm_naturality` and
  `splitTorus.algebraPointsEquiv_naturality`.
- `characterValue_eq` writes `χ` restricted to the split torus as the
  character with exponent vector `weight e χ`
  (`splitTorus.characterValue_characterLatticeEquiv_symm`), cancels
  `e.hom ≫ e.inv`, and compares the values in `𝔾_m` over `K` and over `k`
  through `Gm.pointsEquiv_baseChangeIso_hom`, `Gm.baseChangeUnitsEquiv_apply`,
  `baseChangePointsEquiv_comp` and `Gm.pointsEquiv_naturality`.
- `eq_zero_of_weight_eq_zero`. By `rationalCharacters_ext_affine` it suffices
  that `χ` is `1` on every point `y` over every `k`-algebra `B`. Move `y` to
  `K ⊗[k] B` along the injective map `includeRight`; there
  `characterValue_eq` with weight `0` gives value `1`, and
  `characterValue_affineMap` with injectivity of `includeRight`
  (`Algebra.TensorProduct.includeRight_injective`) brings this back to `B`.
- Split points. Exponent changes act on split coordinates monomially
  (`pointsEquiv_naturality`), which gives multiplicativity coordinatewise from
  `monomial_add`, and `characterValue_eq` computes the value.
- `exists_isDatum`. Since `χ ≠ 0`, its weight is nonzero by
  `eq_zero_of_weight_eq_zero`; pick `j₀` with `weight e χ j₀ ≠ 0` and take
  `c = Pi.single j₀ 1`, so the weight of `splitPoint e c` is the constant
  function `weight e χ j₀ ≠ 0`.
- `pow_affineMap_eq` applies `pointsEquiv e S`: in coordinates the claim is
  `t ^ n = (φ t) ^ n` for units `t`, which is the hypothesis.
- `pow_affineMap_eq_of_tensor` moves the points to `K ⊗[k] A` along the
  injective `includeRight`, uses
  `Algebra.TensorProduct.map_restrictScalars_comp_includeRight` to identify
  `includeRight ∘ g` with `(id ⊗ g) ∘ includeRight`, and applies
  `pow_affineMap_eq` to the `K`-algebra map `id ⊗ g`.

## Provenance

Internal. These are the standard facts that a split torus has points
`(Sˣ)^I` and characters `t ↦ ∏ tᵢ^{mᵢ}`, transported to a torus split over
`K`; here they are derived from the Library's `splitTorus` and base-change
API. The Frobenius-on-points
lemma is an auxiliary step designed by Worker 1001 for torus cocharacter
detection in task 6d0882ee; it supplies the hypothesis of
`IsDatum.exists_of_pow_mem_range`
(`Langlands.GroupScheme.Torus.CocharacterInseparableDescent`).
