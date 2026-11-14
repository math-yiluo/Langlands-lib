# Conjugation invariance of the Plancherel density

Worker 5. The module
`Langlands.Representation.Plancherel.RationalPlancherelDensityConjugation`
states the transport form of `μ(sω) = μ(ω)` for the Library's density
`plancherelDensity` as the target `PlancherelDensityConjugationStatement`.
It proves that the conjugation target for the canonical scalar `j_P`,
`ConditionalDynamicOppositeConjugationScalarStatement`, implies it. Neither
target is proved here.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082, registered as `waldspurger-2003-plancherel`, PDF
SHA256 `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.

- V.2, printed p.292 / PDF p.58: `μ(ω) = j(ω)⁻¹ ∏_α γ(M_α|M)²`.
- Lemma V.2.1, printed p.292 / PDF p.58, third item: `μ(sω) = μ(ω)` for
  `s ∈ W^G`. The proof (printed p.293 / PDF p.59) cites IV.3 (2), (3), (5)
  and (6).
- IV.3 (3), printed p.286 / PDF p.52: `j(wπ) = j(π)` for `w ∈ W^G`.

## Provenance

Derived. In the Library, `plancherelDensity i ζ … K … A …` is
`fieldConstant (plancherelDensityConstant i ζ K hK) * j_P⁻¹` for
`χ = ζ ≫ i`, with `j_P = conditionalCanonicalRationalScalar χ … K … A …`
(module `RationalPlancherelDensity`). For a rational point `g`, the
conjugate data are the torus `innerConjugate i g = i ≫ Int(g)` (module
`RationalPlancherelConstantConjugation`), a compact open `K₁` equal to
`gKg⁻¹`, and the representation `gA = conjugateRepresentation χ g A`
(module `DynamicOppositeConjugationScalar`). The identity is stated after
transport along `Int(g)` on the parameter group, as in the conjugation
target: `μ(gA ⊗ (z ∘ Int(g)⁻¹)) = μ(A ⊗ z)`. For `s ∈ W^G` with a
representative `g ∈ K`, take `K₁ = K`.

The two factors are handled separately. The scalar uses the assumed
conjugation target. The constant uses
`RationalPlancherelDensity.plancherelDensityConstant_eq_of_conjugation`
(module `RationalPlancherelConstantConjugation`), which is proved.

## The target

`PlancherelDensityConjugationStatement` quantifies over a nonarchimedean
local field `F`, an affine group scheme `G` of locally finite type, a
commutative group scheme `T` with `i : T → G` and a cocharacter `ζ` of `T`
(`χ = ζ ≫ i`), the premises `hRefl`, `hCST`, `hG : IsConnectedReductive G`,
a rational point `g`, a compact open `K` with `G = P K` and `G = P̄ K`, and
a smooth representation `A` of `M(F)`. It takes:

- conditional data `p`, `q`, `DForward`, `DReverse`, `D`, `hi` of the
  density for `(i, ζ, K, A)`, as taken by `plancherelDensity`, with the
  three sets open;
- a compact open `K₁` with `conjugateCompact g K = K₁`, proofs of its
  compactness and of `G = gPg⁻¹ K₁ = gP̄g⁻¹ K₁` for the cocharacter
  `ζ ≫ innerConjugate i g`, and independent conditional data `p'`, `q'`,
  `DForward'`, `DReverse'`, `D'`, `hi'` for
  `(innerConjugate i g, ζ, K₁, gA)`, `gA = conjugateRepresentation χ g A`.

Its conclusion is

```
plancherelDensity (innerConjugate i g) ζ … K₁ … gA p' q' … hi'
  = rationalUnramifiedFunctionFieldEquiv … (parameterConjugationIso χ g)
      (plancherelDensity i ζ … K … A p q … hi).
```

`gA` is a representation of `levi ((ζ ≫ i) ≫ Int(g))` and
`parameterConjugationIso χ g` has target `parameterScheme ((ζ ≫ i) ≫ Int(g))`.
Both are used for the cocharacter `ζ ≫ (i ≫ Int(g))`, which is the same
cocharacter up to definitional unfolding of composition.

## Results

- `conditionalDynamicOppositeConjugationScalar_of_heq`. Assume
  `ConditionalDynamicOppositeConjugationScalarStatement`. Its conclusion
  then holds for conjugate data formed with any cocharacter `χ'` with
  `hχ : χ ≫ Int(g) = χ'`, any representation `A'` of `levi χ'` with
  `HEq (conjugateRepresentation χ g A) A'`, any isomorphism
  `e : parameterScheme χ ≅ parameterScheme χ'` with
  `HEq (parameterConjugationIso χ g) e`, and any compact open `K₁` with
  `conjugateCompact g K = K₁`. The proof substitutes the equalities and
  applies `conditionalDynamicOppositeConjugationScalar_of_eq`. It is needed
  because `ζ ≫ (i ≫ Int(g))` and `(ζ ≫ i) ≫ Int(g)` are equal only by
  associativity. They are definitionally equal, but checking this inside
  the types of the continuation data exceeds the elaborator's limits.
- `fieldConstant_conjugation`: the transport
  `rationalUnramifiedFunctionFieldEquiv … (parameterConjugationIso χ g)`
  sends `fieldConstant i ζ hG c` to `fieldConstant (innerConjugate i g) ζ hG c`
  (`rationalUnramifiedFunctionFieldEquiv_constant`).
- `plancherelDensity_conjugation_of_conjugationScalar`. Assume `hconj`, the
  conjugation target. Take
  conditional data of the canonical scalar for `(χ, K, A)`, as taken by
  `plancherelDensity i ζ …`. Take independent conditional data for
  `(ζ ≫ innerConjugate i g, K₁, gA)` with `hK₁ : conjugateCompact g K = K₁`.
  Then

  ```
  plancherelDensity (innerConjugate i g) ζ … K₁ … gA p' q' … hi'
    = rationalUnramifiedFunctionFieldEquiv … (parameterConjugationIso χ g)
        (plancherelDensity i ζ … K … A p q … hi).
  ```

  The proof applies the previous result with `χ' = ζ ≫ (i ≫ Int(g))`,
  `hχ = Category.assoc`, `A' = gA` and `e = parameterConjugationIso χ g`.
  It rewrites the constant by `plancherelDensityConstant_eq_of_conjugation`
  and uses that the transport is a ring isomorphism fixing constants.
- `plancherelDensityConjugation_of_conjugationScalar`: the conjugation
  target for `j_P` implies `PlancherelDensityConjugationStatement`, by the
  previous result.

## Intended use

With a proof of the conjugation target and a Weyl representative `g ∈ K`,
this gives the third item of Lemma V.2.1 in the Library's parametrization.
Comparing the result with the density of the original Levi `M`, through
`s·M = M` and IV.3 (1) for a change of parabolic, is a separate step.

## Axioms

The proved results use only `propext`, `Classical.choice` and `Quot.sound`.
The target is a `def … : Prop` and introduces no axioms.
