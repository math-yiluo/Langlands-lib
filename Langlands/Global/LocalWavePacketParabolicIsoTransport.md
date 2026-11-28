# Transport of the truncated limit along isomorphisms of parabolic subgroups

Module `Langlands.Global.LocalWavePacketParabolicIsoTransport`. It is a helper module for the
proof `Langlands.Global.truncatedWavePacketStandardization` and contains no statement of its own.
It shows that `TruncatedWavePacketPairLimit` (module `Langlands.Global.LocalWavePacketPairLimit`)
depends only on the images of the parabolic subgroups, their Levi subgroups and unipotent
radicals in `G`. The source `P` or the target `P'` may be replaced by an isomorphic group scheme
over `G`. The regularity predicate is then composed with the restriction of parameters along the
isomorphism.

## Setting

`jP : P₁ ≅ P` with `jP ≫ p = p₁`, and `δ : M₁ ≅ M` with `δ ≫ l = l₁ ≫ jP` (the Levi subgroups
correspond); the unipotent radicals have the same image in `G`. For the target, also
`π'₁ ≫ κ = jQ ≫ π'` for the Levi projections.

## Helper results

- `characterRestrict_adjointDeterminantCharacter_iso`,
  `parameterRestrict_modulusParameter_iso`, `parameterRestrict_halfModulusParameter_iso`: the
  determinant of the adjoint representation, hence `2ρ_P` and `ρ_P`, restricts along an
  isomorphism to that of the source (`characterRestrict_determinantCharacter_of_intertwining`
  applied to the conjugation actions).
- `map_levi_iso`, `parameterPower_levi_iso`, `modulusPower_levi_iso`: the points of `G(𝔸)` and
  the parameter powers of the two Levi subgroups correspond.
- `IsSquareIntegrableInducedForm.of_iso`: square integrable induced forms for `p` are square
  integrable induced forms for `p₁`. The invariance subgroups `U(𝔸)M(F)` agree
  (`parabolicQuotientSubgroup_eq_of_range_eq`), the split component equivariance is transported
  through `δ`, and the canonical measures on the quotients `M(F)A_M \ M(𝔸)` agree up to a
  positive scalar (`RestrictionSplitCentre.map_canonicalMeasure`).
- `realParameterRestrictIsoEquiv`, `parameterRestrict_imaginaryParameter`,
  `realWeylParameter_pullback_eq`, `parameterRestrict_id_apply`: restriction of real and complex
  parameters along isomorphisms, and its compatibility with `λ ↦ iλ` and with Weyl parameters.
- `IsWeylConjugation.comp_iso`, `IsWeylConjugation.iso_comp`: a Weyl conjugation `(w, c)`
  composed with an isomorphism of Levi subgroups over `G` is a Weyl conjugation.
- `inducedInnerProduct_levi_iso`: for functions invariant under `M(F)`, the induced inner product
  for `(p, l)` with the image of a Haar measure `μ₁` of `M₁(𝔸)` and the transported coordinates
  equals the induced inner product for `(p₁, l₁)` with `μ₁`. The integrand is
  `InducedInnerProductSesquilinear.kernel` (`kernel_levi_iso`), the quotient measures correspond
  (`LeftCosetSpace.measurePreserving_discreteQuotientMeasure`), and the choice of coset
  representatives does not matter (`LeftCosetSpace.out_mk_of_invariant`,
  `InducedInnerProductSesquilinear.kernel_rational_mul`).
- `IsIwasawaCompatibleMeasure.map_levi_iso`: the image of an Iwasawa-compatible Haar measure is
  Iwasawa-compatible, because the integrands of the two Iwasawa integration formulas agree
  pointwise.

## Transport theorems

- `TruncatedWavePacketPairLimit.of_iso_source`: the limit for `(p, l)` with regularity
  `Reg₁ ∘ (restriction along jP)` gives the limit for `(p₁, l₁)` with `Reg₁`. Given data for `p₁`,
  the same forms are square integrable for `p`; the coefficients `b`, continuations `E` and
  expansion coefficients are precomposed with the restriction `X^*(P) ⊗ ℂ ≃ X^*(P₁) ⊗ ℂ`; the
  real coordinates `e` are composed with the inverse restriction; Weyl representatives become
  `c ≫ δ`. Eisenstein series and intertwining operators agree
  (`IsIwasawaCompact.eisensteinSeries_eq_of_range_eq`,
  `IsIwasawaCompact.intertwiningOperator_eq_of_transport`), and so do the Weyl parameters
  (`weylParameter_parameterRestrict_eq`). The conclusion for the transported data is the
  required conclusion after rewriting these identities.
- `TruncatedWavePacketPairLimit.of_iso_target`: the analogous transport of the target `(p', l', π')`
  to `(p'₁, l'₁, π'₁)`. The Haar measure on `M'(𝔸)` is the image of the given one under `κ`, and
  the inner products agree by `inducedInnerProduct_levi_iso`.

## Provenance

The construction is internal: it records that the objects in Lapid, *On Arthur's asymptotic inner
product formula of truncated Eisenstein series* (2011), §§2, 8, depend only on the subgroups of
`G` and not on their presentation as group schemes over `G`. The inner product is the one of
`inducedInnerProduct` (Lapid §2) and the compatible measure that of `IsIwasawaCompatibleMeasure`
(Mœglin–Waldspurger I.1.13).
