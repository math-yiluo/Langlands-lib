# Proof: tangent and local cotangent dimensions at a rational point over a field

Author: Worker 254.

Module `Langlands.AlgebraicGeometry.FieldPointTangentLocalRegularityProof`.

```lean
theorem Langlands.Scheme.fieldPointTangentLocalRegularity :
    FieldPointTangentLocalRegularityStatement.{u}
```

The theorem proves the published statement
`Langlands.Scheme.FieldPointTangentLocalRegularityStatement` for an arbitrary
universe `u`, an arbitrary field `k`, an arbitrary `X : Over (Spec k)` locally
of finite type, and an arbitrary section `e`. It uses the published
`tangentSpaceAtPoint X e` with its `ModuleCat` scalar action, the actual stalk
`R = X.left.presheaf.stalk (e.left (closedPoint k))`, and Mathlib's
`IsLocalRing.CotangentSpace R` over `IsLocalRing.ResidueField R`. No hypothesis
is added. The statement pair and its import closure are unchanged.

## Implemented proof

Write `S = Spec k`, `pt = closedPoint k`, and `T = tangentSpaceAtPoint X e`.
The carrier of `T` is `Γ(tangentAtSection X e, ⊤)` by definition. The scalar
`c : k` acts as `(ΓSpecIso k).inv c • -`.

1. **Noetherian stalk.** `LocallyOfFiniteType.isLocallyNoetherian X.hom`
   applies over the Noetherian scheme `Spec k`, so `X.left` is locally
   Noetherian. Hence `R` is a Noetherian local ring (Mathlib instance), and
   `CotangentSpace R` is finite-dimensional over `ResidueField R`.
2. **One point.** `Spec k` has exactly one point (`PrimeSpectrum k` is
   `Unique`), so the bridge module applies.
3. **Tangent sections are point derivations.**
   `SectionPoint.tangentDerivationEquiv X e pt`, from
   `Langlands.AlgebraicGeometry.SectionTangentDerivations`, is an additive
   bijection (`tangentDerivationEquiv_add`):

   `T ≃ derivations (baseMap X.hom e.left pt) (e.left.stalkMap pt).hom`.

   `tangentDerivationEquiv_smul` shows that the `k`-action matches
   multiplication by `germ_⊤ ((ΓSpecIso k).inv c)` in `K = O_{S,pt}`. This map
   `k → K` is bijective, by `germ_bijective` and `ΓSpecIso`. Mathlib's
   `rank_eq_of_equiv_equiv` therefore gives `rank_k T = rank_K (derivations)`.
4. **Coefficients in `k`.** Write `τ := (stalkClosedPointIso k).commRingCatIsoToRingEquiv`.
   This is `τ : O_{S,pt} ≃+* k`, the same isomorphism used in Mathlib's
   `Scheme.stalkClosedPointTo`. `derivationsCongr τ` together with
   `derivationsCongr_smul` transports the derivations to coefficients in `k`,
   keeping the rank.
5. **The rational point.** The map `τ ∘ e.left.stalkMap pt ∘ baseMap` equals
   `(ΓSpecIso k).hom`, so it is bijective. The proof combines:
   - `stalkMap_baseMap`, which uses `e.left ≫ X.hom = 𝟙`;
   - Mathlib's `germ_stalkClosedPointIso_hom`.

   This is the hypothesis `hbij` of
   `Langlands.CommutativeAlgebra.PointDerivationCotangent`. That module's
   `rank_derivations hbij` identifies the rank with
   `rank (Dual (ResidueField R) (CotangentSpace R))`. Its `residueEquiv` gives
   the transport between the residue field of `R` and `k`, built from
   `ker π = m`.
6. **Dimensions.** `Module.dual_rank_eq` applies because the cotangent space
   is finite-dimensional. This gives
   `rank_k T = rank_{ResidueField R} (CotangentSpace R) < ℵ₀`.
   - `Module.rank_lt_aleph0_iff` gives `FiniteDimensional k T`.
   - Applying `Cardinal.toNat` gives the `finrank` equality.
7. **Regularity.** Take `g` with `finrank_k T ≤ g ≤ ringKrullDim R`. Rewrite
   `spanFinrank (maximalIdeal R)` as `finrank (CotangentSpace R)`
   (`spanFinrank_maximalIdeal_eq_finrank_cotangentSpace`, using that `R` is
   Noetherian), which equals `finrank_k T`. Then
   `IsRegularLocalRing.of_spanFinrank_maximalIdeal_le` gives regularity. That
   lemma uses Krull's bound `ringKrullDim R ≤ spanFinrank (maximalIdeal R)`
   internally.

## Relation to the statement's suggested route

The statement's Markdown lists the obligations that a proof must supply.
Each is supplied as follows.

- **Global sections of the internal dual on the one-point space.** Supplied by
  `localHomTopEquiv` together with the adjunction. The actual pullback is never
  computed.
- **Pullback and relative differential stalks.** Replaced by the
  pullback–pushforward adjunction, the universal property of the relative
  differential sheaf, and the skyscraper comparison into `e_* O_S`.
- **The rational-point cotangent comparison.** Supplied by `equivDual`, which
  uses the direct splitting by `constPart`. The naive cotangent complex
  argument of Stacks Tag 0B2E is not used.
- **Transport between `k` and the residue field.** Supplied by `germ_⊤`,
  `ΓSpecIso`, `stalkClosedPointIso` and `residueEquiv`.
- **Local Noetherianity and finite-dimensionality.** Supplied by step 1.

## Dependencies

Helper modules in this contribution:

- `Langlands.CommutativeAlgebra.PointDerivationCotangent`;
- `Langlands.AlgebraicGeometry.SectionTangentDerivations`.

Published Library modules, unchanged:

- `Langlands.AlgebraicGeometry.FieldPointTangentLocalRegularityStatement`;
- `PointTangentSpace`, `ModuleDual`, `RelativeDifferentials`;
- `RelativeDifferentialsUniversal`, for `relativeDifferentialsHomEquiv`.

Mathlib provides:

- `Scheme.Modules.pullbackPushforwardAdjunction`;
- `TopCat.Presheaf.germ_eq` and `exists_germ_eq`;
- `Scheme.Hom.germ_stalkMap_apply`;
- `stalkClosedPointIso` and `germ_stalkClosedPointIso_hom`;
- `LocallyOfFiniteType.isLocallyNoetherian`;
- `rank_eq_of_equiv_equiv`;
- `Module.dual_rank_eq` and `Module.rank_lt_aleph0_iff`;
- `IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace`;
- `IsRegularLocalRing.of_spanFinrank_maximalIdeal_le`.

The proof uses none of the Picard proofs `2eb8161a`, `9cd303c4`, `e689d392` or
`4ef972f8`. It makes no dual-number construction. It does not prove that regular
local rings are domains.

## Verification

`lean_check` in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` builds the
three modules with Lake with no errors and no warnings. The declaration
`Langlands.Scheme.fieldPointTangentLocalRegularity` is a theorem with universe
parameter `u` and axioms `propext`, `Classical.choice` and `Quot.sound` only.
There is no `sorry`, `admit` or new axiom.
