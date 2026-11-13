# Equivariant building isomorphisms across a field extension

This internal module assembles the proof of Kaletha–Prasad Axiom 4.1.17
(compatibility with isomorphisms) for the valuation-quotient buildings of
supplied `ValuationBuildingData`. It works over a field extension `F₁ → F₂` of
nonarchimedean local fields and takes four explicit hypotheses. The final
theorem `isomorphismCompatibilityAxiom` (module
`IsomorphismCompatibilityAxiomProof`) discharges all four for a valued-field
isomorphism `σ : F₁ ≃+* F₂`.

## Provenance

The motivating source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), Axiom 4.1.17, printed p.162 (PDF p.193), read with the authors'
corrections of 1 November 2024. Registered source IDs:
`kaletha-prasad-2023-bruhat-tits-new-approach`,
`kaletha-prasad-2024-corrections`. The theorem below is a derived intermediate
result, not a statement from the source. Its route through chart isomorphisms
is specific to this formalization.

## Declarations

- `KPApartmentData.IsChartIso.exists_trans`: if chart isomorphisms
  `D₁ → D₂` along `θ₁` and `D₂ → D₃` along `θ₂` exist, then one `D₁ → D₃`
  along `θ₂ ∘ θ₁` exists. This is the published `IsChartIso.trans` with the
  base points, apartment maps and building maps packed into existentials.
- `ValuationBuildingData.exists_isEquivariantBuildingIso_of_fieldExtension`.
  Let `[Algebra F₁ F₂]`, `b = Spec F₂ → Spec F₁`, `f_G : G₁ ×_{F₁} F₂ ≅ G₂`,
  and let `B₁`, `B₂` be valuation data for `G₁`, `G₂`. Assume:
  - `horder`: `localFieldOrder F₂ (t_{F₂}) = localFieldOrder F₁ t` for all
    `t ∈ F₁ˣ`;
  - `hθ`: `rationalExtend F₁ F₂ G₁ : G₁(F₁) → G₁(F₂)` is bijective;
  - `hN`: `g_{F₂}` normalizes the base-changed torus `(B₁.i)_{F₂}` exactly when
    `g` normalizes `B₁.i`;
  - `hmax`: `(B₁.i)_{F₂}` is a maximal split torus.

  Then some `Φ : B₁.ReducedBuilding ≃ B₂.ReducedBuilding` is an
  `IsEquivariantBuildingIso` along `g ↦ f_G(g_{F₂})`, which is
  `(rationalPoints.map f_G.hom).comp (rationalExtend F₁ F₂ G₁)`.

## Proof of the main theorem

Write `i_K = (B₁.i)_{F₂}` and `S_K = (B₁.S)_{F₂}`.

1. **Conjugate onto `B₂`.** By `hmax` and `IsMaximalSplitTorus.comp_iso`,
   `i_K ≫ f_G` is a maximal split torus of `G₂`. The published
   `maximalSplitTorusConjugacy` gives `g ∈ G₂(F₂)` and an isomorphism
   `σ_S : S_K ≅ B₂.S` with `i_K ≫ f_G ≫ Int(g) = σ_S ≫ B₂.i`. Put
   `F = f_G ≪≫ G₂.innerIso g`.
2. **Carry `B₂` to `i_K`.** Set `D_K = B₂.apartment.transport σ_S⁻¹ F⁻¹`
   (`KPApartmentData.transport`, `torusTransport_inverse_square`). Set
   `C_K = B₁.centralizer.baseChangeOfBasedIso B₂.centralizer σ_S F h`. This is
   the base-changed centralizer datum of module `CentralizerDatumBaseChange`.
   The published `IsOmegaCompatible.transport_basedIso` shows that `D_K`
   satisfies V6 for `C_K`.
3. **Integer orders.** `horder` and `IntegerValuation.order_normalized` give
   the same identity for the integer orders of the normalized valuations.
   `D_K' = D_K.reindexOrder …` moves `D_K` to the integer order, where it
   remains ω-compatible (`isOmegaCompatible_normalized`). The uniformizer has
   nonzero order (`SplitTorusValuation.uniformizerUnit`).
4. **Restrict and compare.** `R = IntegerValuation.fieldRestrictApartment … D_K'`
   is apartment data for `B₁.i`. It is ω-compatible with `B₁.centralizer` by
   `fieldRestrictApartment_isOmegaCompatible`, using bijectivity of `C_K`.
   The published `omegaCompatibleApartmentUniqueness` then gives
   `R.reindexOrder … = B₁.apartment`. `B₁.i` has opposite factor pairs by the
   published `rootRankOneFactorization`. `R` is also the literal field
   restriction `FR = KPApartmentData.fieldRestrict … D_K'` up to reindexing the
   order (`KPApartmentData.ext`, `reindexOrder_carrier`).
5. **Chain of chart isomorphisms.** These are chart isomorphisms
   (`KPApartmentData.IsChartIso`, module `ValuationBuildingChartIso`):
   - `B₁.apartment → reindex` and `R → reindex`, and `D_K' → reindex`:
     `isChartIso_reindexOrder`;
   - the equalities from step 4 and `reindexOrder_symm`:
     `exists_isChartIso_of_eq`;
   - `FR → D_K'` along `rationalExtend F₁ F₂ G₁`:
     `isChartIso_fieldRestrictBuildingEquiv` with `hθ` and `hN`;
   - `D_K → B₂.apartment` along `rationalPoints.map F.hom`:
     `exists_isChartIso_transport_symm`;
   - `B₂.apartment → B₂.apartment` along conjugation by `g⁻¹`:
     `IsChartIso.smul`.

   `exists_trans` composes them into one chart isomorphism
   `B₁.apartment → B₂.apartment`. Its homomorphism is
   `x ↦ g⁻¹ · F(x_{F₂}) · g`. Since `F(y) = g · f_G(y) · g⁻¹`
   (`comp_innerIso_hom`, `constantPoint_self`), it equals
   `x ↦ f_G(x_{F₂})`.
6. **Conclusion.** `g ↦ f_G(g_{F₂})` is surjective, by `hθ` and
   `isoPointsEquiv f_G`. The published `isEquivariantBuildingIso_of_isChartIso`
   turns the composite chart isomorphism into an equivariant building
   isomorphism.

The proof uses no common-apartment, AS 5 or availability hypothesis.
