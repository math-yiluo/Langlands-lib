# Proof: vertex parahorics of `GL_N` are the conjugates of `GL_N(𝒪_F)`

Module `Langlands.Geometry.Building.DepthZero.GeneralLinearVertexParahoricProof`.

The theorem `Langlands.Geometry.Building.generalLinearVertexParahoric` proves
`Langlands.Geometry.Building.GeneralLinearVertexParahoricStatement` at every universe `u`: for a
nonarchimedean local field `F`, every `N` and every `D : KPBuildingDatum` of `GL_N` over `F`
with `D.SatisfiesGroupAxioms`, with `K = GL_N(𝒪_F)` the integral points of the standard model,

- for every vertex facet `x = {y}` of the reduced building, `D.parahoric x = g K g⁻¹` for some
  `g ∈ G(F)`;
- for every `g ∈ G(F)` there is a vertex facet `x` with `D.parahoric x = g K g⁻¹`.

It adds no premise.

## Auxiliary results (namespace `Langlands.Geometry.Building.GeneralLinearParahoric`)

- `map_innerIso_hom_apply`: on rational points, the inner automorphism of the group scheme
  given by `g` is conjugation by `g` (`comp_innerIso_hom`, `constantPoint_self`).
- `pointwiseFixer_smul_singleton_inf_zeroSubgroup`: for parahoric building data `B`, the
  elements of `G(F)^0` fixing `g · z` are the `g`-conjugates of those fixing `z`, since `G(F)^0`
  is normal (`ParahoricBuildingData.normal_zeroSubgroup`).

## Proof

1. **Transport.** The maximal split torus of `D` is conjugate to the diagonal torus by some
   `g₀` (`maximalSplitTorusConjugacy`). Transporting `D` along the inner automorphism of `g₀`
   gives data `P' = D.base.basedTransport σ _ hσ` whose torus is the diagonal torus; they
   satisfy the one-group axioms (`KPBuildingDatum.SatisfiesGroupAxioms.basedTransport`), in
   particular Axiom 4.1.8 (2) (`hasZeroFixerGenerators`).
2. **The parahoric of a translated vertex.** Let `x₀` be a vertex of the apartment of `D` and
   `x₁` its image in the apartment of `P'` (`basedApartmentEquiv`), a vertex for the affine roots
   of `P'` (`transportedRoots_basedApartmentEquiv`,
   `AffineRootSystem.isVertex_transportedRoots_iff`). Its root values are `y_k − y_l` with
   integers `y_k` (`exists_intCast_sub_of_isVertex`), so with `d = diag(ϖ^{−y_k})`
   `P'.nonnegativeRootSubgroup {x₁} = d K d⁻¹`
   (`nonnegativeRootSubgroup_singleton_eq_of_intCast_sub`). By Axiom 4.1.8 (2) for the bounded
   set `{x₁}`, this is `P'.zeroFixer {x₁}`, the elements of `G(F)^0` fixing the image of `x₁`.

   For a facet `x` with `x.val = {h · x₀}`, `D.parahoric x` is the pointwise fixer of
   `{h · x₀}` intersected with `G(F)^0` (`KPBuildingDatum.parahoric_eq_pointwiseFixer_inf`,
   Axiom 4.1.20). Conjugation by `g₀` carries the pointwise fixer to the pointwise fixer of the
   image point (`ValuationBuildingData.map_pointwiseFixer_basedTransport`), which is
   `h′ · x₁` with `h′ = g₀ h g₀⁻¹` (`basedBuildingEquiv_smul`, `basedBuildingEquiv_apartmentMap`),
   and `G(F)^0` to `G(F)^0` of `P'` (`ParahoricBuildingData.basedTransport_zeroSubgroup`). By
   `pointwiseFixer_smul_singleton_inf_zeroSubgroup` the image is `h′ (d K d⁻¹) h′⁻¹`, so
   `D.parahoric x = (h c) K (h c)⁻¹` with `c = g₀⁻¹ d`, which depends only on `x₀`
   (`ParahoricBuildingData.map_conj_map_conj`).
3. **Every vertex facet.** A vertex `y` of the reduced building is `h · x₀` with `x₀` a vertex
   of the apartment (`ValuationBuildingData.IsVertex`), so step 2 gives the first conjunct with
   `g = h c`.
4. **Every conjugate.** The apartment of `P'` has a point with all root values zero
   (`exists_rootValue_eq_zero`), a vertex by `isVertex_iff`; its preimage `x₀` is a vertex of
   the apartment of `D`. For `g ∈ G(F)`, with `c` from step 2 and `h = g c⁻¹`, the set
   `{h · x₀}` is a facet (the image of the facet `{x₀}`) whose point is a vertex, and step 2 gives
   `D.parahoric = g K g⁻¹`.

The proof uses neither the concrete `GL_N` Cartan statement nor a lattice description of the
building: the parahoric is computed from Axioms 4.1.8 (2) and 4.1.20 of the data and the
valuations of the root datum of the diagonal torus.

## Source

Tasho Kaletha and Gopal Prasad, *Bruhat–Tits Theory: A New Approach*, Cambridge University
Press, 2023 (PDF page = printed page + 31): §15.1 and 15.1.33 (printed p. 524, PDF p. 555), the
vertex parahorics of `GL(X)` are the conjugates of `GL_N(𝒪)`. Literature ID
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`. The Lean proof follows the
route described above rather than the source's description by lattices.
