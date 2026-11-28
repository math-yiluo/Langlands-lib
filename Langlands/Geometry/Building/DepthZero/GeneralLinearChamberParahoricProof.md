# Proof: chamber parahorics of `GL_N` are the conjugates of the standard Iwahori subgroup

Module `Langlands.Geometry.Building.DepthZero.GeneralLinearChamberParahoricProof`.

The theorem `Langlands.Geometry.Building.generalLinearChamberParahoric` proves
`Langlands.Geometry.Building.GeneralLinearChamberParahoricStatement` at every universe `u`: for
a nonarchimedean local field `F`, every `N` and every `D : KPBuildingDatum` of `GL_N` over `F`
with `D.SatisfiesGroupAxioms`, with `I = generalLinearIwahoriPoints F N` the standard Iwahori
subgroup,

- for every chamber `C` of the reduced building, `D.parahoric C = g I g⁻¹` for some
  `g ∈ G(F)`;
- for every `g ∈ G(F)` there is a chamber `C` with `D.parahoric C = g I g⁻¹`.

It adds no premise.

## Proof

1. **Transport.** As for vertices, the maximal split torus of `D` is conjugate to the diagonal
   torus by some `g₀` (`maximalSplitTorusConjugacy`), and transporting `D` along the inner
   automorphism of `g₀` gives data `P' = D.base.basedTransport σ _ hσ` with torus the diagonal
   torus satisfying the one-group axioms (`KPBuildingDatum.SatisfiesGroupAxioms.basedTransport`),
   in particular Axiom 4.1.8 (2). On rational points the inner automorphism of `g₀` is
   conjugation by `g₀` (`comp_innerIso_hom`, `constantPoint_self`).
2. **A point on no root hyperplane.** Let `x₀` be a point of the apartment of `D` on no root
   hyperplane and `x₁` its image in the apartment of `P'` (`basedApartmentEquiv`); `x₁` lies on
   no root hyperplane of `P'` (`transportedRoots_basedApartmentEquiv`,
   `AffineRootSystem.affineFunctionalTransport_apply`). Its root values are `y_k − y_l` with no
   integral difference (`exists_rootValue_eq_sub`, `forall_affineRoot_ne_zero_iff`), so
   `exists_floor_perm_of_forall_ne_intCast` gives `a` and `π`, and
   `nonnegativeRootSubgroup_singleton_eq_of_chamber` gives
   `P'.nonnegativeRootSubgroup {x₁} = (d m) I (d m)⁻¹`. By Axiom 4.1.8 (2) for `{x₁}` this is
   the group of elements of `G(F)^0` fixing the image of `x₁`. Conjugation by `g₀` carries the
   elements of `G(F)^0` fixing the image of `x₀` onto it
   (`ValuationBuildingData.map_pointwiseFixer_basedTransport`,
   `ParahoricBuildingData.basedTransport_zeroSubgroup`, `basedBuildingEquiv_apartmentMap`), so
   they form `c I c⁻¹` with `c = g₀⁻¹ d m` (`ParahoricBuildingData.map_conj_map_conj`).
3. **The parahoric of a translated chamber.** For a facet `C` with
   `C.val = h · (facet of x₀)`, `D.parahoric C` is the pointwise fixer of `C.val` intersected
   with `G(F)^0` (`KPBuildingDatum.parahoric_eq_pointwiseFixer_inf`, Axiom 4.1.20), which is
   `h` times the elements of `G(F)^0` fixing the facet of `x₀`, conjugated
   (`ParahoricBuildingData.pointwiseFixer_smul_image_inf_zeroSubgroup`). These are the elements
   of `G(F)^0` fixing `x₀`
   (`ParahoricBuildingData.zeroFixer_facet_eq_nonnegativeRootSubgroup_singleton` together with
   Axiom 4.1.8 (2) for `{x₀}`), so `D.parahoric C = (h c) I (h c)⁻¹` by step 2.
4. **Every chamber.** A chamber of the reduced building is `h` times the image of a chamber of
   the apartment, the facet of a point `x₀` on no root hyperplane
   (`ValuationBuildingData.IsChamber`, `AffineRootSystem.IsChamber`); step 3 applies.
5. **Every conjugate.** The apartment of `P'` has a point `x₁` with root values
   `y_k − y_l`, `y_k = k / (N + 1)` (`exists_forall_sub_ne_intCast`,
   `exists_rootValue_eq_sub_of`), on no root hyperplane; its preimage `x₀` lies on no root
   hyperplane of `D`. With `c` from step 2 and `h = g c⁻¹`, the translate of the facet of `x₀` by
   `h` is a chamber of the reduced building (`AffineRootSystem.IsChamber.isFacet`), and step 3
   gives `D.parahoric C = g I g⁻¹`.

The proof uses neither the concrete `GL_N` Cartan statement nor a lattice-chain description of
the building: the parahoric is computed from Axioms 4.1.8 (2) and 4.1.20 of the data and the
valuations of the root datum of the diagonal torus.

## Source

Tasho Kaletha and Gopal Prasad, *Bruhat–Tits Theory: A New Approach*, Cambridge University
Press, 2023 (PDF page = printed page + 31): Definition 7.4.5 (Iwahori subgroups as chamber
parahorics) and §15.1, 15.1.33 (printed p. 524, PDF p. 555) for `GL(X)`. Literature ID
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`. The Lean proof follows the
route described above rather than the source's description by lattice chains.
