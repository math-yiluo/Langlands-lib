# Abelian reduction from the proper closed fibre criterion

`Langlands.AbelianScheme.abelianReduction_of_properClosedFibre` derives
`Langlands.AbelianScheme.AbelianReductionStatement` from
`Langlands.AlgebraicGeometry.SmoothDvrProperClosedFibreStatement`, the
properness criterion for smooth, separated, quasi-compact schemes over a
discrete valuation ring with geometrically connected fibres and proper closed
fibre. The criterion is an explicit hypothesis of the theorem.

## Proof

Let `V` be a discrete valuation ring with fraction field `K` and residue field
`k`, and let `N` be the given Néron model of the abelian variety `B` over `K`,
with group scheme `G` over `Spec V`. Let `J ⟶ G_kbar` be the supplied relative
identity component of the geometric special fibre, where `kbar` is the
algebraic closure of `k`, and assume `J` is proper.

1. Relative identity component. `RelativeIdentityComponent.smoothExistence`
   gives an open subgroup `j : H ⟶ G` that is the relative identity component
   of `G`. It is smooth with geometrically connected fibres. It is separated,
   being open in the separated `G`. It is quasi-compact, being open in the
   noetherian space underlying `G`, which is of finite type over `V`.

2. Proper closed fibre. By `RelativeIdentityComponent.smoothBaseChange`, the
   base change of `j` to `kbar` is the relative identity component of the
   geometric special fibre. Uniqueness (`IsRelativeIdentityComponent.iso`)
   identifies it with `J`, so `H_kbar` is proper. The morphism
   `Spec kbar ⟶ Spec k` is faithfully flat and quasi-compact
   (`fieldExtension_fpqc`), and properness descends along it. Hence the
   pullback of `H` to `Spec k` is proper.

3. Properness of `H`. The criterion now applies to `H ⟶ Spec V`, so `H` is
   proper. With its group law, `H` satisfies the abelian scheme property
   bundle `GoodReductionJacobian.AbelianSchemePropertyBundle`.

4. Generic fibre. The generic fibre of `G` is isomorphic to `B`, so it is
   geometrically connected. By `RelativeIdentityComponent.smoothBaseChange`,
   the generic fibre of `j` is the relative identity component of the generic
   fibre of `G`, so it is an isomorphism
   (`IsRelativeIdentityComponent.isoOfGeometricallyConnected`).

5. Néron extension. The Néron mapping property of the abelian scheme `H`
   (`baseChange_map_surjective`) gives a homomorphism `r : G ⟶ H` whose
   generic fibre is the inverse of the generic fibre of `j`. The generic fibres
   of `r ≫ j` and of the identity agree. Since `G` is flat and separated,
   `genericFibre_map_injective` gives `r ≫ j = 𝟙`.

6. Conclusion. The open immersion `j` is a monomorphism and now a split
   epimorphism, hence an isomorphism over `Spec V`. Properness and geometric
   connectedness of `H` therefore hold for the given model `G`.

## Provenance

This is the proof of the implication (a) to (b) in Bosch, Lütkebohmert and
Raynaud, *Néron Models* (1990), §7.4, printed p. 183, Theorem 5. There the
identity component is proper by Grothendieck and Dieudonné, *Éléments de
géométrie algébrique IV*, third part (1966), Corollary 15.7.10, hence an
abelian scheme. As an abelian scheme it is the Néron model of its generic
fibre (BLR §1.2, Proposition 8), so it is the whole Néron model. The
properness step is the hypothesis of the theorem. The step "identity component
equals the model" uses the Néron mapping property of the abelian scheme `H`
and generic-fibre uniqueness of morphisms.
