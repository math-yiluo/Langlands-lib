# Maximal residue tori under actual coefficient extension

This transport module concerns a local coefficient extension `R → A`,
the induced residue-field extension `k_R → k_A`, and an integral model `M`
over the local domain `R` with fraction field `K`. The coefficient ring
`A` is local and the coefficient map is local. The first two lemmas do not
require `A` to be a domain or introduce a fraction field of `A`.
No characteristic restriction is imposed, and all rings and fields lie in
arbitrary universe `u`.

`residueTorusCoefficientIso` constructs the canonical isomorphism of actual
source groups between extending the `k_R`-residue of `T` to `k_A` and
taking the `k_A`-residue after extending `T` to `A`. It is the commuting
square comparison for the actual local coefficient and residue maps.
This construction applies to any commutative group scheme `T/R`, without
a torus hypothesis, fraction fields, a model, or smoothness. It is the
source isomorphism used in the maximality transport below.

For a commutative integral group `T/R` and a map `i:T → M.group`,
`M.isMaximalTorus_residue_baseChange` assumes smoothness of `M.group` and
maximality of the actual `k_R`-residue map of `i`. It proves maximality of
the literal map obtained by first pulling `i` back to `A` and then taking
its `k_A`-residue fibre. It does not assume a compatibility equation between
those two pullback orders.

The proof applies the published `maximalTorusBaseChangeForward` to the
original maximal residue map. The published `residue_coefficient_square`
and `residueTorusCoefficientIso` give the source comparison, while
`Descent.squareComparison` gives the model comparison
between the two successive pullbacks. The latter is the comparison used
by `M.specialFibreCoefficientIso` when a fraction field is supplied.
Naturality supplies the exact
map equation. Replacing the source by the inverse comparison and the
ambient group by its comparison carries maximality to the actual residue
map, using `IsMaximalTorus.iso_comp` and `IsMaximalTorus.comp_iso`.

`M.isMaximalSplitTorus_residue_baseChange` additionally assumes that the
integral source after coefficient extension to `A` is split. Its residue
fibre is therefore split, and `IsMaximalTorus.isMaximalSplitTorus` changes
the preceding conclusion to maximal splitness.

The combined theorem
`IntegralModel.Hom.isMaximalSplitTorus_residue_baseChange_of_coefficient_bounded`
uses a generic-identity comparison `φ:M → N` between smooth integral
models and a connected original residue fibre of `M`. The coefficient ring
`A` is a Noetherian Henselian valuation domain with fraction field `L`
and algebraically closed residue field, with compatible maps `K → L`
and `R → L` and both specified scalar towers.
A valuation `v` on `L` is trivial on the image of every
unit of `A`. The group `G_L` is connected reductive. Supply a maximal
split generic torus `i₀:T₀ → G_L` whose character-valuation kernel maps
into `(M.baseChange A L).integralPoints`.

For any integral map `i:T → M.group` whose actual original residue is
maximal, and whose source becomes split over `A`, this theorem proves
maximal splitness of the actual `k_A`-residue of the coefficient extension
of `i ≫ φ.hom`. It first applies the published
`Hom.isMaximalTorus_specialFibreMap_of_coefficient_bounded` to the original
residue map. Functoriality identifies its composite with the residue of
the actual integral composite. The preceding coefficient-transport lemma
then supplies maximal splitness in the target's actual residue fibre.

The provenance is derived from the published maximal-torus field-extension
proof, the actual coefficient square and its naturality, the published
bounded-torus preservation theorem, and maximal-torus transport. Integral
lifting, splitting, the generic bound and the supplied model comparison
remain inputs; this module does not assert their existence from building
fixed points. A lift supplied through a residue source isomorphism can
provide the original residue-maximality input using
`IsMaximalTorus.iso_comp` and its exact residue square. The module supplies
the actual residue-maximality input needed for integral conjugacy; it does
not prove the fixed-pair special-apartment statement it serves,
`UnramifiedFixedPairSpecialApartmentStatement`, which is proved as
`unramifiedFixedPairSpecialApartment` in
`Langlands.Geometry.Building.UnramifiedFixedPairSpecialApartmentProof`.
