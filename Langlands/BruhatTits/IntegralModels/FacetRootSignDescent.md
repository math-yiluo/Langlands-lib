# Descent of the facet root identity through coefficient change and subtori

Module `Langlands.BruhatTits.IntegralModels.FacetRootSignDescent`.

## Setting

As in the accepted module `FacetRootSignBaseChange`: `R` and `A` are local
domains with fraction fields `K` and `L`, the maps `R → A`, `R → K`,
`A → L`, `K → L` and `R → L` form a commuting square, and `R → A` is a local
homomorphism. `G` is a group scheme over `K`. For a relative component model
`D'` of `G`, `D'.baseChange A L` is the Library's coefficient change, and
`φ.baseChange A L`, `Q.baseChange A L` and `T.baseChange A L` are the
coefficient changes of a model morphism, special-fibre quotient data and an
integral torus from `FacetRootSignBaseChange`. For an isomorphism
`e : G_L ≅ H` of group schemes over `L`, `transport e` is the Library's
transport of models, model morphisms and quotient data along `e`
(`BruhatTits/IntegralModels/Transport/Model.lean`). Transport keeps the
integral group schemes, their homomorphisms and the special fibres, and
changes only the generic identifications.

## Content

### Finiteness of the base-changed quotient

`SpecialFibreQuotientData.baseChange_quotient_locallyOfFiniteType` (an
instance): if the quotient of `Q` is locally of finite type over the residue
field of `R`, then so is the quotient of `Q.baseChange A L` over the residue
field of `A`.

### Descent of the root form of the sign formula

`RelativeComponentModelHom.roots_reductiveImageTorusMap_of_baseChange_transport`.
Let `φ : D' ⟶ D` be a morphism of relative component models of `G`, `Q`
special-fibre quotient data of `D` whose quotient is locally of finite type,
and `T` an integral torus of `D'` whose integral torus `T.torus` is split.
Let `e : G_L ≅ H` be an isomorphism. Let `T'` be an integral torus of
`(D'.baseChange A L).transport e` whose integral torus `T'.torus` is split.
Let `ρ` be a homomorphism from the base change of `T.torus` to `A` into
`T'.torus` with `ρ ≫ T'.inclusion` equal to the base change of
`T.inclusion` (`IntegralTorusData.baseChangeInclusion A L T`). Let `σ` and `σ'`
be real functions on the character lattices of `T.torus` and `T'.torus` such
that `σ m = σ' ψ` whenever the base change of `m` to `A` equals `ρ ≫ ψ`.
Write `φ'`, `Q'` for `(φ.baseChange A L).transport e` and
`(Q.baseChange A L).transport e`. If

`roots (φ'.reductiveImageTorusMap Q' T') = {χ ∈ roots (φ'.quotientTorusInclusion Q' T') | 0 ≤ σ'(χ^int)}`,

then

`roots (φ.reductiveImageTorusMap Q T) = {χ ∈ roots (φ.quotientTorusInclusion Q T) | 0 ≤ σ(χ^int)}`.

Here `χ^int` is the integral character with special character `χ`
(`specialCharacterEquiv`). This is the root form of the facet sign formula
(`FacetRootSignRestriction.hasApartmentLieWeightSignFormula_iff_roots`).

### Split tori as integral models

`IntegralModel.ofSplitTorus T hT`: a split torus `T` over `R`, as an
integral model of its own generic fibre `T_K`, with the identity generic
identification. Split tori are affine and smooth over `R`, so the model
axioms hold. The simp lemma `ofSplitTorus_group` records the integral group
scheme.

### Extension of a generic factorization of split tori

`exists_torusHom_of_generic_factor`. Let `R` be a Henselian discrete
valuation ring with separably closed residue field and fraction field `K`.
Let `N` be an integral model over `R` of a group scheme over `K`, `T` and
`A` split tori over `R`, `j : T ⟶ N.group` a homomorphism and
`k : A ⟶ N.group` a closed subgroup. Let `g : T_K ⟶ A_K` with
`g ≫ k_K = j_K`. Then there is a homomorphism of tori `ρ : T ⟶ A` with
`ρ ≫ k = j` and `ρ_K = g`.

## Proofs

`baseChange_quotient_locallyOfFiniteType`: the structure morphism of the
base-changed quotient is a pullback of the structure morphism of the
quotient, and local finite type is stable under base change.

`roots_reductiveImageTorusMap_of_baseChange_transport`. Let `T''` be the
integral torus of `D'.baseChange A L` with integral torus `T'.torus` and
inclusion `T'.inclusion` (`IntegralTorusData.ofInclusion`). Since transport
does not change the integral group schemes or the homomorphisms, `T''` and
`T'` have the same torus and inclusion. The reductive images, torus maps and
quotient torus inclusions of the transported data and of the untransported
data are the same terms, so the hypothesis is literally the root identity
for `φ.baseChange A L`, `Q.baseChange A L` and `T''`. The accepted
restriction lemma `roots_reductiveImageTorusMap_of_comp`
(`FacetRootSignRestriction`), applied to `ρ` from `T.baseChange A L` to
`T''` with the sign function `m' ↦ σ(m'')`, where `m''` is the character of
`T.torus` whose base change is `m'` (`characterLattice.baseChangeEquiv`),
gives the root identity for `T.baseChange A L`. The compatibility of the
sign functions is `hσ`. The accepted coefficient-change lemma
`roots_reductiveImageTorusMap_of_baseChange` (`FacetRootSignBaseChange`)
then gives the identity for `T` with the sign function
`m ↦ σ((m_A)'')`, which is `σ` by `AddEquiv.symm_apply_apply`.

`exists_torusHom_of_generic_factor`. View `T` and `A` as integral models
`ofSplitTorus` and `j`, `k` as homomorphisms of integral models into `N`
over `j_K` and `k_K` composed with the generic identification of `N`. For
an integral point `x` of `T`, `g(x)` maps under `k_K` to `j_K(x)`, which is
integral in `N`. Since `k` is a closed subgroup, the Library's
`Hom.mem_integralPoints_of_map_mem` shows that `g(x)` is an integral point
of `A`. The model `ofSplitTorus T` is smooth, so the Library's
`smoothHomExtension` (KP Corollary 2.10.10) gives a homomorphism of
integral models `ψ : T ⟶ A` over `g`. Its generic fibre is `g`. Finally
`ψ ≫ k` and `j` have equal generic fibres, so they are equal by the
Library's `hom_eq_of_generic`.

## Provenance

Internal infrastructure for the proof of
`Langlands.BruhatTits.IntegralModels.UnramifiedFacetCommonTorusStatement`
(Kaletha–Prasad, *Bruhat–Tits theory: a new approach*, Axiom 4.1.22(3)).
The final proof establishes the sign formula over the ring of integers of
the maximal unramified extension, for a split torus of the transported
model, and descends it to the original model. This module supplies the
descent step and the construction of the integral torus homomorphism. It
uses Library definitions, the Library proof `smoothHomExtension`
(KP Corollary 2.10.10 and Remark 2.10.19), and the accepted modules
`FacetLieImageRoots`, `FacetRootSignRestriction` and
`FacetRootSignBaseChange`. It makes no other assertion from the literature.
