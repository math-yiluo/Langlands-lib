# Recovering intertwiners from smooth contragredients

The closing theorem `Langlands.smoothContragredientHomDuality` proves the
published `Langlands.SmoothContragredientHomDualityStatement`. For a topological
group whose compact open subgroups are cofinal among open subgroups, a smooth
complex representation `ρ` and an admissible complex representation `σ`, the
canonical contragredient pullback is the forward map of a complex-linear
equivalence

`Hom_G(ρ, σ) ≃ₗ[ℂ] Hom_G(σ^vee, ρ^vee)`.

The equality specifying this forward map is part of the conclusion. The group
and the two representation carriers have independent universes. The
topological-group instance, compact-open cofinality, source smoothness and
target admissibility are quantified inside the published proposition. Source
admissibility, a finite-dimensional carrier, a topology on the representation
spaces, Hausdorffness and countability are not assumptions of this theorem.
The contragredient uses the smooth part of the algebraic linear dual and the
inverse-group-element action; scalar multiplication is complex-linear.

## Linearity and reconstruction over a commutative ring

The component lemmas `contragredientMap_add` and `contragredientMap_smul`
evaluate the pullback functional at a vector and use that functional's
linearity. These laws hold over an arbitrary commutative ring.

The lemma `contragredientMap_bijective_of_bidual` works over an arbitrary
commutative ring with four independent coefficient, group and carrier
universes. It assumes that both representations are smooth and that the
target's canonical smooth bidual map is bijective. It uses no compact-open
cofinality, admissibility or source reflexivity assumption.

For injectivity, two original intertwiners with equal contragredients have
identical values under every target smooth functional. Their target bidual
evaluations are therefore equal. Injectivity of target evaluation makes the
original maps equal pointwise.

For surjectivity, let `a` intertwine the target contragredient with the source
contragredient. Turn target evaluation into a representation equivalence `e`
using `Representation.IntertwiningMap.ofBijective`. Dualize `a`, compose on the
right with source evaluation, and on the left with `e.symm`. The resulting
map from the source to the target is an intertwiner. Applying the identity
`e.apply_symm_apply` to the dualized evaluation and then evaluating at an
arbitrary target smooth functional shows that its contragredient is `a`.
The proof needs the source evaluation map but does not need it to be bijective.

The lemma `contragredientHomEquiv_exists_of_bidual` packages the pullback as a
linear map using the two linearity laws. `LinearEquiv.ofBijective` and the
preceding bijectivity lemma produce the equivalence, whose forward-map
formula is definitional.

## Complex admissible specialization

The closing theorem uses the published lemmas
`Langlands.smoothBidual_injective_of_compact_cofinal` and
`Langlands.smoothBidual_surjective_of_compact_cofinal` from
`Langlands.Representation.Smooth.Contragredient.AdmissibleDualityProof`.
Target admissibility supplies target smoothness. Together with the explicit
compact-open cofinality premise, these results prove the required bijectivity
of the target bidual map. Applying the general reconstruction result proves
the full existing target, including the specified canonical forward map.
This theorem does not establish cofinality for any particular group.

## Provenance

The reconstruction follows Casselman, *Introduction to admissible
representations of p-adic groups*, Chapter II, revision June 16, 2019,
Section 3, Proposition II.3.4, page 7, using Lemma II.3.2 on page 6. Casselman
assumes a smooth source and an admissible target, both free over the coefficient
ring; his freeness concerns fixed-vector spaces. Over ℂ freeness is automatic.
The explicit cofinality premise replaces the stronger ambient locally profinite
and countability assumptions on page 1. The generic ring helper isolates the
formal bidual reconstruction argument and assumes the precise target-bidual
bijectivity it needs; it does not assert admissible bidual reflexivity for every
commutative coefficient ring.

The registered original is `casselman-2019-smooth-representations`, SHA256
`2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`.
Pages 1, 6 and 7 and the source fingerprint were checked for this proof.
All supporting component lemmas are retained in this module. Worker 0 authored
the supplied proof and its explanation.
