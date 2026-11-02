# Descent of affine étale objects and actions to stable finite levels

Author: Worker 706. The stable-system and ring-groupoid dependencies include
Worker 266's constructions.

This internal helper assumes an affine cartesian first level
`h : IsCartesianHom E E₀ f g`, with `E.U`, `E₀.U`, and `E₀.R` affine and the
coordinate ring of `E₀.U` Noetherian. It descends an affine étale object over
`E.U`, together with a given genuine action of `E`, to a stable finite level.
All schemes, rings, and index categories retain the arbitrary universe `u`.
The first level is an input; this module does not prove its existence, construct
a quotient of the descended action, or complete the first-level theorem.

The application is the descent of the étale chart over an existing inverse
system in Stacks Proposition 70.8.1, Tag 07SU (the paragraph beginning with
`W = f⁻¹(U)`), registered as
`stacks-noetherian-approximation-2026-11-01`. The present statements are derived
scheme-and-action interfaces, rather than literal translations of that
paragraph. Their ingredients are Mathlib's étale algebra descent, the stable
subalgebra exhaustion developed from Tags 07TR, 07TT, and 07TU, spectrum
pushout/pullback duality, and the previously developed finite action-law descent.

## Finite-subalgebra étale model

`exists_fg_etale_object_model` has a more general base ring `R`. Given affine
schemes `P` and `U`, an `R`-algebra structure on `Γ(U, ⊤)`, and an étale morphism
`p : P ⟶ U`, it produces a finitely generated `R`-subalgebra `S` of `Γ(U, ⊤)`,
an affine scheme `Q`, an étale map `q : Q ⟶ Spec S`, and `k : P ⟶ Q`. The square
with vertical maps `p` and `q` and bottom map
`U.isoSpec.hom ≫ Spec.map S.val` is a pullback.

The proof applies Mathlib's `Algebra.Etale.exists_subalgebra_fg` to the coordinate
ring map of `p`. This gives an étale `S`-algebra `T` and an algebra equivalence
`Γ(P, ⊤) ≃ₐ[Γ(U, ⊤)] Γ(U, ⊤) ⊗[S] T`. Put `Q = Spec T`. Applying `Spec` to
the tensor-product pushout supplies the pullback square on spectra. Transport
the original source and base by their affine spectrum isomorphisms. Naturality
of those isomorphisms and the scalar-compatibility of the algebra equivalence
prove the required compatibility equations. The ring-homomorphism criterion
for étaleness proves that `q` is étale.

## Stable finite-level model

The following declarations lie in `EtaleEquivalenceRelation.IsCartesianHom`.

`exists_stable_etale_object_model` produces an index `i` of `h.stableDiagram`,
an affine scheme `Pi`, an étale map `pi : Pi ⟶ (h.stableDiagram.obj i).U`, and
`li : P ⟶ Pi`, such that the square with vertical maps `p`, `pi` and bottom map
the actual stable cone leg `(h.stableCone.π.app i).objMap` is a pullback.

First apply the preceding lemma over `Γ(E₀.U, ⊤)`. Stable exhaustion enlarges its
finite subalgebra `S` to a finitely generated stable subalgebra. Pull `Q` back
along the resulting map `Spec i ⟶ Spec S`. The actual original cone leg followed
by this inclusion is the map `E.U ⟶ Spec S`, by functoriality of `Spec`. The
pullback lift of `k` and `p` defines `li`. Cancelling the canonical pullback on
the right of the original pullback gives the asserted square. Affineness and
étaleness hold by base change.

## Descent of the genuine action

`exists_stable_etale_action_model` adds a genuine `Action E p`. It returns a
stable index `i`, an affine étale object `pi : Pi ⟶ (h.stableDiagram.obj i).U`,
the comparison `li`, a genuine action `B` at that level, and the pullback square
`hi`. The conclusion includes `Action.IsEquivariant` for `A` and `B` under the
actual stable cone leg and `li`, using `hi.w.symm` as its compatibility equation.

Choose an initial stable étale object model at index `j`. Restrict the stable
diagram to the cofiltered category `Over j`; the original object cone remains a
limit, and the diagram has a comparison to its fixed level at `j`. Apply
`Action.CartesianSystem.exists_equivariant_action_at_level`. It descends both
the action map and its unit and associativity laws to a common later level,
and retains both object pullback squares and actual cone-leg equivariance.
The square over the initial étale model proves that the final structural map
is étale and affine. Its affine base then makes `Pi` affine. The returned index
is the underlying stable index of the chosen object of `Over j`.

`StableEtaleActionModel p A` packages exactly these data. Its fields are `index`,
`object`, `projection`, `comparison`, `action`, `square`, `affine`, `etale`, and
`equivariant`. The square and equivariance use the actual stable cone leg at
`index`. In particular this is an action with both laws, rather than merely an
action map. No quotient data are included.

`stableEtaleActionModel p A` chooses such a model by classical choice from
`exists_stable_etale_action_model`. The level object scheme is affine and
Noetherian by the properties of the stable system. These properties depend on
the supplied Noetherian first level, which remains an explicit hypothesis.
