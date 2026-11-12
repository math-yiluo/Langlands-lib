# Strong heads from regular opposite Jacquet modules

Worker 148. This is an internal assembly of the quotient argument in Renard
VII.4.2 (i), printed p.243 / PDF p.249, on the published actual
represented-parabolic functors. It constructs a strong irreducible head
conditionally on the geometric, regularity, finite-length and second-adjunction
inputs described below. It does not prove the full Langlands classification.

The field universe `u` and inducing-carrier universe `v` are independent.
The ambient group scheme is affine; its rational points have the canonical
point topology, are locally compact, and form a nonarchimedean group. Both
represented parabolics have the same Levi scheme `M`, a specified rational
Levi embedding, a geometric unipotent radical and an isomorphism expressing
the parabolic as their product. The Levi topology is its own published
canonical point topology. The final results additionally use the local-field
and connected-reductive hypotheses. They require a split component
`a : A -> M`, which supplies the centrality of the map on rational points.

`leviInductionEquivOfEquiv` sends an equivariant equivalence of inducing
representations, even in independent carrier universes, to an equivalence
between their actual normalized induced representations. It pulls the
original equivalence back to the literal Levi image and applies the published
`normalizedInductionEquivOfEquiv`. `leviJacquet_map_surjective` proves that
actual Jacquet restriction preserves surjections, using the already proved
surjectivity of the coinvariant localization map. Neither result assumes
finite length or admissibility.

`exists_nonzero_oppositeJacquetMap` takes a supplied second adjunction
`i_P : SmoothRep_M(max u v) -> SmoothRep_G(max u v)` left adjoint to `r_Q`,
and a nonzero map `i_P(sigma) -> pi`, where `sigma` has carrier in `v` and
`pi` in `max u v`. It raises `sigma` to `ULift sigma` in `max u v`, transports
the original induced map along `leviInductionEquivOfEquiv`, and applies the
adjunction to obtain a map `ULift sigma -> r_Q(pi)`. The induction functor is
additive by its explicit action on maps, so the adjunction preserves zero and
the new map is nonzero. Precomposition with the original carrier equivalence
gives a nonzero map `sigma -> r_Q(pi)`. The result concerns the original
`sigma`, with no identification of the two universes.

`exists_regularOppositeQuotientEmbedding` further assumes that `sigma` is
irreducible, is `PQ`-regular, and that the actual identity boundary-support
image `S` in `r_Q i_P(sigma)` is equivariantly isomorphic to `sigma`. For any
smooth irreducible quotient `pi` of `i_P(sigma)`, its quotient map is nonzero.
The supplied second adjunction gives the nonzero map
`j : sigma -> r_Q(pi)` just described. Applying actual Jacquet restriction to
the quotient map gives a surjection `r_Q i_P(sigma) -> r_Q(pi)`.
`IsPQRegular` is exactly comaximality of the kernels of the split-component
algebra on `sigma` and on `r_Q i_P(sigma)/S`. Thus
`quotient_retraction_of_comaximal` gives a retraction of `j`. This retraction
is nonzero. The published Frobenius reciprocity equivalence for `Q` sends it
to a nonzero map `pi -> i_Q(sigma)`, which is injective by irreducibility of
`pi`. The function and its injectivity are the conclusion of the theorem.
No particular choice of adjunction or quotient map is needed.

`exists_regularOppositeLeviHead` assumes, in addition, that `sigma` is
admissible and that actual induction `i_P` preserves finite group-algebra
length. The latter gives an irreducible quotient using the published
`exists_irreducibleLeviInductionQuotient`. Regularity, the identity-support
equivalence and admissible Schur give
`dim_C Hom_G(i_P(sigma), i_Q(sigma)) = 1` by the published
`pqRegular_intertwining_finrank_eq_one`. Every irreducible quotient embeds
in `i_Q(sigma)` by the preceding argument. The published one-dimensional Hom
criterion therefore proves that the chosen quotient is the strong
irreducible head. Its kernel comparison tests every algebraic irreducible
quotient in the source carrier universe `max u v`, since those quotients
inherit smoothness. `regularOppositeLeviHead` chooses the actual smooth
head, in `max u v`, together with its full `IsIrreducibleHead` certificate.
The choice is noncanonical.

All of the following remain explicit inputs of that construction:

- the actual parabolic triples and split component;
- a second adjunction between the specified actual functors on `max u v`;
- preservation of finite group-algebra length by `i_P` on inputs in `v`;
- irreducibility and admissibility of `sigma`;
- `PQ`-regularity of `sigma`;
- the equivariant identification of the actual identity-support image with
  `sigma`.

The theorem does not assert that `Q` is opposite to `P`; the intended
application supplies an actual opposite parabolic and discharges the
adjunction and identity-support inputs for it. Opposite existence, the
identity-support theorem, regularity for Langlands triplets, second
adjointness and induction finite-length preservation are separate obligations.
Parameter injectivity and exhaustion are also unproved here. The protected
classification statement and its imports are unchanged.

The provenance is internal: the module composes published representation
constructions and proved conditional helpers, rather than replacing the
source theorem by a statement with fewer quantifiers. The mathematical route
is the one in David Renard, *Représentations des groupes réductifs p-adiques*,
version dated 9 July 2026, VII.4.2 (i), printed p.243 / PDF p.249, from second
adjointness through the opposite Jacquet retraction and Frobenius reciprocity
to equality of quotient kernels. Registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
