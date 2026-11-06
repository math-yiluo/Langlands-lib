# Original subgroup Haar and gamma under changes of cocharacter description

This derived construction compares descriptions of the same actual dynamic
subgroups. Its measure convention is Waldspurger, *La formule de Plancherel pour
les groupes p-adiques (d'après Harish-Chandra)* (2003), I.1, printed p.240 /
PDF p.6: each subgroup Haar gives mass one to its intersection with the common
compact subgroup. These comparisons are internal consequences of the published
dynamic-subgroup equalities and exact Haar transport, rather than separately
numbered assertions of that source.

The setting is an arbitrary-universe nonarchimedean local field, in arbitrary
characteristic, and an affine group scheme locally of finite type. Rational
points carry their existing canonical topology and its Borel measurable space.
The same compact open `K`, with its compactness proof, is used throughout.
Connected reductivity, splitness, quasisplitness and compact-limit stability
are not needed for these comparisons.

`parabolicSourceChoiceEquiv` restricts the identity of the original rational-point
group to the dynamic parabolics of cocharacters `χ` and `ψ`, given equality of
their subgroup functors. `oppositeRadicalSourceChoiceEquiv` does the same for
their opposite contracting subgroups, given equality of those subgroup
functors. Both definitions specialize the published
`QuotientIntegration.subgroupContinuousMulEquiv`; their forward maps preserve
the underlying original rational point by construction.
No new model of any subgroup is supplied.

The two `measurePreserving_*SourceChoiceEquiv` lemmas apply
`measurePreserving_sourceSubgroupHaar` to the ambient identity and the same
compact. They preserve the original `parabolicHaar` and `radicalHaar` exactly.
These are intrinsic subgroup Haar measures, each fixed by mass one on the
compact trace, and no scale is chosen to force a gamma identity.

`gamma_eq_of_dynamic_subgroups_eq` specializes the published
`compactNormalizedSourceGamma_eq_of_transport` to this identity transport.
Consequently the existing nonnegative extended-real `gamma` agrees for the two
descriptions, using the same original measures. No finiteness or convergence
premise is needed for equality of these lower integrals.

The remaining lemmas give concrete instances:

- `oppositeCocharacter_precomp_power` proves that taking the opposite commutes
  with every integral parameter power. Its proof uses equality on all test
  points, the published `Dynamic.comp_powerHom`, and multiplication of integer
  powers.
- `gamma_precomp_power` uses
  `Dynamic.parabolic_precomp_power` and `Dynamic.unipotent_precomp_power` with
  an integer `n > 0`, applying the latter to the opposite cocharacter.
- `gamma_eq_of_comp_eq_of_central_kernel` uses the existing parabolic and
  unipotent lift-independence theorems. Its assumptions are a morphism `q` out of
  the original group, centrality of its full scheme-theoretic kernel, and
  `χ ≫ q = ψ ≫ q`. Precomposing this equality by inversion gives the corresponding
  equality for the opposite cocharacters. Neither surjectivity of `q` nor
  affineness or a topology on its target is assumed. The gamma comparison takes
  place in the original group and preserves its original measures.
- `gamma_eq_of_positive_powers_comp_eq_of_central_kernel` combines the preceding
  two gamma comparisons when the projections of positive powers, with possibly
  different positive integer exponents, agree.

These comparisons prove independence under the displayed changes of
description of the same subgroups. Waldspurger's stronger I.1 Remark (3),
printed pp.240–241 / PDF pp.6–7, compares different parabolics with the same
Levi through a simultaneous root-index expression. General same-Levi
independence, that root-index argument, special-compact realization, convergence
and the Plancherel conclusions remain separate obligations.
