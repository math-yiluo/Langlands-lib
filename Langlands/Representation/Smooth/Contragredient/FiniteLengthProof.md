# Finite length of admissible smooth contragredients

Author: Worker 1149.

`Langlands.smoothContragredientFiniteLength` proves the published proposition
`Langlands.SmoothContragredientFiniteLengthStatement.{uG,uV}`.
For any topological group with `CompactOpenCofinal G`, the actual smooth
contragredient of an admissible finite-length smooth complex representation
has finite length. The group and representation carrier universes are
independent. The applied interface is
`SmoothRep.contragredient_hasFiniteLength hcof A hA hfinite`.

The proof inducts on finite length of a module over the group algebra
`ℂ[G]`, using Mathlib's `IsFiniteLength` induction with a submodule `N` and
simple quotient `M ⧸ N`. The zero case follows because every linear
functional on a subsingleton module is zero. For the induction step, the
inclusion and quotient homomorphisms are viewed as intertwining maps for
`Representation.ofModule`. The published
`isAdmissible_iff_of_shortExact` supplies admissibility of both ends.
The induction hypothesis handles the submodule. The quotient is irreducible,
so `SmoothRep.isIrreducible_contragredient_iff` makes its actual smooth dual
irreducible as well. Its group-algebra module therefore has length one.

The maps `contragredientMap q` and `contragredientMap i` reverse the original
short exact sequence. Injectivity, surjectivity and exactness are provided by
`contragredientMap_injective_of_surjective`,
`contragredientMap_surjective_of_injective_of_compact_cofinal`, and
`contragredientMap_exact_of_surjective`, respectively. They are transported
to actual `ℂ[G]`-linear maps by
`Representation.IntertwiningMap.equivLinearMapAsModule`.
Mathlib's `Module.length_eq_add_of_exact` identifies the middle dual's length
with the sum of the two finite end lengths. This closes the induction.

Finally, the private intertwining equivalence from a representation to
`Representation.ofModule` of its own group-algebra module transports
admissibility to the induction presentation. Its dual map is surjective,
so `IsFiniteLength.of_surjective` returns the conclusion on the original
representation's smooth dual. All maps are the actual representation maps;
the restricted-scalar module structures only implement this change of
presentation.

This is an internal derived proof using the published duality and exactness
results. The source route motivating them is Renard,
*Représentations des groupes réductifs p-adiques*, 9 July 2026 version,
I.4.1 (printed page 23), I.5.1 (printed page 26), and III.1.6–7
(printed pages 61–62). The finite-length induction here is implemented with
Mathlib module length. The proof uses
`Classification.SupercuspidalContragredientAux` transitively through
`Category.Contragredient`: that dependency supplies generic smooth separation
and admissible irreducibility transfer. It adds no classification or
irreducible-admissibility theorem premise.

Admissibility of the original representation and compact-open cofinality
remain explicit hypotheses of this generic result. It does not prove
admissibility of all finite-length representations, and does not discharge
the separate closed rational-point or dynamic-Levi targets.
