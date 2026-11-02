# A smooth global unit scheme gives actual relative automorphism schemes

This internal adapter starts with an actual scheme `G` over `S` and a
full natural isomorphism from its lifted Yoneda presheaf to
`RelativeGlobalUnits.presheaf f`, for an arbitrary morphism `f : X → S`.
It does not construct such a unit scheme.

For every actual relative test `T` and every line bundle `L` on
`T ×ₛ X`, `relativeAutomorphismSchemeIsoOfUnitScheme f G e T L` uses the
actual base change of `G` to `T.left` as its scheme. The isomorphism first
restricts the global representation by `representedBaseChangeIso`, using
the ordinary pullback adjunction. It then composes with the full natural
scalar-unit identification
`relativeSliceUnitsAutomorphismPresheafIso`. Its target is the
automorphism presheaf formed directly from the actual relative Picard
pseudofunctor, including its coherent restrictions on the entire slice.

If `G → S` is smooth, every structure morphism of these base changes is
smooth by stability of ordinary scheme smoothness under base change.
The implemented proof `hasSmoothUnitSchemes_of_unitScheme` supplies these
same schemes and their restricted representing isomorphisms on every
slice. `hasSmoothRelativeAutomorphismSchemes_of_unitScheme` then applies
the existing scalar-unit comparison to obtain the smooth relative
automorphism condition required in the Picard quotient statement.

All scheme tests, all morphisms and all bundles are retained, including
nonreduced and non-quasi-compact schemes. There is no field, properness,
section or global-functions hypothesis, and no claim that a unit scheme
exists. This adapter proves no quotient or representability theorem for
the Picard class sheaf.
