# Actual fixed-source Hom and its nondegenerate part

This internal arbitrary-ring additive construction supports Renard, French edition
of 9 July 2026, I.2.3, printed pages 16–18 / PDF22–24. Its governing source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The source's conventions at printed pages 5–7 / PDF11–13 permit nonunital rings
and module actions without a unit law. The motivating induction constructions
are in the complex-algebra and nondegenerate setting; the present construction
retains only original additive groups and actions and does not claim recovery
of complex scalars.

For a specified commuting S–R bimodule Y, `ambientMap` abbreviates the published
one-sided `sourceMap`, with the original bimodule identity as source map. It is
postcomposition on exactly `NonUnitalModuleHom S Y M`. Its complete additive map
is `postcomposeAddHom`; its formula is h ↦ f.comp h. Identity, composition,
zero and addition are proved for the entire original R-linear maps, including
independent intermediate and target carrier universes. `ambientFunctor`
packages these maps on the ambient module category. No target right action is
required. Its carrier, published pointwise group, named `sourceAction` and
whole scalar endomorphism are exposed. The action is (r • h)(y) = h(op r • y).
All ring and carrier universes are independent, and the Hom universe is exactly
the maximum of the fixed-source and variable carrier universes.

`homPart` is an abbreviation for the published `nondegeneratePart` of that
actual source-action module. Membership means that an actual idempotent of R
fixes h; equivalently h(op e • y) = h(y) for every y. `partMap` is precisely
`restrictNondegeneratePart hR` of `ambientMap`, with whole additive-map and
subtype-value equalities. It retains the actual inherited group and original
action and has proved identity, composition, zero and addition laws.

`nondegenerateFunctor` is the actual composite of `ambientFunctor` with the
published `nondegeneratePartFunctor hR`. Its object uses the published proof
`nondegeneratePart_isNondegenerate`. Only R is assumed idempotented: neither S
nor either Y-action nor the ambient variable module must be nondegenerate.
The complete composite equality, object carrier/group/action, inherited scalar
formula and restriction maps are exposed. `restrictedFunctor` precomposes with
the published inclusion of nondegenerate S-modules. Additivity in each case
uses the published preadditive structures and additive composition instances.

`inclusion` whiskers the published `nondegeneratePartInclusion hR` by the
ambient functor. Its component is exactly the submodule inclusion, its entire
additive map is the subgroup subtype map, and naturality is proved as equality
of original R-linear maps. `restrictedInclusion` whiskers this with the input
inclusion. This is an inclusion of the part, with no equality asserted between
the included part and the whole ambient Hom.

The supplementary registered `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`, was read at
PDF1–2 and PDF18–19. Its printed-page-299 correction fixes postcomposition in the
covariant variable and precomposition in the contravariant variable, agreeing
with the implemented route. Its printed-page-20 correction concerns the
adjunction orientations, already reflected in the 2026 text. No adjunction is
claimed here.

Pseudo-forgetful and induction specializations use this construction in a
separate companion. Coefficient-linear/unitization comparisons, completion and
regular-Hom equivalences beyond direct object formulas, equality of two Hom
parts, scalar restriction, tensor-Hom equivalences, categorical adjunctions,
exactness and tensor-based F/P remain separate obligations. This is not full
coverage of I.2.3 or the book.
