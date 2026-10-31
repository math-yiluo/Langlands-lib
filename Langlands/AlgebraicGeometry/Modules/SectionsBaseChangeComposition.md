# Naturality and composition of ordinary sections base change

Let `φ : R → R'`, `f : X → Spec R`, `f' : X' → Spec R'`, and
`g : X' → X` form a commuting square, so that
`g ≫ f = f' ≫ Spec.map φ`. All schemes and commutative rings lie
in an arbitrary universe `u`. Write `Γ_f` for the actual relative
global-sections functor and `g*` for scheme-module pullback.

The definition `sectionsBaseChangeNatTrans` packages the published
ordinary sections maps as a natural transformation

`Γ_f ⟶ g* ⋙ Γ_f' ⋙ Res_φ`.

The selected definition `scalarSectionsBaseChangeNatTrans` packages
their scalar-linear adjuncts as a natural transformation

`Γ_f ⋙ Ext_φ ⟶ g* ⋙ Γ_f'`.

Its component at an actual module sheaf `M` is exactly
`scalarSectionsBaseChangeMap φ f f' g w M`, whose source is
`R' ⊗_R Γ_f(M)` and whose target is `Γ_f'(g* M)`.
Both naturality proofs use the coefficient-naturality identities
from `CohomologyBaseChangeZero`.

The lemma `sectionsBaseChangeMap_eq_sectionPullback` identifies the
ordinary map, on each section, with the published semilinear
`Langlands.Scheme.Modules.sectionPullback g M ⊤`. This equality
is definitional: both use the same pullback-adjunction unit at the
whole open.

For every open `U ⊆ X`, the lemma
`sectionsBaseChangeMap_restrict` states that restricting the image
of a global section to `g⁻¹(U)` agrees with pulling back its
restriction to `U`. It is the symmetric form of the published
`sectionPullback_restrict` identity. Thus this compatibility uses
the restriction maps of the actual module presheaves.

For a second commuting square with `ψ : R' → R''` and
`g' : X'' → X'`, `sectionsBaseChangeSquare_comp` supplies the
commutativity equality for the composite square. The theorem
`sectionsBaseChangeMap_comp` identifies successive ordinary maps
with the map for `φ ≫ ψ` and `g' ≫ g`. After the two sections maps,
its left-hand composite uses the inverse of
`ModuleCat.restrictScalarsComp` to identify iterated scalar
restriction with restriction along the composite, then applies
the relative sections of the forward sheaf-pullback comparison
`Scheme.Modules.pullbackComp g' g`. Extensionality on sections
reduces the assertion to the published `sectionPullback_comp`.

The theorem `scalarSectionsBaseChangeMap_comp` starts at
`R'' ⊗_R Γ_f(M)`. It first applies the forward comparison
`ModuleCat.extendScalarsComp φ.hom ψ.hom`, then scalar-extends
the first sections map, applies the second sections map, and
finally applies sections of the same sheaf-pullback comparison.
This composite equals the scalar sections map for the composite
square. The implemented proof uses `ExtendScalars.hom_ext` to
test `1 ⊗ x`; the scalar-extension composition formula sends this
generator to `1 ⊗ (1 ⊗ x)`. Each scalar sections map on its
generator is the actual pullback unit. The remaining equality
is again `sectionPullback_comp`.

The theorem `sectionsBaseChangeMap_id` composes ordinary base
change for the identity square with the forward scalar-restriction
identity comparison and with sections of
`Scheme.Modules.pullbackId X`. The result is the identity on
`Γ_f(M)`. The theorem `scalarSectionsBaseChangeMap_id` composes
the scalar map for the identity square with sections of that
pullback identity comparison; the result is
`ModuleCat.extendScalarsId R`. The first proof applies
`sectionPullback_id` to each section. The second tests tensor
generators, uses the scalar map and scalar-extension identity
formulas, and applies the same published identity.

These statements require only commuting squares. They impose no
Cartesian, quasi-coherence, flatness, or finiteness assumption.
They are internal functorial consequences of the published
sections maps, `SectionPullback`, and Mathlib's change-of-scalars
comparisons. No new external mathematical assertion is used.
The module supplies compatibility of ordinary sections maps;
it makes no assertion of nonaffine cohomology base change or
relative cube detection.
