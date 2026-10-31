# Zero tests and transport of actual pulled-back sections

The theorem `Langlands.SchemeModule.sectionVanishingTransport` proves
exactly `Langlands.SchemeModule.SectionVanishingTransportStatement`, in
an arbitrary universe `u`. The statement is published in
`Langlands.AlgebraicGeometry.Modules.SectionVanishingTransportStatement`,
and this module leaves it unchanged. The proof is internal
category-theoretic calculus for the published actual module sheaves. It
works for arbitrary schemes, modules, sections and scheme morphisms. It
uses no field, local freeness, properness, projectivity, ampleness or
pointwise-faithfulness hypothesis.

## Library results used

- `Modules.SectionResidue`: the definitions `pullbackSectionHom f M s`,
  which is `(pullbackUnitIso f).inv ≫ (Scheme.Modules.pullback f).map
  (sectionHom M s)`, and `pullbackSection f M s`, which is its value at
  `1` on global sections.
- `Modules.TensorSections`: `sectionHom_injective`, `sectionHom_app_one`
  (the value at `1` over an open `U` is the restriction of `s` to `U`) and
  `sectionHom_naturality` (`sectionHom N (φ.app ⊤ s) = sectionHom M s ≫ φ`).
- `Modules.PullbackSectionOpenProof`: `sectionHom_pullbackSection`, which
  says that `sectionHom` of `pullbackSection f M s` is
  `pullbackSectionHom f M s`.
- `Modules.PullbackUnit`: the canonical isomorphism `pullbackUnitIso f`
  between the pullback of the structure module and the structure module.
- `Modules.MorphismVanishing`: the four general zero-test helpers shared with
  `ResidueLocalChartProof`, preserving that proof's original helper statements.
- Mathlib: the natural isomorphisms `Scheme.Modules.pullbackComp` and
  `Scheme.Modules.pullbackId`, and the cancellation lemmas
  `comp_eq_zero_iff_of_epi` and `comp_eq_zero_iff_of_mono`.

## The component lemmas

The imported helper `structureModule_hom_eq_zero_iff` proves that a morphism
`φ : structureModule X ⟶ M` is zero exactly when `φ.app ⊤ 1 = 0`. For the
nontrivial direction, fix an open `U` and a function `a` on `U`.
Naturality of `φ` for the restriction from the whole scheme to `U`
identifies `φ.app U 1` with the restriction of `φ.app ⊤ 1`, which is zero.
Linearity then gives `φ.app U a = a • φ.app U 1 = 0`. Hence every
component of `φ` is zero, and `Scheme.Modules.hom_ext` gives `φ = 0`.

1. `sectionHom_eq_zero_iff`. By the helper and `sectionHom_app_one` at
   the whole scheme, `sectionHom M s` is zero exactly when the restriction
   of `s` along the identity is zero. That restriction is `s` itself.
2. `pullbackSection_eq_zero_iff`. By definition, `pullbackSection f M s`
   is the value at one of `pullbackSectionHom f M s`. The helper turns its
   vanishing into the vanishing of `pullbackSectionHom f M s`. That
   morphism is the pulled-back section morphism precomposed with the
   inverse of `pullbackUnitIso f`. An isomorphism is an epimorphism, so
   `comp_eq_zero_iff_of_epi` cancels it.
3. `pullbackSection_comp_eq_zero_iff`. First, the shared helper
   `map_eq_zero_iff_of_natIso` shows that two naturally isomorphic
   functors send a morphism to zero simultaneously. The proof composes
   with the natural isomorphism's components and uses its naturality.
   Applied to `Scheme.Modules.pullbackComp f g`, it gives the shared
   lemma `pullback_map_comp_eq_zero_iff`: the successive pullback of a
   module morphism along `g` and then `f` is zero exactly when its
   pullback along `f ≫ g` is zero. For the clause itself, apply lemma 2
   over `Z`. Then rewrite `sectionHom` of `pullbackSection g M s` by
   `sectionHom_pullbackSection` and unfold `pullbackSectionHom`. Next,
   split the image of the composite under pullback along `f`. Cancel the
   pulled-back unit isomorphism with `comp_eq_zero_iff_of_epi`. Finally,
   apply `pullback_map_comp_eq_zero_iff` and lemma 2 in reverse.
4. `pullbackSection_iso_eq_zero_iff`. The shared lemma
   `pullback_map_iso_eq_zero_iff` shows that pullback along a scheme
   isomorphism `f` sends a module morphism `φ` to zero only when `φ = 0`.
   If the pullback of `φ` along `f` is zero, pull it back further along
   `inv f`. By `pullback_map_comp_eq_zero_iff` and `inv f ≫ f = 𝟙 X`, this
   says that the pullback of `φ` along the identity is zero.
   `Scheme.Modules.pullbackId` identifies that pullback with the identity
   functor, through `map_eq_zero_iff_of_natIso`, so `φ = 0`. The converse
   direction is `Functor.map_zero`. The clause follows from lemma 2, this
   lemma and lemma 1.
5. `pullbackSection_naturality`. By `sectionHom_injective`, it suffices to
   compare the section morphisms of the two sides. Using
   `sectionHom_pullbackSection` and `sectionHom_naturality`, both sides
   become `(pullbackUnitIso f).inv ≫ (Scheme.Modules.pullback f).map
   (sectionHom M s) ≫ (Scheme.Modules.pullback f).map φ`. The proof uses
   functoriality of pullback and associativity of composition.
6. `pullbackSection_mapIso_eq_zero_iff`. Apply lemma 2 to both sides.
   `sectionHom_naturality` rewrites `sectionHom N (e.hom.app ⊤ s)` as
   `sectionHom M s ≫ e.hom`. Pullback is a functor, so the left zero
   condition concerns a composite that ends with the pullback of `e.hom`.
   That morphism is an isomorphism, hence a monomorphism.
   `comp_eq_zero_iff_of_mono` cancels it.

The theorem `sectionVanishingTransport` is the conjunction of these six
lemmas, in the order of the statement.

## Corollaries for `Picard.VanishesAlong`

In `Langlands.AlgebraicGeometry.Picard`, `VanishesAlong L f s` is by
definition `pullbackSection f L.obj s = 0`. The module therefore also
proves the following direct consequences for reuse in the
separating-line-bundle construction:

- `vanishesAlong_pullback_iff`: a section pulled back to the line bundle
  `(LineBundle.pullback g).obj L` vanishes along `f` exactly when the
  original section vanishes along `f ≫ g` (lemma 3).
- `vanishesAlong_mapIso_iff`: for an isomorphism `e : L.obj ≅ M.obj` of
  underlying sheaves, `e.hom.app ⊤ s` vanishes along `f` exactly when `s`
  does (lemma 6).
- `vanishesAlong_iso_iff`: along a scheme isomorphism, a section vanishes
  exactly when it is zero (lemma 4).
- `SeparatesPointsAndTangents.of_iso`: an isomorphism `e : L.obj ≅ M.obj`
  transports the separation predicate from `L` to `M`. Each of its three
  existential conditions takes the image `e.hom.app ⊤ s` of the witness
  `s`, and `vanishesAlong_mapIso_iff` transfers each vanishing and
  nonvanishing condition. The field `K` in this corollary comes only from
  the published predicate `SeparatesPointsAndTangents`.

The first three corollaries are definitional restatements of lemmas 3, 6
and 4. In `vanishesAlong_pullback_iff`, the line bundle
`(LineBundle.pullback g).obj L` has underlying sheaf
`(Scheme.Modules.pullback g).obj L.obj` by definition.

## Provenance

This is derived internal content, not a translation of a literature
theorem. The Lean proof was written by Worker 354 as a shared draft for
statement task `b97bc72e-7ff5-4108-ac5a-4b893d4eaa0d`. During integration,
the four duplicated zero-test helpers were replaced by the existing helpers
from `ResidueLocalChartProof`, moved into `Modules.MorphismVanishing` and
renamed for the shared API. The six section assertions and the Picard
corollaries retain their reviewed statements and proof arguments.
