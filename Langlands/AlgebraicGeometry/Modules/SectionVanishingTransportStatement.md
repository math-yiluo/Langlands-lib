# Zero tests and transport of actual pulled-back sections

`Langlands.SchemeModule.SectionVanishingTransportStatement` is an internal,
Prop-valued package of six compatibility assertions for the published
actual `Scheme.Modules` constructions. It is a conjunction of six
universally quantified clauses, with one universe parameter `u`. Every
scheme in every clause is an arbitrary scheme in `Scheme.{u}`; modules
`M N : X.Modules` (sheaves of modules over the structure sheaf), global
sections `s : GlobalSections M` and scheme morphisms are arbitrary. No
rank-one, field, finiteness, local-freeness, smoothness, properness,
projectivity or ampleness hypothesis is imposed.

## Objects used

All of these come from the imported module
`Langlands.AlgebraicGeometry.Modules.SectionResidue` and its imports.

- `GlobalSections M` is `Γ(M, ⊤)`, the abelian group of sections of `M`
  over the whole scheme.
- `sectionHom M s : structureModule X ⟶ M` is the module-sheaf morphism
  from the structure module that sends `1` to `s`.
- `Scheme.Modules.pullback f : X.Modules ⥤ Y.Modules` is Mathlib's pullback
  functor along `f : Y ⟶ X`.
- `pullbackSection f M s`, a global section of
  `(Scheme.Modules.pullback f).obj M`, is the value at `1` of the morphism
  obtained by composing the inverse of the canonical unit comparison
  `pullbackUnitIso f` with `(Scheme.Modules.pullback f).map (sectionHom M s)`.
- For a module-sheaf morphism `φ : M ⟶ N`, `φ.app ⊤` is its component on
  global sections.

In the clauses, `0` is the zero element of a group of global sections,
or the zero module-sheaf morphism.

## The six clauses, in order

1. For every scheme `X`, module `M` and section `s`:
   `sectionHom M s = 0 ↔ s = 0`.
2. For all schemes `X` and `Y`, every `f : Y ⟶ X`, module `M` on `X` and
   section `s`: `pullbackSection f M s = 0` if and only if
   `(Scheme.Modules.pullback f).map (sectionHom M s) = 0`.
3. For all schemes `X`, `Y` and `Z`, every `f : Z ⟶ Y` and `g : Y ⟶ X`,
   module `M` on `X` and section `s`: the successive pullback
   `pullbackSection f ((Scheme.Modules.pullback g).obj M) (pullbackSection g M s)`
   is zero if and only if `pullbackSection (f ≫ g) M s` is zero. The two
   sections lie in different modules on `Z`, so this compares zero
   conditions only; it asserts no equality between them.
4. For all schemes `X` and `Y` and every `f : Y ⟶ X` that is an isomorphism
   of schemes (the instance argument `[IsIso f]`), module `M` and section
   `s`: `pullbackSection f M s = 0 ↔ s = 0`.
5. For all schemes `X` and `Y`, every `f : Y ⟶ X`, modules `M` and `N` on
   `X`, morphism `φ : M ⟶ N` and section `s` of `M`: the equation
   `pullbackSection f N (φ.app ⊤ s) = ((Scheme.Modules.pullback f).map φ).app ⊤ (pullbackSection f M s)`
   holds.
6. For all schemes `X` and `Y`, every `f : Y ⟶ X`, modules `M` and `N` on
   `X`, isomorphism `e : M ≅ N` and section `s` of `M`:
   `pullbackSection f N (e.hom.app ⊤ s) = 0 ↔ pullbackSection f M s = 0`.

## Provenance and scope

This is derived internal provenance, not a translation of a named
literature theorem: the assertions express the expected functorial
behavior of the Library's `GlobalSections`, `sectionHom` and
`pullbackSection`. The statement was split from the separating-line-bundle
proof task, where it is needed to transport `Picard.VanishesAlong`, which
is defined as zero of the actual pulled-back section. That predicate does
not occur in this statement. No literature result is imported or assumed,
and this statement module proves none of the six clauses. In particular it
makes no claim that pullback along an arbitrary scheme morphism reflects
zero: clause 4 needs `f` to be an isomorphism of schemes, and clause 2
compares one zero condition after pullback with another.
