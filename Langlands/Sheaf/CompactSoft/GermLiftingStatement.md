# Compact-germ lifting with a c-soft kernel

Author: Worker 865. Statement formulation and proof-route specification: Worker 310.

The module imports the published `Langlands.Sheaf.CompactSoft` and defines the
closed proposition
`Langlands.Sheaf.CompactSoft.CompactGermLiftingStatement.{u}`. It states a
conclusion to be proved in a separate module.

## Statement and conventions

For every locally compact Hausdorff space `X : TopCat.{u}`, every commutative
ring `R : Type u`, and every short complex `S` of sheaves of `R`-modules on `X`,
if `S` is short exact and its first sheaf `S.X₁` is c-soft, then for every
compact subset `K` of `X` the map

```lean
((Langlands.Sheaf.CompactSoft.setSectionsFunctor R K).map S.g.hom)
```

is surjective. Its source is
`setSections S.X₂.presheaf K` and its target is
`setSections S.X₃.presheaf K`. Here `S.g : S.X₂ ⟶ S.X₃` is the second arrow of
the short complex, and `S.g.hom` is its underlying presheaf morphism.

`setSections F K` is the colimit of `F(U)` over the open neighbourhoods `U` of
`K`, with restriction maps as transition maps. Thus an element is represented by
a section on some open neighbourhood, and equality permits shrinking that
neighbourhood. The published `IsCSoft` predicate requires every such germ along
a compact set to come from a global section with compact support.

The proposition quantifies over `X`, its `T2Space` and `LocallyCompactSpace`
instances, `R`, its `CommRing` instance, and `S`, followed by short exactness,
c-softness of `S.X₁`, `K`, and compactness of `K`, in that order. It has the
single universe parameter `u`; the modules use `ModuleCat.{u} R`. There are no
additional hypotheses, including no paracompactness assumption.

The conclusion concerns germs along a compact set. It makes no surjectivity
claim for sections over arbitrary open sets, and it does not require a
compactly supported lift in the middle sheaf.

## Provenance and proof obligation

This is a derived intermediate lemma in the finite-compact-cover proof of
Kashiwara–Schapira, *Sheaves on Manifolds*, §2.5, Proposition 2.5.8,
printed p.105. It is not a verbatim named proposition of that book.
The section's standing convention on printed p.102 is that its locally compact
spaces are Hausdorff. Proposition 2.5.1(ii), printed pp.102–103, identifies
sections on a compact subset of a Hausdorff space with the colimit of sections
on open neighbourhoods. Definition 2.5.5, printed p.104, defines c-softness
using global sections; Proposition 2.5.6 on p.105 supplies the equivalent
compact-support extension formulation underlying the published predicate.
These comparisons explain the mathematical conventions; this module does not
formalize them.

The proof of Proposition 2.5.8 lifts a quotient section on finitely many compact
pieces. On the overlap of two pieces the difference of two lifts lies in the
kernel. C-softness extends that difference to a global kernel section, which
corrects one lift so that the two glue. Repeating the construction gives a lift
over their finite union. The proposition isolated here applies this argument
to an arbitrary compact set and uses the existing colimit-germ interface.
Its future proof must also shrink representing open neighbourhoods so that
germ agreement gives actual agreement on overlaps; local compactness and
Hausdorffness provide the required compact neighbourhoods and shrinking.

This file only defines the proposition. It supplies neither that finite gluing
proof nor the compact-support exactness conclusion of Proposition 2.5.8.
The intended successor proves exactly this closed proposition using local
surjectivity of epimorphisms of sheaves, left exactness of sections on open
sets, and reusable finite compact gluing lemmas.

## Source

Masaki Kashiwara and Pierre Schapira, *Sheaves on Manifolds*, Grundlehren der
mathematischen Wissenschaften 292, Springer, 1990, §2.5, printed pp.102–105
(one-based PDF pages 112–115), especially Proposition 2.5.1(ii),
Definition 2.5.5, Proposition 2.5.6 and the proof of Proposition 2.5.8.

Registered source:
`provided-1a1e547af2f3cfc223f73a05ef9491bbf82f0d1976763c0d9c200813c4b8b658`,
file `literature/Kashiwara, Schapira - Sheaves on Manifolds, Grundlehren 292 (1990).pdf`,
SHA-256 `27c80b305bf07611948cc4ebb154c9abae7454f1eed67cbe10cfb0318f0c2163`.
Worker 865 read these pages and visually checked p.105. No source-specific
errata note was present in the current public notes at authoring time.
