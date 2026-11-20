# Transport of polarizations along isomorphisms of abelian schemes

This module proves that relative polarizations, in the sense of the Library's
`AbelianScheme.IsPolarization`, are transported along isomorphisms of abelian schemes.
The dual witnesses on the two sides may be arbitrary. It introduces no statement and no
hypothesis beyond the named `Prerequisites` inputs that the predicate already uses.

## Main result

`DualWitness.isPolarization_iso_transport P e WA WB lam h`. Let `P : Prerequisites.{u}`,
let `e : A ≅ B` be an isomorphism of abelian schemes over a scheme `S`, and let
`WA : DualWitness A` and `WB : DualWitness B` be dual witnesses. Let
`lam : B ⟶ WB.dual P` with `h : WB.IsPolarization P lam`. Then

```
WA.IsPolarization P (e.hom ≫ lam ≫ WA.map P WB e.hom).
```

Here `WA.map P WB e.hom : WB.dual P ⟶ WA.dual P` is the Library's contravariant dual map.

The selected definition `DualWitness.transportMap P e WA WB lam : A ⟶ WA.dual P` is this
transported map, `e.hom ≫ lam ≫ WA.map P WB e.hom`, by definition.
`DualWitness.isPolarization_transportMap` restates the main result for it.
The transported map has the same shape as the right-hand side of
`PolarizedIso.polarization_eq`. The theorem is intended for building data on an abelian
scheme isomorphic to that of a given datum, as in the existence half of the Zariski gluing
for `moduliFunctor`.

## Auxiliary results (namespace `Langlands.AbelianScheme`)

- `isIso_hom_of_iso e` (instance): the underlying scheme morphism `hom e.hom` of an
  isomorphism of abelian schemes is an isomorphism, with inverse `hom e.inv`.
- `isIsogeny_of_iso e`: isomorphisms of abelian schemes are isogenies. The proof applies the
  Library's `GroupScheme.isIsogeny_of_isIso` to the underlying group-scheme isomorphism.
- `dualBaseChangeMap_dualPullback stability universality b g hA hB fB`. Let `g : A ⟶ B` and
  `fB : B.X ⟶ dualScheme B hB`, and form the transported map `g ≫ fB ≫ dualSchemeMap g`.
  Its base change `dualBaseChangeMap` along `b` equals the transport of
  `dualBaseChangeMap B hB universality b fB` along the base-changed homomorphism
  `(baseChange b).map g`. Both sides use the dual witnesses `hasDualScheme_baseChange`.
  The proof unfolds `dualBaseChangeMap` (pullback of the map followed by
  `dualSchemeBaseChangeIso`). It then uses the Library's naturality lemma
  `dualSchemeMap_dualSchemeBaseChangeIso`, which needs the prerequisite
  `PicardZeroPullbackStatement`.
- `hasAmpleMumfordAfterBaseChange_iso`: for an isomorphism `e : A ≅ B`, the condition
  `HasAmpleMumfordAfterBaseChange … B hB universality b fB` implies the same condition for
  `A`, `hA` and the transported map `e.hom ≫ fB ≫ dualSchemeMap e.hom hA hB`. After
  rewriting with `dualBaseChangeMap_dualPullback`, this is the Library's
  `hasAmpleMumfordPresentation_dualPullback` for the homomorphism `(baseChange b).map e.hom`.
  Its underlying morphism is an isomorphism, hence affine.
- `hasFieldAmpleMumfordPresentation_iso`: the same transport for
  `HasFieldAmpleMumfordPresentation` over `Spec k`. That predicate asks for
  `HasAmpleMumfordAfterBaseChange` along `Spec K ⟶ Spec k` for some field extension
  `k →+* K`. The proof keeps the same extension.

## Proof of the main result

`IsPolarization` has two conjuncts: an isogeny condition, and a condition at every
geometric point.

1. *Isogeny.* `e.hom` is an isogeny, and so is `WA.map P WB e.hom`, because it is the forward
   map of the isomorphism `DualWitness.mapIso P WA WB e`. Hence the composite with `lam` is
   an isogeny (`IsIsogeny.comp`).
2. *Geometric points.* Fix an algebraically closed field `K` and `s : Spec K ⟶ S`. The
   underlying map of the transported homomorphism is, by definition,
   `(groupHom e.hom).hom.hom ≫ (groupHom lam).hom.hom ≫ dualSchemeMap e.hom WA.hasDual
   WB.hasDual`. `dualBaseChangeMap_dualPullback` rewrites its base change along `s` as the
   transport of `dualBaseChangeMap B WB.hasDual P.universality s (groupHom lam).hom.hom`
   along `(baseChange s).mapIso e`. The hypothesis `h` gives
   `HasFieldAmpleMumfordPresentation` for that map over `B`. `hasFieldAmpleMumfordPresentation_iso`
   transports it to `A`.

## Provenance

Internal. Polarizations are invariant under isomorphism, a standard fact. The module derives
it from the Library's definitions. It combines the published affine transport of ample
Mumford presentations (`AffineMumfordTransport`), the naturality of the dual base-change
comparison (`DualAbelianBaseChangeNaturalityProof`), and the isogeny API, and it makes no
literature claim. The predicate itself follows the sources cited in `RelativePolarization`
(Kottwitz 1992, Section 5; Edixhoven–van der Geer–Moonen, Chapter XI, (11.5)–(11.6)).
