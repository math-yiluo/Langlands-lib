# Action quotients from a smooth relation space

Author: Worker 5132.

This module is the second half of the proof of
`SmoothStabilizerActionQuotientStatement`. It proves the conclusion of that statement for an
action `a` of a group scheme `G` on `V` as soon as a suitable "relation space" `B` is
available. In the Stacks Project argument that space is `R' = R/G`. The module does not
construct `B` and makes no assertion about the stabilizer.

## Provenance

The argument is derived. It follows the second half of the proof of Stacks Project,
Morphisms of Algebraic Stacks, Proposition 101.28.9 (Tag 06QJ), (2) ⇒ (1). There
`s', t' : R' → U` are flat and locally of finite presentation, `j' = (t', s')` is an
equivalence relation, and "Bootstrap, Theorem 80.10.1 shows that `X = U/R'` is an algebraic
space". The groupoid is the action groupoid `G × V ⇉ V`. In place of Theorem 80.10.1 this
module uses the Library's smooth special case `smoothRelationQuotient`
(`SmoothRelationQuotientProof.lean`). The citations are those recorded in
`SmoothStabilizerActionQuotientStatement.md`: registered source
`stacks-free-action-stabilizer-quotient-06PH-06QJ-2026-11-10` (Tag 06QJ) and
`stacks-smooth-quotient-local-finite-type-2026-11-01` (Tag 04S6). The source gives two
facts in a few words: `j'` is an equivalence relation, and `U/R'` is the quotient of `U` by
the groupoid. Below they are proved directly: by étale-local lifting of sections of `R'`
through `R → R'`, and by the universal property of the étale sheafification.

## Setting and hypotheses

`S : Scheme.{u}`, `G : GroupScheme S`, `V : Over S`, `a : SchemeAction G V`. Points of
`V` over a test scheme `T` are written `x : T ⟶ V`. The data are:

- an algebraic space `B` over `S` with maps `s', t' : B ⟶ h_V` of presheaves;
- a map `q : h_{G × V} ⟶ B` with `q ≫ s' = h(a.hom)` (the action) and
  `q ≫ t' = h(snd G.X V)` (the projection);
- `hinj`: for every test scheme `T`, the map `r ↦ (s' r, t' r)` on `B(T)` is injective;
- `hq`: `q` is locally surjective for the big étale topology `Scheme.etaleTopology.over S`;
- `hsm : HasSmoothProjections B s' t'`: on some surjective étale scheme atlas of `B`,
  both `s'` and `t'` are given by smooth morphisms of schemes;
- `hV : LocallyOfFiniteType V.hom`.

## Declarations

- `IsSmooth.comp_iso`: composing a smooth presheaf transformation with an isomorphism
  keeps it smooth. It is proved like `IsEtale.comp_iso` (`RelativeHelpers.lean`), from the
  fact that `Smooth` respects isomorphisms.
- `isSheaf_etale`, `isSheaf_etale_scheme`, `isSheaf_etale_fppfSheaf`: algebraic spaces,
  represented functors and fppf sheaves are sheaves of types for the big étale topology.
  The proof applies `Sites.etaleTopologyOver_le_fppfTopologyOver`.
- `relation_of_sieve`: for jointly injective `s', t'`, the relation
  `relation B s' t'` is étale local. Suppose that on an étale covering sieve of `T` every
  restriction of `(x, y)` has a witness in `B`. Joint injectivity makes these witnesses
  agree on overlaps. They glue in the étale sheaf `B` to a section `r` over `T`. Then
  `s' r = x` and `t' r = y` hold because `h_V` is separated.
- `ActRel`, `actRel_equivalence`, `ActRel.comp`: the orbit relation over a single test
  scheme, `x = g · y` for some `g : T ⟶ G.X` (`a.act g y`). It is an equivalence relation
  (`act_one`, `act_mul`, inverses in the group `T ⟶ G.X`) and stable under pullback
  (`a.naturality`).
- `relation_of_actRel`: if `x = g · y` then `q(g, y)` witnesses `relation B s' t' T x y`.
- `exists_sieve_actRel`: if `r` witnesses `relation B s' t' T x y`, then on the image
  sieve of `r` under `q`, which is an étale covering by `hq`, the points `x` and `y` lie
  in one orbit. Over each `f : W ⟶ T` in that sieve, choose `α : W ⟶ G × V` with
  `q α = r|_W`. Then `f ≫ x = α ≫ a.hom` and `f ≫ y = α ≫ snd`, so `f ≫ x` is
  `(α ≫ fst) · (f ≫ y)`.
- `relation_iff`: `relation B s' t' T x y` holds iff `x` and `y` are in one orbit
  étale locally on `T`. This combines the three previous items.
- `isEquivalenceRelation`: `IsEquivalenceRelation B s' t'`. Injectivity is `hinj`.
  Reflexivity uses `g = 1`. Symmetry and transitivity follow from `relation_iff`, applied
  on the intersection of two covering sieves for transitivity.
- `hom_ext_of_isLocallySurjective`: two maps into an étale sheaf agree when they agree
  after an étale locally surjective map. The proof uses separatedness on image sieves.
- `coequalizes_of_invariant`: let `k : h_V ⟶ F` be a map into an étale sheaf with
  `h(a.hom) ≫ k = h(snd) ≫ k`. Then `s' ≫ k = t' ≫ k`, because both sides agree after `q`.
- `actionQuotient_of_relationSpace`: the main theorem. Its conclusion is exactly the
  conclusion of `SmoothStabilizerActionQuotientStatement` for this action `a`:
  1. There are an algebraic space `X` and `π : h_V ⟶ X` with `IsFppfActionQuotient a π`.
  2. For every algebraic space `X` and every `π` with `IsFppfActionQuotient a π`, we have
     `IsSmooth π.hom`, `IsSurjective π.hom` and `LocallyOfFiniteTypeOverBase X`.

## Proof of `actionQuotient_of_relationSpace`

1. `isEquivalenceRelation` gives the witness `h`. `smoothRelationQuotient S V B s' t' h hsm
   hV` shows several things about the canonical étale quotient sheaf
   `quotientSheaf B s' t' h`: it is an fppf sheaf and has representable diagonal, and it
   has a surjective étale atlas `c` from a scheme `W` locally of finite type over `S`.
   It also shows that `quotientMap B s' t' h` is smooth and surjective. These data give an
   algebraic space `X` with `X.presheaf = (quotientSheaf B s' t' h).obj`, and
   `π := ObjectProperty.homMk (quotientMap B s' t' h)`.
2. `π` coequalizes the action and the projection. Rewrite `h(a.hom) = q ≫ s'` and
   `h(snd) = q ≫ t'`, then apply `quotientMap_coequalizes`.
3. The cofork is a colimit in `FppfSheaf S`. Take a cofork `k : h_V ⟶ F`. Each fppf sheaf is
   an étale sheaf, so `coequalizes_of_invariant` gives `s' ≫ k = t' ≫ k`. The descended
   map is `quotientSheafDesc`, with factorization `quotientMap_desc` and uniqueness
   `quotientSheaf_hom_ext` (`SmoothRelationQuotientDescent.lean`).
4. Let `π'` be any fppf quotient map with target `X'`.
   `IsColimit.coconePointUniqueUpToIso` gives an isomorphism `e : X ≅ X'` of fppf sheaves
   with `π ≫ e.hom = π'`. Hence `π'.hom = quotientMap ≫ e.hom`.
   - `π'.hom` is smooth by `IsSmooth.comp_iso`.
   - It is surjective by `IsSurjective.comp_iso` (`AtlasIsoTransport.lean`).
   - `X'` has the transported atlas `c ≫ e.hom`, by `HasAtlasProperty.of_iso`
     (`StructuralAtlasGeometry.lean`).

The equivalence relation is proved without forming an orbit-class sheaf: `relation_iff`
identifies the relation with the étale-local orbit relation directly.
