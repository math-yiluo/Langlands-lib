# The Isom presheaf as an equalizer of Hom presheaves

For two coherent families `M N : FamilyGroupoid f T`, this module exhibits the
Library's actual Isom presheaf `FamilyGroupoid.isomPresheaf f M N` as an
equalizer of Hom presheaves. A point over a scheme `Z` over `T.left` is an
isomorphism of the pulled-back families. It amounts to a pair of module maps
`a : M ⟶ N` and `b : N ⟶ M` of the pullbacks with `a ≫ b = 𝟙` and `b ≫ a = 𝟙`.
All presheaves live on the entire slice `Over T.left`, and the comparison is
natural for all restriction maps.

## Restriction lemmas

Restriction in `isomPresheaf` is coherent restriction (Mathlib's `pullHom`) in
the morphism-lifted core pseudofunctor. Restriction in `homPresheaf` is
coherent restriction in `Family.pseudofunctor f`, followed by a universe lift.
They are compared in two generic steps, each proved for an arbitrary Cat-valued
pseudofunctor `F` and then specialized.

- `homLift_pullHom_down`, `presheafHom_homLift_map_down`: in the
  morphism-lifted pseudofunctor `homLift F`, coherent restriction of a lifted
  morphism is the lift of the coherent restriction in `F`. The proof
  substitutes the composite maps, unfolds `pullHom`, rewrites `mapComp'` to
  `mapComp`, and closes by `rfl`. It is the same argument as the private lemma
  `lifted_pullHom_down` in the Library module `IsomPresheaf`.
- `corePseudofunctor_pullHom_iso_hom`, `presheafHom_corePseudofunctor_map_iso_hom`:
  in `corePseudofunctor F`, the forward morphism of the coherent restriction
  of a core morphism is the coherent restriction in `F` of its forward
  morphism. The proof is the same.
- `FamilyGroupoid.isomPresheaf_map_iso_hom`: restricting a point of the Isom
  presheaf restricts its forward module map as a point of `homPresheaf f M N`.
  It chains the two generic lemmas.
- `FamilyGroupoid.isomPresheaf_map_iso_inv`: the same for the inverse map, as a
  point of `homPresheaf f N M`. The proof uses `Iso.inv_ext`, the forward
  lemma, and the Library laws `homPresheaf_map_comp` and
  `homPresheaf_map_identity`. Restriction preserves composition and
  identities, so the restricted inverse is inverse to the restricted forward
  map.

## Constructions

- `isomToHom`, `isomToHomInv`: the natural maps from the Isom presheaf to
  `homPresheaf f M N` and `homPresheaf f N M` taking an isomorphism to its
  forward and its inverse module map. Their naturality is the two restriction
  lemmas. `isomToHom_app_down` and `isomToHomInv_app_down` record the
  components, and `isomToHom_app_injective` states that a point is determined
  by its forward map.
- `homPairComposites`: the map `(a, b) ↦ (a ≫ b, b ≫ a)` from
  `FunctorToTypes.prod (homPresheaf f M N) (homPresheaf f N M)` to
  `FunctorToTypes.prod (homPresheaf f M M) (homPresheaf f N N)`. It is built
  from the Library's `homCompose`. Its naturality is `homPresheaf_map_comp`.
- `homPairIdentities`: the map with constant value `(𝟙, 𝟙)` between the same
  presheaves. It is built from `homIdentity`, and its naturality is
  `homPresheaf_map_identity`.
- `isomToHomPair`: the pairing `FunctorToTypes.prod.lift` of `isomToHom` and
  `isomToHomInv`. `isomToHomPair_comp` states that it equalizes the two maps
  above, which is `hom_inv_id` and `inv_hom_id`.
- `isomPairFork`: the resulting fork.
- `isomPairForkIsLimit`: this fork is a limit. Given another fork `s`, the
  private `forkLift` sends a point to the isomorphism with forward map the
  first component of `s.ι` and inverse the second. The fork condition gives
  the two inverse equations. Naturality of `forkLift` reduces to naturality of
  the first component, through the forward restriction lemma. The
  factorization through `isomPairFork` holds by definition. Uniqueness holds
  because a point is determined by its forward map (`Core.hom_ext`).

## Provenance

This is a derived formalization of the identification in the proof of Stacks
Project Proposition 99.4.3 (Section 99.4, Tag 08K7):
`Isom(F, G) = (H' ×_B H) ×_{c, I ×_B I', σ} B`, where `c(u', u) =
(u ∘ u', u' ∘ u)` and `σ` is the section `(id_F, id_G)`. The retained original
is `08K7.html` in registered source `stacks-isom-functor-08k7-2026-11-02`
(folder SHA-256
`a05b61ba562e7e65dd2b64446e779a6bb67af1846c0a00f4a656d64a2b2c27b5`). The
source omits these details ("Some details omitted"). Here the fibre product
with the section `σ` is phrased as the equalizer of `c` and the constant
identity map, at the level of presheaves on the full slice, before any
representability is used. No properness, flatness or finiteness hypothesis is
used in this module.
