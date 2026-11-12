# Affineness descends along flat surjective morphisms of affine schemes

Authors: Worker 1497.

This module proves one theorem,

```
FaithfullyFlatAffineDescent.isAffine_of_isPullback
    {P X Y G : Scheme} {fst : P ⟶ X} {snd : P ⟶ G} {π : X ⟶ Y} {q : G ⟶ Y}
    (h : IsPullback fst snd π q) [IsAffine Y] [IsAffine G]
    [Flat q] [Surjective q] [IsAffine P] : IsAffine X
```

In words: let `q : G ⟶ Y` be a flat surjective morphism of affine schemes and
`π : X ⟶ Y` any morphism. If the fibre product `P = X ×_Y G` is affine, then `X` is
affine.

## Provenance

This is the key case of the fpqc descent of affineness: the Stacks Project, Descent
chapter (version ed88ff78, compiled July 14, 2026), Lemma 23.20 (Tag 02L5), PDF p.57,
registered source `stacks-descent-ed88ff78-2026`: “The property P(f) = ‘f is affine’
is fpqc local on the base.” Its proof treats exactly this situation, a flat
surjective morphism `g : S' ⟶ S` of affine schemes and `f : X ⟶ S` with affine base
change `X'`, and shows that `X` is affine by comparing `X` with `Spec Γ(X, 𝒪_X)`
after base change. The Lean proof below follows that comparison, using Mathlib's
descent of isomorphisms in place of the source's direct argument. The current Mathlib has no
fpqc descent of `IsAffineHom` or of `IsAffine`. This module proves this case for use
in `Langlands.GroupScheme.HomogeneousQuotientTower`. It is an internal helper lemma.
Its Lean statement is not taken from a published Lean source.

## Proof

1. **`X` is quasi-compact and quasi-separated.** `fst` is a base change of `q`, so
   it is surjective and quasi-compact (`MorphismProperty.of_isPullback`). Hence `X`
   is the continuous image of the compact space `P`. The published
   `FieldExtensionAffineDescent.quasiSeparatedSpace_of_surjective` gives that `X`
   is quasi-separated, because `P` is affine and `fst` is surjective.
2. **Global sections form a pushout.** Since `X` is quasi-compact and
   quasi-separated and `q` is a flat morphism of affine schemes, the published
   `LocallyQuasiFiniteDescent.isPushout_appTop_of_isPullback` shows that the square
   of global-section maps `Γ(Y) → Γ(X)`, `Γ(Y) → Γ(G)`, `Γ(X) → Γ(P)`,
   `Γ(G) → Γ(P)` is a pushout of commutative rings. Mathlib's
   `isPullback_SpecMap_of_isPushout` turns it into a pullback square of the spectra
   `hR`.
3. **The comparison map is a base change of a faithfully flat map.** `Spec Γ(q)` is
   flat (`Scheme.Hom.flat_appTop`) and surjective (it is isomorphic as an arrow to
   `q`, by `arrowIsoSpecΓOfIsAffine`). Its base change `Spec Γ(fst)` along `hR` is
   therefore flat and surjective.
4. **`P` is the base change of `X ⟶ Spec Γ(X)`.** The square
   `G ⟶ Spec Γ(G)` over `Y ⟶ Spec Γ(Y)` is a pullback, because both horizontal maps
   are isomorphisms (`IsPullback.of_horiz_isIso`). Pasting it with `h` and
   cancelling `hR` on the right (`IsPullback.of_right`) shows that the square with
   top `P ⟶ Spec Γ(P)`, bottom `X ⟶ Spec Γ(X)`, and vertical maps `fst` and
   `Spec Γ(fst)` is a pullback.
5. **Descent of isomorphisms.** `P ⟶ Spec Γ(P)` is an isomorphism because `P` is
   affine. Isomorphisms descend along surjective, flat, quasi-compact morphisms
   (Mathlib's `MorphismProperty.of_isPullback_of_descendsAlong` for
   `MorphismProperty.isomorphisms`). So `X ⟶ Spec Γ(X)` is an isomorphism, which is
   the definition of `IsAffine X`.
