# Rational restriction on the actual root spans

Let `k` and `L` be fields in the same arbitrary universe, with a `k`-algebra
structure on `L`. Let `G` be an affine, locally finite type quasi-split group
scheme over `k`. Let `a : S → G` be a maximal split torus, let `j : T → G`
be a maximal torus, and let `f : S → T` factor `a` through `j`. Assume that
`T_L` is split. There are no characteristic, finiteness, separability or Galois
hypotheses on `L/k` in the constructions below.

`SplittingFieldRootRestriction.characterMap` first restricts an actual
character of `T_L` along `f_L`, then descends its character of `S_L` by the
inverse of the character pullback equivalence for the original split torus
`S`. Its scalar extension to the rationals is `rationalMap`. On a rationalized
integral character this map is the rationalization of `characterMap`.

The total root restriction of `QuasiSplitRootRestriction` shows that every
root of `j_L` maps to an actual root of `a`. Since these actual roots generate
the two rational root spans, `rationalMap_rootSpan_le` permits restriction to

```
IsQuasiSplit.rationalRootRestriction :
  relativeRootSpan j_L →ₗ[ℚ] relativeRootSpan a.
```

These are the spans of all actual roots; the ambient rationalized character
modules may have additional central directions. On each actual root vector,
`rationalRootRestriction_rootVector` gives the vector of its total restricted
root. The published total-root surjectivity, followed by the fact that the
actual root vectors span, proves `rationalRootRestriction_surjective`.

For any `k`-automorphism of `L`, `rootRestriction_galois` states that ordinary
Galois transport of an actual root has the same restricted root. The proof
compares the characters after pullback to `S_L`. Naturality of Galois transport
moves the action through `f_L`; canonical pullbacks from `S` are fixed by that
action. Injectivity of the split-torus character pullback then gives equality
over `k`. This argument does not require `L/k` to be a Galois extension.

`rationalRootRestriction_injective_of_rootSystems` has additional explicit
inputs. It takes rational root pairings `P` and `Q` on the target and source
root spans, with their dual spaces, such that:

- Both pairings are root systems.
- `Q` is irreducible.
- The root images of `P` and `Q`, after the subtype inclusions, are exactly the
  rationalized actual relative roots of `a` and actual roots of `j_L`, respectively.
- The full indexed root-coroot pairing of `P` is symmetric.

The two index types may lie in arbitrary independent universes. The exact
root-image equalities and the root-vector formula show that rational restriction
takes every `Q`-root to a `P`-root. The theorem then applies
`SymmetricRootPairingForm.injective_of_mapsTo_roots`. No reducedness,
crystallographicity, finite root index, target irreducibility, or compatibility
between the two coroot maps is an extra hypothesis of this implication.

`rootRestriction_injective_of_rationalRootRestriction` uses the injective
rationalization of the character lattice of the split torus `T_L` to detect
equality of actual roots. Finally,
`root_galois_eq_self_of_rationalRootRestriction_injective` combines this
injectivity with `rootRestriction_galois` to prove that every actual root
character of `j_L` is fixed by every `k`-automorphism of `L`.

This is an internal derived construction from actual character restriction,
total quasi-split root restriction, root-vector spanning, Galois naturality and
the generic symmetric-root-pairing injectivity criterion. It does not assert
existence of the supplied irreducible root system or symmetric full target
pairing. It does not establish triviality on all characters, splitting of `T`
over `k`, a stable chamber, or the host local anisotropic affine-diagram theorem.
