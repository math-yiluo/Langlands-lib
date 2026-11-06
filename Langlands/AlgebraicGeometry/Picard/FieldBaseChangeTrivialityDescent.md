# Triviality of line bundles descends along field extensions

Module `Langlands.AlgebraicGeometry.Picard.FieldBaseChangeTrivialityDescent`.

## Main result

`fieldBaseChangeTrivialityDescent`: let `k` and `K` be fields,
`g : Spec K ⟶ Spec k` any morphism of schemes, and `f : X ⟶ Spec k` a smooth,
proper and geometrically connected morphism. Let `L` be a locally free sheaf of
rank one on `X` (`IsLocallyFreeRankOne L`). If the pullback of `L` along the
first projection `X ×_{Spec k} Spec K ⟶ X` is isomorphic to the structure sheaf of
`X ×_{Spec k} Spec K`, then `L` is isomorphic to the structure sheaf of `X`.

The result only asserts existence (`Nonempty`) of the isomorphism. It needs no
rational point or rigidification.

## Helper lemmas

- `pullback_nonempty_iso_structureSheaf`: the pullback of a module sheaf
  isomorphic to the structure sheaf is again isomorphic to the structure sheaf.
  This uses the canonical comparison `Langlands.Scheme.Modules.pullbackUnitIso`.
- `nonempty_iso_of_pullback_isIso`: if `a` is an isomorphism of schemes and the
  pullbacks of `N` and `N'` along `a` are isomorphic, then `N ≅ N'`. The proof
  pulls back along `inv a` and uses `pullbackComp`, `pullbackCongr` and
  `pullbackId`.
- `nonempty_iso_structureSheaf_of_pullback_isIso`: the special case
  `N' = 𝒪`.

## Proof of the main result

1. `X` is geometrically integral over `k` by
   `Langlands.AbelianScheme.smoothGeometricIntegrality`. It is flat because it is
   smooth (Mathlib instance).
2. For every `k`-algebra `B`, the base change `X_B ⟶ Spec B` is again smooth,
   proper and geometrically connected. So
   `Langlands.AlgebraicGeometry.smoothProperConnectedGlobalFunctions` makes its
   map on global sections an isomorphism, hence bijective. This is the
   global-functions hypothesis of the seesaw.
3. Apply `noetherianLineBundleSeesaw` with `c = f`, the noetherian base
   `T = Spec k`, `t = 𝟙`, the pullback `M` of `L` to `X ×_k k`, and the
   structure sheaf. It gives a closed immersion `ι : Z ⟶ Spec k` through which a
   morphism `ψ : T' ⟶ Spec k` factors exactly when the two pullbacks are locally
   isomorphic on `T'`.
4. Take `ψ = g`. The given trivialization over `X ×_k K` is compared with the
   pullback of `M` to `(X ×_k k) ×_k K` through the map `φ` into `X ×_k K` defined
   by `pullback.lift`. Restricting the resulting global isomorphism to `⊤` gives the
   local condition, so `g` factors through `ι`.
5. Hence `Z` has a point. Since `Spec k` has exactly one point, `ι` is
   surjective. As `Spec k` is reduced, Mathlib's
   `isIso_of_isClosedImmersion_of_surjective` shows that `ι` is an isomorphism.
6. Thus `𝟙 (Spec k)` factors through `ι`, and the seesaw gives an open `U` of
   `Spec k`, containing its point, over which the pullbacks to
   `(X ×_k k) ×_k k` are isomorphic. The preimage `W` of `U` is everything, so the
   open immersion `W.ι` is an isomorphism (`isIso_iff_isOpenImmersion_and_surjective`).
   Restriction along `W.ι` is pullback (`restrictFunctorIsoPullback`). Pullback
   along an isomorphism reflects isomorphisms, so it can be removed. Doing the same
   for the first projections from `(X ×_k k) ×_k k` and from `X ×_k k`, which are
   isomorphisms because they are base changes of identities, gives `L ≅ 𝒪_X`.

## Provenance

This is a derived, internal helper with no separate literature statement. It is
the familiar fact that triviality of a line bundle on a proper, geometrically
integral scheme over a field can be checked after a field extension. Here it is
obtained directly from the Library's `noetherianLineBundleSeesaw` over the
noetherian base `Spec k`; see that statement's Markdown for the source of the
seesaw. The openness proof for the Picard-zero locus (task `40d423ed`) uses it to
descend triviality of the Mumford bundle from a geometric fibre over `Spec K` to
the fibre over the residue field `κ(p)`.
