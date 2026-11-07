# Split field groups with matching simple-root parametrizations are isomorphic

Module `Langlands.GroupScheme.Reductive.LocalSplitFieldComparison`, namespace
`Langlands.GroupScheme.LocalSplitCell` (one lemma in `Langlands.GroupScheme.splitTorus`).

## Setting

`Ga`, `rootPoint`, `weylPoint` and `IsRootParametrization` are as in the Library module
`Langlands.GroupScheme.Reductive.LocalSplitCell`. `T_I = splitTorus (Spec k) I` is the coordinate
split torus. A coordinate root datum is `P : RootDatum J (I → ℤ) (I → ℤ)`. Its realization
`fieldRealization k P` (Library, `Reductive/FibrewiseRootDatum.lean`) is the same datum on the
character and cocharacter lattices of `T_I`. Its root `a` is the character `exponentCharacter (P.root a)`.

## Results over a ring

- `splitTorus.exponentCharacter_neg`: `exponentCharacter (-m) = -exponentCharacter m`.
- `rootPoint_zero`: `rootPoint u Z 0 = 1`.
- `IsRootParametrization.rootPoint_mem`: the values of a root parametrization for `m` lie in the
  relative root subgroup of `exponentCharacter m`.
- `IsRootParametrization.rootPoint_injective`: `c ↦ rootPoint u Z c` is injective.

## Results over a field `k`

- `one_ne_zero_unit_sections`: `1 ≠ 0` in the global sections of `Spec k`.
- `fieldRealization_root_eq`, `fieldRealization_isReduced`: the roots of `fieldRealization k P`
  are the images of the roots of `P` under the inverse of `splitTorus.characterLatticeEquiv`,
  and the realization is reduced when `P` is.
- `hasNoHigherRoots_fieldRealization`: if `P` is reduced and `fieldRealization k P` is the root
  datum of `i` (`IsRootDatumOf`), no multiple `n • a` with `n ≥ 2` of a root `a` is a root of `i`.
- `gaLieEquiv k : k ≃ₗ[k] Lie(Ga k)`: the epsilon coordinate. `gaLieEquiv_one`: it sends `1` to
  the Library's standard tangent vector `VectorGroup.standardEpsilon k`.
- `fieldPinning hG i hi hred hP b u hu : SplitPinning G`. The inputs: `G` connected reductive
  (`hG`), a maximal torus `i : T_I ⟶ G` (`hi`), `J` finite, `P` reduced (`hred`),
  `fieldRealization k P` the root datum of `i` (`hP`), a base `b` of it, and root
  parametrizations `u a` of `i` for `P.root a`, one for each simple root `a` (`hu`). The pinning
  has torus `T_I`, inclusion `i`, datum `fieldRealization k P` and base `b`. For each simple
  root `a`, its trivialization `k ≃ₗ[k] weightSpace i a` is `c ↦ Lie(u a)(c ε)`, where `ε` is the
  standard tangent vector.
- `fieldPinning_rootVector`: the pinned vector of the simple root `a` is `Lie(u a)(ε)`.
- `normalizedOfRootParametrization`: a root parametrization `w` of `i` for a simple root `a` with
  `Lie(w)(ε) = Lie(u a)(ε)` is a normalized root parametrization (Library
  `SplitPinning.NormalizedRootParametrization`) of `fieldPinning … u …` at `a`.
- `exists_iso_of_simpleRootParametrizations` (main theorem). Let `G` and `H` be connected
  reductive over `k`, with maximal tori `i : T_I ⟶ G` and `i' : T_I ⟶ H`. Let `J` be finite and
  `P` reduced, and let `fieldRealization k P` be the root datum of both `i` and `i'`. Fix a base
  `b`. For each simple root `a`, suppose given root parametrizations of `i`: `u a` for `P.root a`
  and `v a` for `-P.root a`, such that `weylPoint (u a) (v a) = v_a(-1) u_a(1) v_a(-1)` lies in
  `normalizerPoints i`. Suppose the same for `u' a` and `v' a` with respect to `i'`. Then there
  is an isomorphism `Φ : G ≅ H` with `i ≫ Φ.hom = i'`. For every simple root `a` it satisfies
  `u a ≫ Φ.hom = u' a` and `Φ(v_a(-1)) = v'_a(-1)` (as base points).

## Proof

`fieldRealization_isReduced` transports linear (in)dependence of two roots along the linear
equivalence `characterLatticeEquiv`. `hasNoHigherRoots_fieldRealization` copies the Library proof
of `SplitPinning.hasNoHigherRoots`. The roots of `i` are the roots of the datum. Mathlib's
`nsmul_notMem_range_root` excludes multiples of roots in a reduced pairing. The character lattice
is torsion free because `T_I` is split.

`fieldPinning`. The trivialization is `gaLieEquiv k` followed by the Library's
`RelativeRoot.representedRootLieEquiv`. That map identifies the Lie algebra of any representative
of the root subgroup functor with the root weight space, given that higher multiples of the root
are not roots. The representative is `u a`, which represents the root subgroup functor by the
first field of `IsRootParametrization`. `fieldPinning_rootVector` holds by definition and
`gaLieEquiv_one`.

`exists_iso_of_simpleRootParametrizations`. Let `p` and `q` be the field pinnings of `G` and `H`
built from `u` and `u'`. Their root data are both `fieldRealization k P`. The Library theorem
`pinnedIsomorphism` (`PinnedIsomorphismStatement`), applied to the identity equivalence
`RootPairing.Equiv.id`, gives a pinned isomorphism `f : SplitPinning.Iso p q` whose torus part
induces the identity on characters and whose index map is the identity.

1. Torus. `IsSplitTorus.iso_ext_of_character_congr` shows that the torus isomorphism of `f` is
   the identity. So the square of `f` reads `i ≫ Φ.hom = i'`, where `Φ` is the group part of `f`.
2. Simple roots. `IsRootParametrization.comp_iso` (module `LocalSplitRootTransport`) shows that
   `u a ≫ Φ.hom` is a root parametrization of `i'`. Its derivative at `ε` is `Lie(Φ)(Lie(u a)(ε))`,
   by `Lie.targetMapLinear_comp`. This is `Lie(Φ)` of the pinned vector of `p`, which is the
   pinned vector of `q` (field `rootVector_eq` of `f`), that is `Lie(u' a)(ε)`. So both
   `u a ≫ Φ.hom` and `u' a` are normalized root parametrizations of `q` at `a`. The Library's
   `NormalizedRootParametrization.hom_eq` gives `u a ≫ Φ.hom = u' a`.
3. The points `v_a(-1)`. Let `x = u'_a(1)`. It lies in the root subgroup of `a` for `i'`, and it
   is not `1` because `c ↦ u'_a(c)` is injective and `u'_a(0) = 1`. Consider the two pairs
   `(v'_a(-1), v'_a(-1))` and `(Φ(v_a(-1)), Φ(v_a(-1)))`. Both are opposite factor pairs of `x`
   in the sense of the Library (`RelativeRoot.IsOppositeFactorPair`): their entries lie in the
   root subgroup of `-a`, and `p₁ x p₂` normalizes `i'`. For the second pair,
   `Φ(v_a(-1)) x Φ(v_a(-1)) = Φ(weylPoint (u a) (v a))`, by step 2. This point normalizes
   `i'` because `weylPoint (u a) (v a)` normalizes `i` (Library `normalizerPointsMap`). The Library
   theorem `IsOppositeFactorPair.eq` says that a nonidentity root point has at most one
   opposite factor pair. Hence `Φ(v_a(-1)) = v'_a(-1)`.

## Provenance

These are internal lemmas for the proof of the Isomorphism Theorem over a reduced local ring
(`LocalSplitReducedIsomorphismTheoremStatement`), written for this project. The main theorem is a
reformulation of the Isomorphism Theorem for pinned split reductive groups over a field
(Conrad, *Reductive group schemes*, Theorem 6.1.17, PDF p.197, stated there over any non-empty
scheme and used here for `S = Spec k`; in the Library, `PinnedIsomorphismStatement`, proved as
`pinnedIsomorphism`). It is stated in terms of root
parametrizations of the simple roots instead of Lie pinnings, so that it can be applied to field
fibres of groups over a ring. It adds the comparison of the points `v_a(-1)`, which follows from
the uniqueness of opposite factor pairs. The proof combines the Library results named above and
follows no particular printed source.
