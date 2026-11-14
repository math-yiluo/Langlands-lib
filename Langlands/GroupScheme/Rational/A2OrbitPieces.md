# Piece families of `A₂` orbits of simple roots

Author: Worker 4348.

Module `Langlands.GroupScheme.Rational.A2OrbitPieces`, namespace
`Langlands.GroupScheme.GaloisCompatiblePinningData`.

The setting is that of module `Rational.CompatiblePinningRestriction`:
- `D : GaloisCompatiblePinningData k K G` with pinning `p = D.pinning`;
- `t : S ⟶ D.torus`, with `restrictMap t : S_K ⟶ p.torus`;
- `Γ = Aut_k(K)`, and `a_K = characterLattice.baseChange (algebraBaseMap k K) S a`.

Let `p₀ ≠ q₀` be simple roots restricting to the same `a_K`, and let `m₀` be a root index with
`root m₀ = root p₀ + root q₀`. The module turns the Galois orbit of `m₀` into a piece family
over `a_K`, in the sense of the published `PieceFamily` (module
`Geometry.Building.QuasiSplitMultipliableOpposite`). It also attaches exactly
Galois-equivariant merged-root maps to the pieces. This is the combinatorial setup for the
`A₂`-orbit case of `Z(k) ⊆ G(k)^+` for quasi-split simply connected groups.

## The Galois action on root indices

- `rootIndexAction : Γ →* Equiv.Perm p.rootIndex` is the published
  `IsRootDatumOf.galoisRootIndexAction` for the transported root datum.
  `transportedRoot_rootIndexAction` gives
  `transported root (σ r) = galoisRepresentation σ (transported root r)`.
- `rootIndexAction_simple σ a`: on simple roots it is `D.action`.
- `root_rootIndexAction_add σ h`: if `root m = root x + root y`, then the same holds for the
  images under `σ`. Transport through `characterLattice.congr D.torusIso` and use additivity of
  the Galois representation.
- `rootIndexMulAction` makes this a `MulAction`; `smul_rootIndex` unfolds it.

## The orbit of pairs

- `PairOrbit m₀` is `MulAction.orbit Γ m₀`, a finite type.
- `pairElement c` is a chosen `σ` with `σ • m₀ = c` (`pairElement_smul`).
- `pairA p₀ c = D.action (pairElement c) p₀` and `pairB q₀ c = D.action (pairElement c) q₀`.
- `root_pair hm₀ c`: `root c = root (pairA c) + root (pairB c)`.

Assume moreover:
- `S` is split (`hS`);
- `p₀` and `q₀` both restrict to `a_K` (`hp₀`, `hq₀`), and `p₀ ≠ q₀`;
- `hline : RestrictsToMultipliableLine (restrictMap t) p.rootDatum a_K`.

Then:

- `restrict_pairA`, `restrict_pairB`: `pairA c` and `pairB c` restrict to `a_K`
  (`restrictMap_comp_root_action`).
- `pairA_ne_pairB c`: they are different root indices (`D.action σ` is injective).
- `isMultipliablePiece_pair c`: `(pairA c, pairB c, c)` is an `IsMultipliablePiece` over `a_K`.
- `pair_orient σ c`: `pairA (σ • c)` and `pairB (σ • c)` are `D.action σ (pairA c)` and
  `D.action σ (pairB c)`, in one of the two orders. Both pairs decompose `root (σ • c)` into
  two roots over `a_K`. Conclude by the published `piece_decomposition_unique`.
- `pair_eq_of_mem hx hx'`: two pieces sharing a root index are equal. The shared root has a
  unique partner (published `partner_unique`, with `piece_pairing_pq`). So the two pieces have
  the same roots, and `root c = root c'`.
- `pair_pairings c`: `pairA c ≠ pairB c`, and both mutual pairings are `-1`
  (`piece_pairing_pq`, `piece_pairing_qp`).
- `exists_mergedPieces` (with `[FiniteDimensional k K]`): apply the published
  `exists_mergedRootGaloisData` to `J = PairOrbit m₀`, `a = pairA p₀`, `b = pairB q₀`. This
  gives `M : PairOrbit m₀ → p.SteinbergModifiedData` with:
  1. `(M c).a = pairA c`, `(M c).b = pairB c`, `(M c).ca = (M c).cb = 1`;
  2. the reflection representative of `M c` lies in the rational points of
     `U(α_c) ⊔ U(-α_c)`;
  3. `σ((M c).xAlpha(s)) = (M (σ • c)).xAlpha(σ s)` (`rationalConjugate`);
  4. the representatives and the coroot points are transported accordingly.

## The piece family

Fix any `M` whose data satisfy `(M c).a = pairA c` and `(M c).b = pairB c` (`hM`).

- `mergedAlpha_eq hm₀ M hM c`: `(M c).alpha = c`, by injectivity of roots.
- `pieceEquiv m₀ : Fin (Nat.card (PairOrbit m₀)) ≃ PairOrbit m₀` is an enumeration of the
  pieces (`Finite.equivFin`).
- `basePair m₀` is the point `m₀` of its orbit.
- `a2PieceFamily …` is the `PieceFamily (restrictMap t) p.rootDatum a_K` with `r` the number
  of pieces. Its `l`-th piece is `(pairA c, pairB c, (M c).alpha)` for `c = pieceEquiv l`.
  The fields are proved as follows.
  - `piece`: `isMultipliablePiece_pair` and `mergedAlpha_eq`.
  - `disjoint`: `pair_eq_of_mem`.
  - `lm_injective`: `mergedAlpha_eq`.
  - `cover_a`: this takes the further hypotheses that `K/k` is finite Galois, that
    `(D.torus)_K` is split, that `groupHom t ≫ D.inclusion` is a maximal split torus, that
    `D.inclusion` is a closed subgroup representing its centralizer, and the needed
    finite-type instances. A root over `a_K` is `D.action σ p₀`
    (`exists_action_eq_of_restrict_eq`). It belongs to the piece `σ • basePair m₀`, because
    `D.action σ p₀` and `D.action σ q₀` decompose that piece's root
    (`piece_decomposition_unique`).
  - `cover_two`: a root over `2 • a_K` has the restriction of `m₀`, since
    `root m₀ = root p₀ + root q₀`. So it is a Galois transform of `m₀`
    (`exists_galois_of_restrict_eq`), and hence the merged root of the piece
    `σ • basePair m₀`.

## Provenance

This is internal combinatorics built from published Library results: Galois index
permutations of root data, restriction fibres, multipliable pieces, and the
merged-root Galois data `exists_mergedRootGaloisData`. It makes no new mathematical
assertion. In the classical picture, for a quasi-split group each Galois orbit of type
`A₂ × … × A₂` (pairs swapped by Galois) gives the roots over a multipliable relative root `a`
and over `2a`.
