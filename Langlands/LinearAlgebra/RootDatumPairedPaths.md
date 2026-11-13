# Paired simple roots of a pairing-compatible action and their even paths

Provenance: internal helper for the even-chain Galois data proof (Task 5375).
That target is derived from Robert Steinberg, *Regular elements of semi-simple
algebraic groups*, Publ. Math. IHÉS 25 (1965), 49–80 (source
`steinberg-1965-regular-elements-semisimple-groups`); the Markdown of the
target `EvenChainGaloisDataStatement` gives the full source account.
Steinberg's 9.4 (printed pp.72–73) excludes components of type `A_n` with `n`
even; there the roots in each Galois orbit of simple roots are orthogonal. For
a component of type `A_{2m}`, the notation before Theorem 9.11 (printed p.74)
pairs `α_i` with `α_{2m+1-i}`. These roots are orthogonal unless `i = m`; the
middle pair `α_m`, `α_{m+1}` has pairings `-1` and is merged into the root
`α_m + α_{m+1}`. Steinberg treats one component at a time (last paragraph of
printed p.77, proof of 9.7 e)). This module proves, as an internal derived
combinatorial result, that two distinct, non-orthogonal simple roots `a, a'`
in one Galois orbit have pairings `-1` and are the two middle entries of a path
component of type `A_{2m}` (`IsPaired.exists_path`). It packages these pairs,
for all components at once, as the index type, paths, action and level
function used by `SplitPinning.EvenChainData`. The mathematical input is the
published `RootDatumOrbitPairs` and `RootDatumReversedPath` theory.

Throughout, `P : RootDatum ι M N` has finite index type `ι` and a base `b`.
`Γ` is a group and `ρ : Γ →* Equiv.Perm b.support` an action on the simple roots.
Most statements assume `hρ : IsPairingCompatible b ρ`: every `ρ γ` is induced by a
pairing-preserving permutation of all roots.

## Definitions

- `IsPaired ρ a`: some `γ` moves `a` to a distinct simple root that is not
  orthogonal to `a`.
- `partner ρ a`: for a paired root, the image `ρ γ a` under the chosen witness
  `γ`. For an unpaired root it is `a` itself.
- `key a`: an auxiliary injective numbering of the simple roots, by
  `Fintype.equivFin`. It only serves to select one root of each pair.
- `PairIndex ρ`: the paired simple roots `a` with `key a < key (partner ρ a)`.
  It is finite (`instance : Finite (PairIndex ρ)`).
- `pairRep ρ a`: whichever of `a` and `partner ρ a` has the smaller key.
- `pairSMul hρ σ c` and the `MulAction` `pairAction hρ`: `σ` acts on a pair by
  moving its selected root and selecting again with `pairRep`.
- `half hρ c` and `path hρ c : Fin (2 * half hρ c) → b.support`: a chosen path
  component of even length `2 * half` containing the pair in the middle. Entry
  `half - 1` is `c.1` and entry `half` is its partner.
- `level hρ z`: the distance `middleDistance (half c) i` of `z` from the middle
  pair if `z = path c i` for some pair `c` and index `i`, and `0` if `z` is on no path.

## Statements

- `key_injective`; `middleDistance_rev`: `middleDistance m` is invariant under
  `Fin.rev` on `Fin (2 * m)`.
- `IsPaired.exists_eq_partner`, `IsPaired.partner_ne`: the partner is a
  distinct non-orthogonal image of `a` in its orbit.
- `not_isOrthogonal_of_not_isPaired`: an unpaired `z` is orthogonal to every
  distinct simple root `ρ γ z` in its orbit.
- `IsPaired.eq_partner`: every distinct non-orthogonal simple root in the
  orbit of a paired root is its partner.
- `IsPaired.pairing_partner`: `⟨a, partner a^∨⟩ = ⟨partner a, a^∨⟩ = -1`.
- `IsPaired.partner_isPaired`, `IsPaired.partner_partner`: the partner is
  paired and taking partners is an involution.
- `IsPaired.apply`, `isPaired_apply_iff`: pairedness is invariant under the
  action. `IsPaired.partner_apply`: `partner (ρ σ a) = ρ σ (partner a)`.
- `pairRep_val`, `pairRep_spec`, `pairRep_partner`, `pairRep_apply_pairRep`,
  `pairSMul_val`: bookkeeping for the selection.
- `pairSMul_orientation`: either `(σ • c).1 = ρ σ c.1` and
  `partner (σ • c).1 = ρ σ (partner c.1)`, or both equalities hold with the roles of
  `c.1` and `partner c.1` exchanged on the right.
- `IsPaired.exists_path`: a paired root `a` and its partner are entries
  `m - 1` and `m` of a path component `β : Fin (2 * m) → b.support`.
- `path_spec`, `isPathComponent_path`, `half_pos`, `path_left`, `path_right`:
  the properties of the chosen paths.
- `path_disjoint`: if `path c i = path c' i'`, then `c = c'`.
- `exists_path_smul`: `ρ σ (path c i)` equals `path (σ • c) i'` for some `i'`
  at the same distance from the middle pair.
- `middleDistance_eq_of_path_eq`, `level_path`: `level (path c i)` is
  `middleDistance (half c) i`.
- `level_apply`: `level (ρ σ z) = level z`.
- `isPaired_iff_exists`: `z` is paired iff `z = c.1` or `z = partner c.1` for
  some pair `c`.

## Implemented proof

The partner lemmas reduce to the published `RootDatumOrbitPairs` results for
pairing-compatible actions. `eq_of_not_isOrthogonal` gives uniqueness of the
distinct non-orthogonal orbit companion,
`pairing_eq_neg_one_of_not_isOrthogonal` gives the pairings `-1`, and
`apply_apply_eq_of_not_isOrthogonal` shows that the witness `δ` sends the partner
back to `a`. Hence the partner is paired, the partner of the partner is `a`, and
`partner` is an involution. Invariance under the action conjugates the witness:
`ρ (σ γ σ⁻¹) (ρ σ a) = ρ σ (ρ γ a)`, and `IsPairingCompatible.pairing_apply`
shows that `ρ σ` preserves orthogonality. Uniqueness then gives `partner_apply`.

The selection lemmas unfold `pairRep` and compare keys: `key` is injective, and
the two roots of a pair are distinct. `pairAction` satisfies the action laws
because `pairRep (ρ σ (pairRep (ρ τ a))) = pairRep (ρ (σ τ) a)`, which uses
`partner_apply` and `pairRep_partner`. `pairSMul_orientation` splits on which
root of the image pair has the smaller key.

`exists_path` uses the published `exists_isReversedPath` for the witness of
`partner a`. It gives a reversed path of length `2m` with `a` at entry `m - 1`,
which is a path component by `IsReversedPath.isPathComponent`. Entry `m` is
the reversal of entry `m - 1`, which the path's permutation `ρ δ` sends to `ρ δ a =
partner a` (`IsReversedPath.apply_eq_rev`). `half` and `path` are chosen
witnesses of this existence statement.

`path_disjoint` applies `IsPathComponent.eq_or_eq_rev` from
`RootDatumPathUniqueness`. The two paths have the same length and agree up to
reversal, so the selected root `c'.1` at the left middle entry is `c.1` or
`partner c.1`. The second case contradicts the key inequalities of `c` and
`c'`.

`exists_path_smul` compares the path `path (σ • c)` with the path component
`ρ σ ∘ path c` (`IsPathComponent.comp_perm`). By `pairSMul_orientation` they
share a middle entry, so `eq_or_eq_rev` identifies them up to reversal, and
`middleDistance_rev` keeps the distance from the middle. `level_path` follows
from `path_disjoint` and injectivity of paths. `level_apply` uses
`exists_path_smul` for `σ` on roots on a path, and for `σ⁻¹` to see that the
image of a root on no path is on no path. `isPaired_iff_exists` uses `pairRep z`
as the pair and `partner_partner`.
