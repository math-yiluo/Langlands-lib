# Short roots, strings of length at most one, and a positive functional (`ShortRoots`)

Author: Worker 239.

This module collects three ingredients of the short-root representation built in
`ShortRootModule` and `ShortRootRep`.

## Strings of length at most one

Fix `α : X` and `pair : X →+ ℤ` with `pair α = 2`.

- `StringData.ofUnit`: let `ω : C → X` be an injective family with `|pair (ω d)| ≤ 1` for all
  `d`, stable under the reflection `μ ↦ μ − pair μ • α`. Then it has root-string data (see
  `StringRep`) with `bot d = 1` if `pair (ω d) = 1` and `0` otherwise (`ofUnit_bot`), and
  `top d = 1` if `pair (ω d) = −1` and `0` otherwise (`ofUnit_top`). Its strings have length at
  most one.
- `StringData.ofUnit_decomp_E_one`, `StringData.ofUnit_decomp_F_one`: for the resulting string
  decomposition, the raising operator sends `ω c` to `ω c + α` with coefficient `1`, and the
  lowering operator sends `ω c` to `ω c − α` with coefficient `1`. The proofs specialize
  `decomp_E_one` and `decomp_F_one` and compute `bot` and `top` by case analysis.
- `StringDecomp.trivial`: if `pair (ω d) = 0` for all `d`, then the family has the decomposition
  into strings of length zero. By `trivial_E_one` and `trivial_F_one`, its operators `E 1` and
  `F 1` vanish.

## Short roots

Let `P : RootDatum J X Y`.

- `IsShortRoot P j`: `|⟨α_j, α_k^∨⟩| ≤ 1` for every root `α_k ≠ ±α_j`.
- `root_reflectionPerm_self`: `α_{s_i i} = −α_i`.
- `pairing_reflectionPerm_left`: `⟨s_i α_j, α_k^∨⟩ = ⟨α_j, α_k^∨⟩ − ⟨α_j, α_i^∨⟩⟨α_i, α_k^∨⟩`.
- `IsShortRoot.reflectionPerm`: short roots are permuted by the reflections.
  `⟨s_i α_j, α_k^∨⟩ = ⟨α_j, (s_i α_k)^∨⟩`, and `s_i α_k ≠ ±α_j` exactly when `α_k ≠ ±s_i α_j`.
- `IsShortRoot.abs_pairing_le_one`, `IsShortRoot.of_root_eq`: the defining bound in the form
  `⟨α_j, α_k^∨⟩ ∈ {−1, 0, 1}`, and `±` a short root is short.
- `pairingIn_int`, `pairing_pairing_mem`: for a reduced root datum with finite `J` and roots
  `α_i ≠ ±α_j`, the pair `(⟨α_i, α_j^∨⟩, ⟨α_j, α_i^∨⟩)` lies in the usual list of eleven
  possibilities. This is Mathlib's `pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed'`.
- `root_ne_two_smul`, `root_ne_neg_two_smul`: in a reduced root datum, `±2α_i` is not a root.
- `exists_isShortRoot_pairing_eq_neg_one` (finite `J`, reduced `P`): for every root `α_x` that
  is not short, there is a short root `β` with `⟨β, α_x^∨⟩ = −1`.

  Proof: strong induction on the norm `B(α_x, α_x)`, where `B = P.RootForm`. Since `α_x` is
  not short, some `α_k ≠ ±α_x` has `|⟨α_x, α_k^∨⟩| ≥ 2`. The table of pairings and the relation
  `2 B(μ, α_k) = ⟨μ, α_k^∨⟩ B(α_k, α_k)` show that `⟨α_k, α_x^∨⟩ = ±1` and
  `B(α_k, α_k) < B(α_x, α_x)`. Replacing `α_k` by `−α_k` if needed gives a root `γ` with
  `⟨γ, α_x^∨⟩ = −1` and smaller norm. If `γ` is short, take `β = γ`. Otherwise induction gives
  a short `β'` with `⟨β', γ^∨⟩ = −1`. Since `α_x` is not short, `α_x ≠ ±β'`, so
  `⟨β', α_x^∨⟩ ∈ {−1, 0, 1}`. In these three cases take `β = β'`, `β = s_γ β'` (whose pairing is
  `0 − (−1)(−1) = −1`), or `β = −β'`.

## A functional positive on the simple roots

- `posCorootSum b : X →+ ℤ` (finite `J`, base `b`) is `x ↦ Σ_{α_j > 0} ⟨x, α_j^∨⟩`, the sum
  of the pairings with the coroots of the positive roots (that is, `⟨x, 2ρ^∨⟩`).
- `posCorootSum_root`: `⟨α_i, 2ρ^∨⟩ = 2` for every simple root `α_i`. The term `j = i`
  contributes `2`. The other positive roots are permuted by `s_i`, and
  `⟨α_i, (s_i α_j)^∨⟩ = −⟨α_i, α_j^∨⟩`, so their terms cancel in pairs
  (`Finset.sum_involution`).
- `posCorootSum_pos`: hence `posCorootSum b` is positive on the simple roots.

## Provenance

The notion of short root used here (all pairings with non-proportional coroots in
`{−1, 0, 1}`) is internal to this project. For an irreducible root system with two root
lengths it gives the roots of the shorter length, and for a simply-laced system all roots.
That classification fact is neither stated nor used. `⟨α_i, 2ρ^∨⟩ = 2` is the dual form of
`⟨2ρ, α_i^∨⟩ = 2` (Humphreys, *Introduction to Lie Algebras and Representation Theory*,
§10.2, Lemma B and Corollary). The table of pairings of two roots is the standard one
(Humphreys, §9.4), taken from Mathlib.
