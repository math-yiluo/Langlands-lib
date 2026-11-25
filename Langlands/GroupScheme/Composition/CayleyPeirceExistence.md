# Existence of a Peirce frame for an isotropic idempotent

This module proves, for a Cayley datum `c` over an arbitrary field `K`
(no characteristic assumption, so characteristic two is included), that an
isotropic vector `e` of trace one has a dual pair of triples in its two
Peirce spaces. It imports only the composition identities of
`Langlands.GroupScheme.Composition.CayleyIdentities` (`form` is the polar
form `b` of the norm `N`, `trace x` is `T(x) = b(x, 1)`) and Mathlib's
finite-dimensional linear algebra.

## Main result

`exists_peirceFrame` (namespace `Langlands.GroupScheme.CayleyDatum`): if
`N(e) = 0` and `T(e) = 1`, there are `u v : Fin 3 → CayleyVector K` with

- `e (u a) = u a`, `T(u a) = 0` and `b(u a, e) = 0` for every `a`;
- `e (v a) = 0`, `T(v a) = 0` and `b(v a, e) = 0` for every `a`;
- `b(u a, v b) = 1` if `a = b` and `0` otherwise.

Here `e y` is the multiplication `c.multiplication e y`. The statement is
the one consumed by `IsotropicCayleyAutomorphismRankProof` to build a
weighted self-dual frame `e, 1 - e, u, v` of the Cayley algebra (the
`PeirceFrame` of `CayleyPeirceFrame`).

## Auxiliary declarations

All auxiliary declarations live in the namespace
`Langlands.GroupScheme.CayleyDatum.PeirceExistence`, so they cannot clash
with other modules about the same algebra. Throughout, `e` satisfies
`N(e) = 0` and `T(e) = 1` (each lemma lists the hypotheses it uses).

- `peirceU c e` and `peirceV c e` are the submodules
  `U = {y | T(y) = 0, b(y, e) = 0, e y = y}` and
  `V = {y | T(y) = 0, b(y, e) = 0, e y = 0}`, defined as intersections of
  kernels of linear maps; `mem_peirceU` and `mem_peirceV` unfold membership.
- `form_e_e`: `b(e, e) = 0`; `e_mul_e`: `e e = e` (from
  `x² = T(x) x - N(x) 1`); `e_mul_e_mul`: `e (e y) = e y` (left
  alternativity).
- `trace_e_mul`: if `T(y) = 0` and `b(y, e) = 0` then `T(e y) = 0` (from
  `b(xy, z) + b(y, xz) = T(x) b(y, z)` with `z = 1`); `form_e_mul_e`:
  `b(e y, e) = 0` (from `b(xy, xz) = N(x) b(y, z)` with `z = 1`).
- `mul_e_eq`: if `T(y) = 0` and `b(y, e) = 0` then `y e = y - e y` (from the
  linearization `xy + yx = T(x) y + T(y) x - b(x, y) 1`); hence
  `mul_e_of_mem_V`: `y e = y` on `V`.
- `norm_of_mem_U`, `norm_of_mem_V`: `N` vanishes on `U` and on `V`
  (`y = e y` or `y = y e` and `N` is multiplicative); `form_of_mem_U`,
  `form_of_mem_V`: `U` and `V` are totally isotropic for `b`.
- `decomp`: every `y` equals `a 1 + b e + p + q` with `p ∈ U`, `q ∈ V`.
  Explicitly `w = y - b(y, e) 1 - (T(y) - 2 b(y, e)) e` has `T(w) = 0`,
  `b(w, e) = 0`, and `p = e w`, `q = w - e w`. Hence `sup_eq_top`:
  `span {1, e} + U + V` is the whole space, and `eight_le_finrank`:
  `8 ≤ 2 + dim U + dim V`.
- `eq_zero_of_orthogonal`: a vector orthogonal to `1`, `e`, `U` and `V` is
  zero (nondegeneracy of `b` plus `decomp`).
- `pairVU : V → U*` and `pairUV : U → V*` are the pairings induced by `b`;
  `pairVU_apply`, `pairUV_apply` evaluate them. Both are injective
  (`pairVU_injective`, `pairUV_injective`): a vector of `V` killing `U` is
  orthogonal to `1`, `e`, `U` and (by isotropy) `V`, hence zero; similarly
  for `U`. Therefore `finrank_V_eq_U` (`dim V = dim U`),
  `three_le_finrank_U` (`3 ≤ dim U`, from `8 ≤ 2 + 2 dim U`), and
  `pairVU_surjective`.

## Proof of the main result

Take a basis of `U` (Mathlib's `Module.finBasis`), let `u a` be its first
three vectors (indices `Fin.castLE` of `3 ≤ dim U`), and let `v b ∈ V` be a
preimage under the surjection `pairVU` of the coordinate functional of
`u b`. Then `b(u a, v b)` is the `u b`-coordinate of `u a`, which is
`δ_{ab}`. The Peirce conditions on `u a` and `v b` are membership in `U`
and `V`.

This avoids computing `dim U = dim V = 3` exactly: only the lower bound
`3 ≤ dim U` is needed.

## Provenance

The decomposition of a split composition algebra along an isotropic
idempotent `e` (spanned by `e`, `1 - e` and two totally isotropic subspaces
in duality) is a standard tool in the theory of split Cayley algebras; the
algebra-level source for this project is Knus, Merkurjev, Rost and Tignol,
*The Book of Involutions*, Section 33.C (Theorem 33.17 and the discussion of
split Cayley algebras on printed pp.459–462 / PDF pp.482–485), as cited in
the target statement's Markdown. This module is internal, derived content:
the Lean route is the self-contained dimension count described above,
chosen for this development, and it uses only the composition identities
of `CayleyIdentities`. It does not compute `dim U = 3` exactly and does not
use any classification of composition algebras.
