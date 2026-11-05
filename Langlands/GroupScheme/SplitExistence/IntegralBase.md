# Bases of reduced root data over ℤ

This module proves that every reduced root datum `P : RootDatum J X Y` with a finite
index type `J` has a base (`P.Base`). It works directly over `ℤ`. The roots need not
span `X`, and no finiteness hypothesis on `X` or `Y` is used.

Mathlib's `RootPairing.nonempty_base` only covers crystallographic reduced root systems
over a field of characteristic zero. It also assumes that the roots span the module. A
root datum in the split classification has a radical, and its lattices are ℤ-modules,
so the field result does not apply directly. The proof here follows Mathlib's
`BaseExists` file (Mathlib commit `5ed29652`). It replaces each step that uses a field
with an integral argument.

## Main results

- `nonempty_base_int (P : RootDatum J X Y) [Finite J] [P.IsReduced] : Nonempty P.Base`.
- `baseOf_root_eq_baseOf_coroot`: let `f : X →ₗ[ℤ] ℤ` and `g : Y →ₗ[ℤ] ℤ` be nonzero on
  every root and every coroot respectively, and suppose `f(α_i) > 0` exactly when
  `g(α_i^∨) > 0`. Then the indecomposable positive roots for `f` and the
  indecomposable positive coroots for `g` have the same index set. This is the integral
  version of Mathlib's `RootPairing.baseOf_root_eq_baseOf_coroot`.

## Auxiliary lemmas

The canonical symmetric form `B = P.RootForm` (Mathlib: `B(x, y) = Σ_i ⟨x, α_i^∨⟩⟨y, α_i^∨⟩`)
satisfies the following.

- `rootForm_comm`, `rootForm_self_nonneg`: `B` is symmetric and `B(x, x) ≥ 0`.
- `four_le_rootForm_root`: `B(α_j, α_j) ≥ 4`. The summand for `i = j` is
  `⟨α_j, α_j^∨⟩² = 4`.
- `two_mul_rootForm_root`: `2 B(x, α_j) = ⟨x, α_j^∨⟩ B(α_j, α_j)`. This follows from
  Mathlib's `rootForm_self_smul_coroot`, `B(α, α) • α^∨ = 2 • Pol(α)`.
- `eq_zero_of_mem_rootSpan`: an element `z` of the ℤ-span of the roots with
  `B(z, z) = 0` is zero. Each term `⟨z, α_i^∨⟩²` vanishes, and a nonzero element of the
  root span pairs nontrivially with some coroot (Mathlib's `exists_coroot_ne`).
- `exists_dual_forall_ne_zero`: finitely many vectors, each detected by some integral
  functional, are all detected by one integral functional. The proof is induction on
  the finite set. Given `φ` for the old vectors and `ψ` for the new one, `φ + nψ` works
  for all but finitely many `n ∈ ℤ`.
- `exists_dual_coroot_ne_zero`: some `g : Y →ₗ[ℤ] ℤ` is nonzero on every coroot. Each
  coroot is detected by pairing with its root, since `⟨α_i, α_i^∨⟩ = 2`.
- `two_mul_dual_polarization_root`, `dual_polarization_root_pos_iff`,
  `dual_polarization_root_ne_zero`: for `f = g ∘ P.Polarization` one has
  `2 f(α_i) = B(α_i, α_i) g(α_i^∨)`. So `f` is nonzero on each root, and its sign
  agrees with the sign of `g` on the coroot.
- `baseOf_root_subset_baseOf_coroot`: the inclusion behind
  `baseOf_root_eq_baseOf_coroot`.

## Proof of `baseOf_root_subset_baseOf_coroot`

Let `i` be `f`-indecomposable and suppose `α_i^∨ = α_j^∨ + α_k^∨` with both coroots
`g`-positive. Write `l_m = B(α_m, α_m)`. Mathlib's argument divides by `l_m`. Here we
multiply instead, and the relation becomes

`l_j l_k α_i = l_i l_k α_j + l_i l_j α_k`.

To prove it, set `z = l_j l_k α_i − l_i l_k α_j − l_i l_j α_k`. Expand `B(z, z)` and use
`two_mul_rootForm_root` together with the coroot relation. This gives `2 B(z, z) = 0`,
and then `eq_zero_of_mem_rootSpan` gives `z = 0`.

The roots `α_j` and `α_k` are `f`-positive. So they are nonnegative integral
combinations of the `f`-indecomposable roots (Mathlib's
`closure_image_isAddIndecomposable_baseOf` and `mem_closure_image_pos_iff`). The
indecomposable roots are ℤ-linearly independent (Mathlib's `linearIndepOn_root_baseOf'`,
which holds over `ℤ`). Comparing coefficients in the relation therefore forces `α_j` to
be a positive integer multiple of `α_i`. This contradicts reducedness: `α_j ≠ α_i`,
since otherwise `α_k^∨ = 0`, and `α_j ≠ −α_i`, since both are `f`-positive.

The reverse inclusion is the same lemma applied to the flipped datum `P.flip`, with `f`
and `g` exchanged. The flipped datum is reduced because ℤ-modules in a perfect pairing
are reflexive (`IsReflexive.of_isPerfPair`), hence torsion-free.

## Proof of `nonempty_base_int`

Choose `g` with `g(α_i^∨) ≠ 0` for all `i`, and put `f = g ∘ P.Polarization`. The base
is indexed by the `f`-indecomposable positive roots, `baseOf P.root f`. The base axioms
are verified as follows.

- Linear independence of the simple roots is `linearIndepOn_root_baseOf'`.
- Every root is a positive or negative ℕ-combination of the simple roots by
  `mem_or_neg_mem_closure_baseOf`.
- The same two facts for coroots come from the flipped datum with the functional `g`.
  They transfer via `baseOf_root_eq_baseOf_coroot`.

## Provenance

The statements are the integral analogues of Mathlib's `RootPairing.nonempty_base` and
`RootPairing.baseOf_root_eq_baseOf_coroot`. The classical source for the existence of
bases is Bourbaki, *Lie groups and Lie algebras*, Chapter VI, §1. The integral
adaptation is internal to this project. It consists of the choice
`f = g ∘ Polarization` with `g` integral, the multiplied-out relation, and the
norm-zero argument in place of division.
