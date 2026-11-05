# Vanishing Verschiebung for reduced bialgebras killed by `p`

Author: Worker 1519, as internal infrastructure for the proof of
`Langlands.GroupScheme.RelativeRoot.SmoothCommutativePTorsionVectorStatement`
(task `c8e71bce-b184-446c-af50-7ac4df6401a3`).

Provenance: internal. This is the algebraic fact "`[p] = 0` and reducedness force the
Verschiebung to vanish", phrased on the full linear dual. The argument below is the
author's own implementation; no source statement is translated.

Throughout, `k` is a field, `A` a commutative `k`-bialgebra, and the *convolution dual* is
Mathlib's convolution ring `WithConv (A →ₗ[k] k)`: `(ξ * η) a = ∑ ξ(a₁) η(a₂)` and the unit
is the counit. When `A` is cocommutative (`Coalgebra.IsCocomm k A`) this ring is
commutative.

## Duality and finiteness

- `exists_eq_apply_of_finset S L hL`: for a vector space `V` over a field, a finite set
  `S ⊆ V`, and a linear functional `L` on `Module.Dual k V` vanishing on every functional
  that vanishes on `S`, there is `w : V` with `L ξ = ξ w` for all `ξ`. The proof restricts
  functionals to the finite-dimensional span `W` of `S`, chooses a linear right inverse of
  the (surjective) restriction map, and uses the canonical isomorphism of `W` with its double
  dual (`Module.evalEquiv`).
- `exists_finset_convPow m a`: for every `m` and `a` there is a finite set `S ⊆ A` such that
  `(ξ ^ m) a` depends only on the values of `ξ` on `S`. Induction on `m`, writing
  `ξ ^ (m+1) = ξ ^ m * ξ` and using a finite representation of `comul a`
  (`Coalgebra.Repr`).

## The `p`-th power map

Assume `p` is prime and `CharP k p`.

- `convOne_apply_one`: the unit of the convolution dual takes the value `1` at `1`.
  The instance `Nontrivial (WithConv (A →ₗ[k] k))` follows, and `charP_dual` gives
  `CharP (WithConv (A →ₗ[k] k)) p` through the injective algebra map from `k`.
- `convPow_char_add` (cocommutative case): `((ξ + η) ^ p) a = (ξ ^ p) a + (η ^ p) a`, by
  the Frobenius identity in the commutative ring of characteristic `p`.
- `convPow_char_smul`: `((c • ξ) ^ p) a = c ^ p * (ξ ^ p) a`.
- `rootPowFunctional p a` (for `PerfectRing k p`): the map
  `ξ ↦ (ξ ^ p)(a) ^ (1/p)`, i.e. `(frobeniusEquiv k p).symm` applied to `(ξ ^ p) a`, as a
  `k`-linear functional on `Module.Dual k A`. Additivity and linearity come from the two
  previous lemmas.
- `frobeniusEquiv_symm_eq_iff`: `(frobeniusEquiv k p).symm x = y ↔ x = y ^ p`.

## Main results

Assume moreover `IsAlgClosed k`, `Algebra.FiniteType k A` and `IsReduced A`, and the
hypothesis

`hA : ∀ φ : A →ₐ[k] k, toConv φ.toLinearMap ^ p = 1`,

i.e. every `k`-point, viewed as an element of the convolution dual, has `p`-th convolution
power equal to the counit.

- `convPow_char_apply p hA ξ a`: `(ξ ^ p) a = counit a * ξ 1 ^ p` for every functional `ξ`
  and every `a`.

  Proof as implemented. By `exists_finset_convPow` the functional `rootPowFunctional p a`
  vanishes on all functionals vanishing on a finite set, so by
  `exists_eq_apply_of_finset` it is evaluation at some `w : A`; hence
  `(ξ ^ p) a = ξ(w) ^ p` for every `ξ`. For a `k`-algebra map `φ`, `hA` gives
  `(φ ^ p) a = counit a`, so `φ w = c` with `c ^ p = counit a`. Thus `w - c • 1` vanishes at
  every `k`-point; the Library Nullstellensatz
  `GroupScheme.KostantRosenlicht.eq_zero_of_forall_algHom` (reduced finitely generated
  algebra over an algebraically closed field) gives `w = c • 1`, and therefore
  `(ξ ^ p) a = (c * ξ 1) ^ p = counit a * ξ 1 ^ p`.
- `convPow_char_eq_zero p hA hξ`: if `ξ 1 = 0`, then `ξ ^ p = 0`.

These are exactly the vanishing of the Verschiebung on the convolution dual. The module does
not assume a Hopf (antipode) structure.
