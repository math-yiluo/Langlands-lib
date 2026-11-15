# Commutators of two root groups for non-opposite roots

This module gives the commutator of two root groups, for any pair of roots that are not
opposite. Neither root has to be simple, and no base is fixed in advance. The base ring
is an arbitrary commutative ring, which may have nilpotents. The module imports the
universal commutator polynomials of
`Langlands.GroupScheme.Reductive.LocalSplitCommutatorPolynomials`. It also imports
the integral base constructions of `Langlands.GroupScheme.SplitExistence.IntegralBase`.

## Root-datum part (namespace `Langlands.LinearAlgebra`)

`P : RootDatum J X Y` is a root datum with finite index type `J`.

- `isPos_iff_of_pos_simple`: if an integral functional `f` on `X` is positive on the
  simple roots of a base `b`, then `b.IsPos i ↔ 0 < f (P.root i)`.
- `exists_base_isPos_iff`: let `P` be reduced and let `g` be an integral functional on
  `Y` that is nonzero on every coroot. Then some base `b` has `b.IsPos i` exactly when
  `0 < g (P.coroot i)`.
- `exists_regular_of_pos`: every integral functional `g` on `Y` has a perturbation
  `q = n • g + q₀` that is nonzero on every coroot. Here `q₀` is any functional nonzero
  on every coroot, and `n` is larger than all `|q₀ (coroot i)|`. The perturbation is
  positive on every coroot where `g` is positive.
- `exists_base_isPos_of_pos`: for `P` reduced and any `g`, some base makes positive
  every root whose coroot has positive value under `g`.
- `exists_base_isPos_pair`: for `P` reduced with `X` torsion-free, and roots `i`, `j`
  with `P.root i ≠ -P.root j`, some base makes both `i` and `j` positive.

## Group part (namespace `Langlands.GroupScheme.LocalSplitCell`)

`orderedProduct u pos Z c` is the imported ordered product `∏_q u_{pos q}(c q)`.
`rootPoint` is the imported point of a root group, and `posComm` the imported
commutator `(u_k(x) u_l(y))⁻¹ (u_l(y) u_k(x))` of two positive cell factors.

- `orderedProduct_eq_rootPoint_of_eq_zero`: if all coordinates vanish except the one at
  position `k`, the ordered product is the factor `u_{pos k}(c k)`.
- `orderedProduct_eq_rootPoint_mul_of_eq_zero`: if all coordinates vanish except those
  at two positions `k₁ < k₂`, the ordered product is
  `u_{pos k₁}(c k₁) · u_{pos k₂}(c k₂)`.
- `exists_cell_of_base`: the setting is a reductive `G` over `Spec R` with affine
  structure morphism, a fibrewise maximal coordinate split torus `i`, a fibrewise root
  datum `P`, and root parametrizations `v α` of `i` for every root `α`. Then for every
  base `b` there are enumerations `neg`, `pos` of the non-positive and positive roots
  such that `cellMap i v neg pos` is an open immersion. There is also a cocharacter `ν`
  pairing negatively with the roots at `neg` and positively with those at `pos`.
- `rootPoint_commute_of_forall_ne`: in this setting, let `β`, `ε` be roots with
  `P.root β ≠ -P.root ε`, such that no `dS • β + dT • ε` with `dS, dT ≥ 1` is a root.
  Then `v_β(x) v_ε(y) = v_ε(y) v_β(x)` over every ring over `R` (every
  `s : Spec B → Spec R`).
- `exists_rootPoint_comm_single`: in this setting, let `β`, `ε` be roots with
  `P.root β ≠ -P.root ε`, and `δ` a root with `P.root δ = P.root β + P.root ε`. Suppose
  that `dS • β + dT • ε` with `dS, dT ≥ 1` is a root only when `dS = dT = 1`. Then there
  is `C ∈ R` such that for every `s : Spec B → Spec R` and all `x, y ∈ B`,
  `(v_β(x) v_ε(y))⁻¹ (v_ε(y) v_β(x)) = v_δ(s(C) x y)`. Here elements of `B` are
  global functions via the inverse of `Scheme.ΓSpecIso`, and `s(C)` is the image of `C`
  under the ring map `(Spec.preimage s).hom` of `s`.

- `exists_rootPoint_comm_two`: in the same setting, let `β`, `ε` be roots with
  `P.root β ≠ -P.root ε`, and `δ₁`, `δ₂` roots with `P.root δ₁ = P.root β + P.root ε` and
  `P.root δ₂ = 2 • P.root β + P.root ε`, whose root groups commute over every ring over
  `R`. Suppose that `dS • β + dT • ε` with `dS, dT ≥ 1` is a root only for
  `(dS, dT) = (1, 1)` or `(2, 1)`. Then there are `C₁, C₂ ∈ R` with
  `(v_β(x) v_ε(y))⁻¹ (v_ε(y) v_β(x)) = v_{δ₁}(s(C₁) x y) · v_{δ₂}(s(C₂) x² y)`.
- `coord_zero_of_eq_mul`: let `δ₀`, `δ₁`, `δ₂` be distinct positive roots of a base,
  where the root groups of `δ₁` and `δ₂` commute over a given ring over `R`. If
  `v_{δ₀}(r₀) = v_{δ₁}(r₁) v_{δ₂}(r₂)` there, then `r₀ = r₁ = r₂ = 0`.

## Statement

`LocalSplitRootPairCommutatorStatement.{u}` quantifies over a commutative ring `R`, a
finite type `I`, a type `J` (all in universe `u`), a group scheme `G` over `Spec R`
with affine structure morphism that is reductive, a coordinate split torus
`i : T_I → G` that is maximal on every residue-field fibre, a fibrewise root datum
`P : RootDatum J (I → ℤ) (I → ℤ)`, a family `v` of root parametrizations of `i` for all
roots, and roots `β`, `ε` with `P.root β ≠ -P.root ε`. Its conclusion is the
conjunction of two parts:

1. the commutation of `rootPoint_commute_of_forall_ne`, under its hypothesis on the
   multiples `dS • β + dT • ε`;
2. for every root `δ` with `P.root δ = P.root β + P.root ε`, the existence of `C`
   from `exists_rootPoint_comm_single`, under its hypothesis on the multiples.

The module proves it at full universe as `localSplitRootPairCommutator`.

## Proof

**Bases.** `isPos_iff_of_pos_simple` is an induction over positive roots (Mathlib's
`IsPos.induction_on_add`). A negative root is minus a positive one
(`IsPos.or_neg`, `indexNeg`). For `exists_base_isPos_iff`, put `f = g ∘ Pol` with the
polarization of `P`. The imported `dual_polarization_root_ne_zero` and
`dual_polarization_root_pos_iff` show that `f` is nonzero on every root, with the same
signs as `g` on the coroots. The base has support `baseOf P.root f`, exactly as in the
published `nonempty_base_int`. Its coroot axioms come from the imported
`baseOf_root_eq_baseOf_coroot`. The simple roots lie in `baseOf`, so `f` is positive on
them, and `isPos_iff_of_pos_simple` applies. In `exists_regular_of_pos`, `q₀` comes
from the imported `exists_dual_coroot_ne_zero`. Integrality gives `|g| ≥ 1` where `g` is
nonzero, which yields both properties. For two roots `i ≠ j`, the functional
`y ↦ (2 - ⟨j, i^∨⟩) ⟨i, y⟩ + (2 - ⟨i, j^∨⟩) ⟨j, y⟩` takes the value
`4 - ⟨i, j^∨⟩ ⟨j, i^∨⟩` on both coroots `i^∨` and `j^∨`. This value is positive by
Mathlib's `coxeterWeightIn_le_four` and `coxeterWeightIn_ne_four`, which need the two
roots not to be opposite and `P` reduced. For `i = j`, the functional `⟨i, ·⟩` takes the
value `2` on `i^∨`.

**Cells.** `exists_cell_of_base` uses `Finite.equivFin` for the enumerations, the
imported `LocalSplitBigCell.isOpenImmersion_cellMap` for the open immersion, and the
imported `exists_coPairing_eq_height` for a cocharacter `ν` with
`⟨α, ν⟩ = d · height α`, `d > 0`.

**Commutators.** Choose a base `b` making `β` and `ε` positive, and positions `k`, `l` of
`β` and `ε` in `pos`. The root parametrizations give torus equivariance with the
characters `P.root α`. For commutation, the imported `posComm_eq_one_of_forall_ne` gives
`posComm = 1`, that is `(v_β(x) v_ε(y))⁻¹ (v_ε(y) v_β(x)) = 1`. For a single root in
the cone, `δ` is positive (Mathlib's `IsPos.add`). The imported `exists_isUnivComm` gives
universal coordinates `E`. At a position `q` other than that of `δ`, every monomial
weight `dS • β + dT • ε` would be a root, hence equal to `β + ε = δ`. Injectivity of
`P.root` and of `pos` would then give `q = q₀`, so `E q = 0` by the imported
`IsUnivComm.eq_zero_of_forall_ne`. At `δ`, the imported `IsUnivComm.one_le` and
`IsUnivComm.weight` leave only the monomial `S T`, so
`E q₀ = monomial 1 (monomial 1 C)`, where `C` is the coefficient of `S T`. The imported
specialization `IsUnivComm.posComm_eq` and `orderedProduct_eq_rootPoint_of_eq_zero` then
give `v_δ(s(C) x y)`.

For two roots in the cone, the same argument applies at the positions `q₁`, `q₂` of `δ₁`,
`δ₂`. These positions differ, because `δ₁ ≠ δ₂` by linear independence of `β`, `ε`
(Mathlib's `IsReduced.linearIndependent`; `β = ε` is impossible since `3 β` is not a
root). The weights leave only `S T` in `E q₁` and `S² T` in `E q₂`. The ordered product
with two nonzero coordinates is the product of the two factors, in the order of the
positions. When `q₂ < q₁`, the commutation hypothesis swaps them. `coord_zero_of_eq_mul`
writes both sides as ordered products in the big cell of the base, using
`orderedProduct_eq_rootPoint_of_eq_zero` and `orderedProduct_eq_rootPoint_mul_of_eq_zero`
(with the commutation if needed). It then compares coordinates by the imported
`orderedProduct_pos_injective`.

## Provenance and scope

This is internal derived content toward the Isomorphism Theorem over an arbitrary local
ring. The shape of the commutator of two root groups follows the commutation formula of
Conrad, *Reductive group schemes* (2014), Proposition 5.1.14 with formula (5.1.5). The
existence of a base making two non-opposite roots positive is a standard fact about root
systems. Compare SGA 3, Exp. XXI, 3.5.4, which constructs a base containing a given
root by a lexicographic order. The integral functional constructions here are explicit
arguments of this module. The module does not compute the constant `C`, and it does not
compare constants between two groups.
