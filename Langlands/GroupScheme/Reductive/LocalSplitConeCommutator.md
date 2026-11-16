# Commutators of two root groups along an ordered cone of roots

This module computes the shape of the commutator of two root groups whose cone contains
several roots. The roots of the cone must be listed in a prescribed order. It is a helper
module for the rank-two computations of type `G₂`. The base ring is an arbitrary
commutative ring. The module imports
`Langlands.GroupScheme.Reductive.LocalSplitRootPairCommutator`, and through it the
universal commutator polynomials of
`Langlands.GroupScheme.Reductive.LocalSplitCommutatorPolynomials`. It contains no
`Prop`-valued statement.

## Results (namespace `Langlands.GroupScheme.LocalSplitCell`)

`orderedProduct u pos Z c` is the imported ordered product `∏_q u_{pos q}(c q)` of root
points over `Z`, taken in the order of the positions `q`. `rootPoint` is the imported point
of a root group.

- `exists_pos_initial`: let `b` be a base of a root datum with finite index type, and let
  `L` be a list of distinct positive roots. Some enumeration
  `pos : Fin (L.length + m) ≃ {α // b.IsPos α}` of the positive roots lists `L` first, in
  order: `pos (Fin.castAdd m r) = L.get r`.
- `coPairing_combo`: the pairing `coPairing` of an exponent vector with a cocharacter is
  linear in the exponent vector.
- `orderedProduct_initial`: if the coordinates `c` vanish at all positions after the
  first `k`, the ordered product equals the product of its first `k` factors.
- `exists_cell_initial`: the setting is a reductive `G` over `Spec R` with affine structure
  morphism, a fibrewise maximal coordinate split torus `i`, a fibrewise root datum `P`, and
  root parametrizations `v α` of `i` for every root `α`. For a base `b` and a list `L` as
  above, there are enumerations `neg`, `pos` of the non-positive and positive roots such
  that `pos` lists `L` first and `cellMap i v neg pos` is an open immersion. There is also a
  cocharacter `ν` pairing negatively with the roots at `neg` and positively with those at
  `pos`.
- `listProd_rootPoint_injective`: in this setting, for a list `L` of distinct positive roots
  of a base, the product `∏_r v_{L r}(x r)`, taken in the order of `L`, determines the
  coordinates `x`. This holds over every ring over `R`, that is, over every
  `s : Spec B → Spec R`.
- `exists_rootPoint_comm_cone`: in this setting, let `β ≠ ε` be roots with
  `P.root β ≠ -P.root ε`. Let `L` be a list of distinct roots with
  `P.root (L r) = e₁ r • P.root β + e₂ r • P.root ε` and `e₁ r, e₂ r ≥ 1`, containing every
  root of the form `dS • β + dT • ε` with `dS, dT ≥ 1`. Then there are constants
  `C r ∈ R` such that for every `s : Spec B → Spec R` and all `x, y ∈ B`,
  `(v_β(x) v_ε(y))⁻¹ (v_ε(y) v_β(x)) = ∏_r v_{L r}(s(C r) x^{e₁ r} y^{e₂ r})`, the product
  taken in the order of `L`. Here elements of `B` are global functions via the inverse of
  `Scheme.ΓSpecIso`, and `s(C r)` is the image of `C r` under the ring map
  `(Spec.preimage s).hom` of `s`.

## Proof

**Enumerations.** `exists_pos_initial` splits the positive roots into those in `L` and the
others (Mathlib's `Equiv.sumCompl`). The first part is enumerated by `L` itself
(`List.Nodup.getEquiv`), the second by `Finite.equivFin`. The two parts are joined with
`finSumFinEquiv`. `exists_cell_initial` combines this enumeration with the imported
`LocalSplitBigCell.isOpenImmersion_cellMap` and with the cocharacter of the imported
`exists_coPairing_eq_height`, which pairs with every root to a positive multiple of its
height.

**Uniqueness.** In `listProd_rootPoint_injective`, both products are extended by zero
coordinates to ordered products over all positive roots (`orderedProduct_initial`, with the
imported `rootPoint_zero`). The imported `orderedProduct_pos_injective` then identifies the
coordinates.

**The cone.** Choose a base `b` making `β` and `ε` positive (imported
`exists_base_isPos_pair`). Every root in `L` is then positive, because the height
cocharacter pairs positively with `β`, `ε`, and so with each `L r`. Take the cell of
`exists_cell_initial` for `L`. The imported `exists_isUnivComm` gives universal coordinates
`E` of the commutator. At a position after `L`, the imported
`IsUnivComm.eq_zero_of_forall_ne` gives `E = 0`: a monomial of weight
`dS • β + dT • ε` there would be a root of the cone, hence a member of `L`, hence at a
position in the initial segment. At the position of `L r`, the imported `IsUnivComm.weight`
leaves only the monomial `S^{e₁ r} T^{e₂ r}`, by linear independence of `β` and `ε`
(Mathlib's `IsReduced.linearIndependent`). Its coefficient is `C r`. The imported
specialization `IsUnivComm.posComm_eq` and `orderedProduct_initial` give the formula.

## Provenance and scope

This is internal derived content toward the Isomorphism Theorem over an arbitrary local
ring. The shape of the commutator follows the commutation formula of Conrad, *Reductive
group schemes* (2014), Proposition 5.1.14 with formula (5.1.5), where the product over the
roots of the cone is taken in a fixed order. The ordering by an initial segment of the
positive roots is a construction of this module. The module does not compute the constants
`C r`; the `G₂` module `Langlands.GroupScheme.Reductive.LocalSplitTypeG2` computes them in
type `G₂`.
