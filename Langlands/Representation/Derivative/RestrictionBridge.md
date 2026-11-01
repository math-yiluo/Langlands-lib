# General linear derivatives through the mirabolic restriction

Module `Langlands.Representation.Derivative.RestrictionBridge`, namespace
`Langlands.Derivative.RestrictionBridge`.

The published `GL` derivative of positive order
(`Langlands.Derivative.generalLinearDerivative`) is defined as the mirabolic
derivative of the restriction to the mirabolic subgroup, up to rank
transports. This module records that identification for objects and for
nonvanishing. It also proves a homogeneity criterion: a mirabolic
representation all of whose nonzero derivatives have one order is
homogeneous. The proof of Zelevinsky's Theorem 6.2 uses these to move between
`GL` derivatives of segment-socle products and the mirabolic level of their
restrictions.

## Provenance

This is internal derived material. Bernstein–Zelevinsky
(`bernstein-zelevinsky-1977-induced-i`, §3.5 and §4.3) define the derivative
of a `GL_n` representation as the mirabolic derivative of its restriction to
`P_n`. Zelevinsky (`zelevinsky-1980-induced-ii`, §5.2, printed p.187) uses
this to define homogeneity of `GL_n` representations. The first four results
below unfold the published definitions to this form. The last result is a
routine consequence of derivative detection and exactness; it is not stated in
either source.

## Conventions

`{p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}`, `T : F.TopologicalData` and
`ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology` are fixed, with
`T.topology` installed. Carriers are in `Type uV`.
`generalLinearRestriction T n` restricts a smooth representation of
`GL_(n+1)` to `mirabolic n F.Carrier = P_(n+1)`. `generalLinearRankCast T h`
and `mirabolicRankCast T h` are the published equality transports between
categories at equal ranks.

## Declarations

- `generalLinearRestriction_rankCast_obj e e'`: for `e : n+1 = c+1` and
  `e' : n = c`, restricting a `GL` transport along `e` equals transporting the
  restriction along `e'` (objectwise).
- `generalLinearDerivative_succ_obj_eq hk hk'`: for `A` on `GL_(n+1)` and
  `j + 1 ≤ n + 1`, the `GL` derivative of order `j+1` of `A` *equals* (as an
  object, with no further transport) the mirabolic derivative of order `j+1`
  of the restriction `(generalLinearRestriction T n).obj A`, i.e.
  `(mirabolicDerivativeOfOrder T ψ n (j+1) hk').obj (Res A)`. Proof: unfold
  `generalLinearDerivative_succ_obj`, `generalLinearDerivativePositive_obj` and
  `mirabolicDerivativeOfOrder_obj`, then apply the previous lemma.
- `generalLinearDerivative_obj_eq_cast ha hk hk' h`: the same identification
  for a source on a rank `a` with `ha : a = n + 1` and any positive order `k`.
  The target is transported along `h : a - k = n + 1 - k`, and the source
  along `ha` before restricting.
- `nontrivial_generalLinearRankCast_iff`: rank transport preserves
  nontriviality.
- `nontrivial_generalLinearDerivative_iff ha hk hpos`: for `0 < k ≤ a = n + 1`,
  the `GL` derivative of order `k` of `A` is nontrivial iff
  `HasNonzeroDerivative T ψ (Res (cast A)) k`, where `Res (cast A)` is the
  restriction to `P_(n+1)` of `A` transported to `GL_(n+1)`.
- `isHomogeneous_of_single_order hE c A hA`: let `hE` be the published
  proposition `Mirabolic.MinusExactnessStatement F T`, taken as an **explicit
  hypothesis**. Let `A` be a smooth representation of `mirabolic N F.Carrier`
  such that every order `j` with `HasNonzeroDerivative T ψ A j` equals `c`. Then
  `IsHomogeneous T ψ A`. Proof: let `W` be nontrivial with an injection
  `W ⟶ A`. By the published detection theorem (`LevelCalculus.level_pos`), `W`
  has a nonzero derivative of order `level W > 0`. By exactness
  (`LevelCalculus.hasNonzeroDerivative_of_injective`), `A` has a nonzero
  derivative of the same order. So `level W = c`, and
  `LevelCalculus.isHomogeneous_of_forall_injective` concludes.
