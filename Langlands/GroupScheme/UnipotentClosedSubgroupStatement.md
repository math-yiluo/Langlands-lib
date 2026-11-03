# Closed subgroups of unipotent group schemes are unipotent

`Langlands.GroupScheme.UnipotentClosedSubgroupStatement.{u}` is a
proposition target, not a proof.

Let `k : Type u` be a field and let `H` be a group scheme over `Spec k`
whose structure morphism is affine and locally of finite type. Let
`w : W ⟶ H` be a homomorphism of group schemes that is a closed subgroup
(`IsClosedSubgroup w`: the underlying morphism of schemes is a closed
immersion). If `H` is unipotent, then so is `W`.

Unipotence is the existing Library predicate `IsUnipotent`: every nonzero
finite-dimensional matrix representation over `k` has a nonzero fixed
vector. This is Milne's definition of a unipotent algebraic group.

## Source

J. S. Milne, *Algebraic Groups* (2017), Corollary 14.7, printed p.282
(zero-based PDF page 297): "Subgroups, quotients, and extensions of
unipotent algebraic groups are unipotent." This statement is the subgroup
clause only. Milne's proof of that clause: a unipotent group has a faithful
unipotent representation (Corollary 14.6, from Theorem 14.5), and its
restriction to an algebraic subgroup is again faithful and unipotent.

Milne's algebraic groups are group schemes of finite type over `k`, and
Chapter 14 concerns affine ones. The hypotheses here put `H` in that
setting: an affine morphism is quasi-compact, so `H` is of finite type.
The closed subgroup `W` is then also affine and of finite type, so no
separate hypothesis on `W` is needed. An algebraic subgroup in Milne's
sense is a closed group subscheme, which is what `IsClosedSubgroup`
encodes.

The official author errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02` was read; it has no
correction to Corollary 14.6 or 14.7.

## Use

This is a prerequisite for the envelope step in the proof of
`Langlands.GroupScheme.ChevalleyUnipotentEnvelopeStatement`: a closed
subgroup of the unipotent part of a Borel subgroup is unipotent.

Source: `milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
