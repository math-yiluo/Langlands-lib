# Affine root systems admitting rank zero

Module `Langlands.Geometry.Building.RankZeroAffineRootSystem`, namespace
`Langlands.Geometry.Building.AffineRootSystem`.

`IsAffineRootSystemWithRankZero` is the reviewed derivative-spanning version of
AR 1: the derivative roots span the dual vector space, every affine root is
nonconstant, and the derivative-root set is finite. AR 2 supplies coroots,
AR 3 asserts their integral pairings, and corrected AR 4 requires infinite
fibres with finite bounded subsets. The existing `IsAffineRootSystem` in
[AffineRootSystem](AffineRootSystem.md) retains its affine-spanning AR 1.
The two predicates have different meanings at rank zero and retain separate names.

Kaletha–Prasad print “Ψ spans A*” in Definition 1.3.1 (book PDF p.45,
printed p.14), but the following rank sentence and Remark 1.3.2(4)
(PDF p.46, printed p.15) include the empty system on a point. The derivative
form expresses that convention and is the form used in the proof of Lemma
1.3.6 (PDF p.47, printed p.16).

`IsAffineRootSystemWithRankZero.span_eq_top` proves affine spanning when the
root set is nonempty. Infinite fibres supply two distinct roots with the
same derivative; their difference is a nonzero constant. Thus the span
contains every constant, and derivative spanning supplies every remaining
affine functional. The converse linear-algebra implication is the existing
`span_derivativeRoots_eq_top` in [AffineWeylGroups](AffineWeylGroups.md).

`isAffineRootSystemWithRankZero_empty_iff` identifies the empty-system case
with `Subsingleton V`; `IsAffineRootSystemWithRankZero.nonempty_iff_nontrivial`
states the corresponding rank criterion. The module also retains the
variant's `neg_mem` and `isCoroot_unique` proofs, using its unchanged coroot
axioms and the finite spanning derivative-root set. It reuses the existing
affine and derivative Weyl groups without redefining them.

These are the definition and proofs submitted with `KPApartmentAxioms`,
relocated and renamed during integration without changing their statements.
The apartment predicate uses this variant for both AS 2 and AS 3.

Sources: Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
§1.3, registered as `kaletha-prasad-2023-bruhat-tits-new-approach`,
SHA-256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`;
*Corrections and additions* (1 November 2024), PDF p.2, registered as
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.
