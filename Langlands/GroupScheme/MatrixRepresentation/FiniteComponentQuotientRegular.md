# Actual regular representations of finite component quotients

Let `G` be a group scheme locally of finite type over an algebraically closed
field `k`, and let `q : G(k) → Q` be a homomorphism to a finite group.
Assume `q` is constant on each actual connected component of `G`.
The construction `finiteComponentQuotientRegular` is an actual matrix
representation of `G` on `Fin (Fintype.card Q) → k`.
Its rational-point representation is the finite-coordinate regular
representation of `Q` pulled back along `q`.

The construction composes the finite regular matrix homomorphism with `q`
and applies the component-constant matrix algebraization. The module proves
its actual component constancy and identifies its rational representation.
The coefficient field and the abstract quotient group share a universe,
while the representation's coordinate index is a finite type in universe zero.

For affine `G`, semisimplicity of any componentwise constant actual
representation implies semisimplicity of its rational-point representation.
Indeed, every rationally stable subspace is all-test stable by the preceding
componentwise-constant criterion. Its all-test stable complement exists by
the stable-subspace semisimplicity theorem and gives a rationally stable
complement.

If `q` is surjective and every actual finite-coordinate representation of
`G` is semisimple, the constructed regular representation is semisimple.
The surjective quotient has the same invariant subspaces for that action,
so the finite regular order criterion gives `¬ p ∣ Nat.card Q`
in characteristic `p`.

This is internal derived infrastructure for Nagata's component-order necessity.
It treats a supplied componentwise constant rational quotient over an
algebraically closed field. Identifying the canonical component quotient and
obtaining the full arbitrary-ground-field statement are separate obligations.
The stable-complement infrastructure was authored by Worker 539 and is reused
unchanged; the component algebraization and regular representation are Worker
544's constructions.

The source motivation is J. S. Milne, *Algebraic Groups*, corrected reprint
(2022), Definition 4.15, Proposition 4.17 and the converse immediately following
it, printed p.90 (PDF p.101), for the semisimplicity and complement convention;
and Remark 12.56, printed p.249 (PDF p.260), for the component-order condition.
The source is registered as `milne-2022-algebraic-groups`. The complete official
errata snapshot of 4 November 2026, registered as
`milne-2022-algebraic-groups-errata-2026-11-04`, has no corrections to these
passages. The actual componentwise-constant algebraization is the internal
construction described above.
