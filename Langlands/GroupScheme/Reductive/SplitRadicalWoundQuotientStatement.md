# Woundness of the ordinary radical modulo the split radical

This module defines the proposition
`Langlands.GroupScheme.SplitRadicalWoundQuotientStatement.{u}`. It states
the woundness conclusion of CGP Corollary B.3.5 using supplied representatives
and a supplied fppf quotient. It contains no proof.

The registered original source is Conrad–Gabber–Prasad,
*Pseudo-reductive groups*, second edition (2015),
`conrad-gabber-prasad-2015-pseudo-reductive`, SHA-256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
The readable PDF is
`/home/taskhub/central-library/Conrad-Gabber-Prasad--Pseudo-reductive groups (book, 2nd edition)--2015.pdf`.
Theorem B.3.4 is on printed pp.573–574 (one-based PDF pp.599–600);
Corollary B.3.5 is on printed p.574 (PDF p.600). No public erratum for this
source was found.

Theorem B.3.4 constructs the maximal split part of a smooth connected
unipotent group and shows that its quotient is wound. Corollary B.3.5
identifies this split part of the ordinary radical with the ambient group's
split radical. The present proposition retains only the quotient's woundness.
It asserts neither the canonical split part's existence nor compatibility
with separable field extension. This is the structural input used in the
first equality of Proposition 2.2.4, printed pp.63–64 (PDF pp.89–90).

The statement quantifies over an arbitrary field `k : Type u` and a smooth
connected affine group scheme `G` over `Spec k`. The supplied maps `j : U ⟶ G`
and `n : V ⟶ G` satisfy the existing predicates `IsUnipotentRadical j` and
`IsSplitUnipotentRadical n`. A supplied homomorphism `m : V ⟶ U` satisfies
`m ≫ j = n`, so it presents the split radical inside the ordinary radical.
No equality between the two radicals is assumed.

For every supplied smooth connected affine group scheme `Q` and homomorphism
`q : U ⟶ Q`, the hypothesis
`RelativeRoot.IsFppfQuotient (SubgroupFunctor.range m) q` says that the
underlying map is flat, surjective, and locally of finite presentation, and
that its full kernel image on every relative scheme test is exactly the
image of `m`. It does not supply a section or a lift on any test.

The conclusion `HasConstantAffineLineMaps Q` says that every scheme
morphism over `Spec k` from the affine line to `Q` factors through a
`k`-point. For smooth connected unipotent groups this is the woundness
condition used in the source. Although unipotence of `Q` is not a separate
hypothesis, it follows mathematically because `Q` is a quotient of the
unipotent group `U`; establishing any such fact needed by a proof remains
an obligation.

This is an all-field formulation at arbitrary universe `u`, including
imperfect fields, finite fields, and characteristic zero. Appendix B is
written for nonzero characteristic. The characteristic-zero case is an
additional proof obligation in this formulation, where smooth connected
unipotent groups are split and the quotient in question is trivial. No
characteristic-zero proof is supplied here.

The radical predicates and the quotient kernel equality retain their
all-relative-test meanings, including nonaffine and nonreduced tests.
The proposition assumes the representatives and quotient as data; it
asserts no existence theorem, torus-action statement, or equality of
pseudo-parabolic products.
