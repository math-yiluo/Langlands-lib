# Anisotropy of multiplicative-type quotients by maximal split subtori

Authors: Worker 1567 and Worker 1232.

`Langlands.GroupScheme.MultiplicativeTypeSplitQuotientAnisotropyStatement.{u}`
is an algebraic proposition over every field `k : Type u`. It is a proof
target; this module does not prove that proposition.

For an actual group scheme `Z` of finite-type multiplicative type, an actual
commutative group scheme `A`, a maximal split-subtorus inclusion
`j : A.toGrp ⟶ Z`, and an actual group-scheme morphism `q : Z ⟶ C`, it
assumes that `q` is an fppf quotient by the full all-test range of `j`.
It asserts `HasAnisotropicTorusFiniteQuotient C`. Unfolding the latter
predicate, there must be an actual torus `T`, a closed immersion `T ⟶ C`
with `splitRank T = 0`, an actual finite group scheme `Q`, and an fppf
quotient `C ⟶ Q` by the full all-test range of that immersion. Both fppf
quotient premises include flatness, surjectivity and local finite
presentation of the underlying scheme morphism, and equality of the
scheme-kernel functor with the specified range functor.

No smoothness, reducedness, connectedness, perfectness or characteristic
restriction is imposed on `Z`, `C` or `Q`. The finite group scheme `Q`
retains its possible nilpotents. There is no rational-point surjectivity,
finite point-cokernel, topology or compactness assertion in the proposition.
The ambient group `Z` is not replaced by its largest torus.

The statement is a derived consequence to be formalized from Milne,
*Algebraic Groups* (2017), source `milne-2017-algebraic-groups`:
Definition 12.17 and closure under subgroups and quotients, printed p.236 /
PDF p.252; the exact Galois-character equivalence in Theorem 12.23 and the
torus/finite extension in Corollary 12.24, printed p.240 / PDF p.256;
the largest-torus construction in Notation 12.29, printed p.241 / PDF p.257;
and Exercises 12-2, 12-5 and 12-6, printed p.252 / PDF p.268.
It is not a verbatim numbered assertion of the book.

These passages give the intended algebraic route: the quotient remains
of multiplicative type, and its largest torus has finite schematic
quotient. Its largest split subtorus must be trivial by maximality of `A`.
The corresponding character-module comparison, including the passage
between the source and quotient maximal split subtori, is part of the
unproved target. Milne's Exercise 12-5 uses absence of nontrivial
`k`-characters as the convention for anisotropy of tori. The Lean conclusion
instead uses the published split-rank-zero predicate; their equivalence
for tori also belongs to the required argument, for example through the
finite-Galois rational character representation and its dual. The
proposition does not silently identify these definitions. The complete
registered official errata snapshot of 2 November 2026 was checked;
the Chapter 12 corrections concern 12.41 and 12.57 and do not change the
passages cited here.

The module also proves
`IsSplitComponent.isMaximalSplitTorus_centerFactor`. Given an actual
representative `z : Z ⟶ M` of the full scheme-theoretic center, a split
component `i : A.toGrp ⟶ M`, and an actual factor `j : A.toGrp ⟶ Z`
with `j ≫ z = i`, the factor `j` is a maximal split subtorus in `Z`.
Its splitness comes from `i`, and its closed immersion follows from
`IsClosedSubgroup.of_comp` and the closed center inclusion. Any larger
split subtorus `j'` in `Z` gives a central split subtorus `j' ≫ z` in `M`
by composition of closed immersions and the all-test centrality of `z`.
Associativity turns a factorization through `j'` into the factorization
required by maximality of `i`, which supplies the required isomorphism.
This is a direct consequence of the published definitions and does not
require reductivity or a smooth center.

`MultiplicativeTypeSplitQuotientAnisotropyStatement.centerQuotient`
then applies its explicit structural-statement hypothesis to `Z`, that
maximal split factor `j`, and the specified actual quotient `q`. It
requires both a full-center representative and its multiplicative-type
property; it does not construct either. Quotient existence, algebraic
affineness, rational lifting through the split torus, anisotropic
compactness and the comparison with the full-center point quotient
remain separate obligations for the full compactness theorem.
