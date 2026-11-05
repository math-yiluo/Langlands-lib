# Finite exponent support from spanning and finite generation

This internal reduction supports the finiteness assertion in Renard 2026,
VII.1.1, printed page 220 / PDF page 226. Its proof uses the published uniform
generalized weight spaces and their independence, together with compactness of
the top submodule of a finitely generated group-algebra module.

`GeneralizedWeightFiniteSupportStatement` says that a smooth representation
with spanning generalized weight spaces and finite generation over its acting
group algebra has finitely many smooth nonzero generalized weights. The field,
central group, acting group, and representation carrier have independent
universes. The acting group is nonarchimedean and weakly locally compact, as
required by the compact-open definition of the weight spaces. The central
group has a topology; its point homomorphism need not be continuous for this
finiteness implication.

`finite_generalizedWeights_of_spanning` proves this implication without
admissibility or algebraic closure. It translates the supplied spanning
equality from scalar submodules to group-algebra submodules. Finite generation
makes the top submodule compact, so finitely many weight submodules already
span. Independence then forces every nonzero weight into that finite set.
The smoothness hypothesis supplies the independence theorem.
`generalizedWeight_finiteSupport` packages this proof as a theorem of the
named proposition.

The represented-parabolic specialization uses the actual literal parabolic,
Levi, and radical point images and their published semidirect decomposition.
`finite_normalizedJacquetExponents_of_compactQuotient_of_spanning` applies the
published compact-quotient finite-generation theorem to the actual normalized
Jacquet functor, then applies the generic finite-support lemma. Its supplied
spanning equality is indexed by actual normalized Jacquet exponents, exactly
as in `ArbitraryParabolicExponentStatement`. Enlarging that supremum to all
characters gives the generic lemma's spanning hypothesis.

`finite_normalizedJacquetExponents_of_hasFiniteLength_of_compactQuotient_of_spanning`
deduces ambient finite generation from finite length, and applies the previous
result. Both wrappers retain compactness of the literal quotient
`Induction.LeftQuotient (pointImage p)` and the Jacquet spanning equality as
explicit hypotheses. They require neither admissibility nor finite length of
the Jacquet module, and do not assert either preservation property. They do
not prove those retained hypotheses or the full arbitrary-parabolic target.

The generic argument is an internal strengthening of the admissible
finite-support proof in `SplitComponentDecomposition`: explicit spanning
replaces admissible center-finiteness and algebraic closure. The concrete
finite-generation input is reused from `JacquetFiniteGeneration`, including
its actual Haar normalization. The source's later Casselman and VII.2
obligations are separate.
