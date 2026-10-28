# Rational prime-adic Weil pairing

This internal construction extends the actual `primeWeilBilinearMap` from
the p-adic integers to the p-adic rationals. The prime has `Fact p.Prime`.
It retains the seven tensor/Picard propositions, the actual abelian scheme
and its constructed dual, the inverse Poincare bundle and evaluation, and
the explicit `RelativeFiniteWeilTransitionStatement`.

`primeRationalWeilBilinearMap` has the existing rational prime-adic Tate
modules as inputs and the existing rational prime-adic roots-of-unity twist
as output. Each is the tensor product over the p-adic integers with the
p-adic rationals. The private helper extends the linear map from the
tensor product associated to the integral bilinear map, uses the inverse
of the distribution of base change over tensor products, and curries.
This gives bilinearity over the p-adic rationals in both variables.

The pure-tensor formula multiplies the two p-adic rational factors and
applies the integral pairing. The canonical-map formula sets both factors
to one. The uniqueness lemma uses tensor extensionality in both arguments
and fixes exactly this pure-tensor normalization.

`rationalToPrime_rationalWeilBilinearMap` compares the rational pairing of
any selected divisibility system with the prime-adic rational pairing. It
assumes that the system retains every power of this prime. Extraction on
the output twist agrees with extraction on both input Tate modules.
The proof uses tensor induction twice, the rational extraction formulas,
the integral extraction comparison, and compatibility of rational
multiplication with the inclusion into the p-adic rationals.

The full specialization retains all orders. The away specialization
assumes `Nat.Coprime p m`, ensuring that each power of p is retained among
orders coprime to m. These are also comparisons with the underlying values
of the full and away adelic pairings constructed in `WeilRational`.

The provenance is internal scalar extension of the intrinsic integral
pairing, followed by the existing extraction maps on actual Tate modules
and root twists. The finite pairing keeps the convention beta(y)(x).
No twist basis or roots-of-unity trivialization is chosen. This unit
asserts no continuity, perfectness, alternation, nondegeneracy, polarization
specialization or monodromy equivariance. Relative transition compatibility
remains a theorem hypothesis.
