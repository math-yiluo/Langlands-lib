# Galois descent of split additive polynomial kernel curves

Author: Worker 864.

This is a derived polynomial form of Conrad–Gabber–Prasad, *Pseudo-reductive
Groups*, second edition (2015), Lemmas B.1.7–B.1.9, printed pp.563–565,
one-based PDF pp.589–591. The registered source is
`conrad-gabber-prasad-2015-pseudo-reductive`, with SHA256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.

The principal declaration
`Langlands.GroupScheme.Unipotent.HasNonconstantPolynomialKernelCurve`
is an internal predicate for a finite family `f : ι → k[X]`. It means that
there exists a tuple `φ : ι → k[X]` with a coordinate of positive natural
degree and with the exact polynomial relation

`∑ i, (f i).comp (φ i) = 0`.

The definition does not assume that either family is additive. The theorems
comparing this predicate with split additive curves assume that each `f i`
is additive as a polynomial identity. This is stronger than testing
additivity only on rational points and applies over finite fields.

The coefficient field `k`, extension field `K`, and finite index type `ι`
have independent universes. There is no perfectness or infinitude
assumption. `IsGalois k K` is Mathlib's algebraic Galois condition, without
a finite-degree restriction. The empty index type is allowed: its
nonconstant-curve predicate is false.

`HasSplitAdditiveKernelCurve`, imported from `AdditiveKernelRetraction`,
records additive tuples `ψ` and `r` such that the kernel relation holds
for `ψ` and `∑ i, (r i).comp (ψ i) = X`. The new theorem
`hasSplitAdditiveKernelCurve_iff_hasNonconstantPolynomialKernelCurve`
identifies this condition with the new predicate when `f` is additive.
In one direction it uses the existing degree-induction construction.
In the other, if all `ψ i` were constant, their additivity would make
them zero; additivity of `r` would then contradict the retraction
identity. Thus the retraction forces a positive-degree coordinate.

The supporting lemma `OneDimensional.IsAdditive.map_algebraMap` proves
that mapping coefficients preserves polynomial additivity. It evaluates
the original identity in the two-variable polynomial algebra over `K`
and uses compatibility of evaluation with scalar extension.
`HasSplitAdditiveKernelCurve.map_algebraMap` maps both tuples and both
identities, using preservation of sums and composition by polynomial
mapping. This direction needs no Galois assumption.

`HasSplitAdditiveKernelCurve.of_polynomialShear` returns a split curve
from the equation transformed by an invertible additive triangular
shear. It applies the forward shear to the section. It changes only the
distinguished coordinate of the retraction row, replacing it by the
sum of the old row polynomials composed with the inverse-shear
coordinates. The substitution identity proves the kernel relation,
and inverse-after-forward cancellation proves the retraction identity.

`exists_principalPart_zero_of_galois_curve` assumes all equation
coordinates are nonzero and additive. A nonconstant curve over `K`
first gives a nonzero zero of the principal form over `K` by the
existing highest-degree coefficient argument. Every nonzero additive
polynomial has degree `p ^ m i`, where `p` is the exponential
characteristic. The imported Galois power-sum descent then provides
a nonzero zero of the principal form over `k`.

The main construction
`hasSplitAdditiveKernelCurve_of_pointed_galois` starts with a nonzero
curve over `K` whose constant coefficients vanish. Its private helper
uses strong induction on an upper bound for `∑ i, (f i).natDegree`.
If some `f j = 0`, the existing same-field result applies to the
coordinate curve `X` at `j` and zero elsewhere. Otherwise the
principal-zero lemma supplies a base-field zero, and
`exists_degree_reducing_polynomialShear` supplies a base-field shear
that strictly lowers the degree sum.

The equation and shear stay over `k`; the retained curve stays over
`K`. The proof maps the shear to `K` and transports that curve through
its inverse. The inverse identity preserves nonzeroness, and the
coefficient-zero identity preserves pointedness. Compatibility of
polynomial mapping with sums and composition proves the transformed
kernel relation. The induction hypothesis gives a split curve over
`k` for the transformed equation, and `of_polynomialShear` returns
it to the original equation.

This procedure obtains a fresh principal zero at each step. It does
not assume that one principal zero in fixed coordinates suffices;
CGP explicitly warns against that claim before B.1.7.
`hasSplitAdditiveKernelCurve_of_nonconstant_galois` removes pointedness
by first using the imported additive-curve extraction over `K`.
The result is a split additive polynomial curve over `k` from any
nonconstant polynomial curve over `K`.

Finally, `hasSplitAdditiveKernelCurve_iff_of_isGalois` combines this
construction with scalar extension. The theorem
`hasNonconstantPolynomialKernelCurve_iff_of_isGalois` rewrites both
sides using the same-field comparison. These give the polynomial
existence invariance underlying CGP B.1.9, without claiming a full
coordinate isomorphism of vector groups.

Appendix B assumes positive characteristic. This implementation also
covers characteristic zero: it uses `ringExpChar k`, which is one
there, and the imported all-field degree theorem makes every nonzero
additive coordinate linear. Both the degree reduction and power-sum
descent remain valid in this case. This extension and the explicit
retraction are derived content.

These results concern polynomial tuples and coefficient mapping.
Actual group-scheme morphisms and closed immersions, full coordinate
isomorphisms, vector-factor decompositions, arbitrary-group
presentations, and the complete woundness criterion remain separate
obligations.
