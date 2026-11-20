# Scalar meromorphic identity with a finite sum in changed coordinates

The theorem `Langlands.Analysis.Meromorphic.scalarMeromorphicSumIdentity`
proves `ScalarMeromorphicSumIdentityStatement` using the scalar identity
principle in `ScalarIdentity`. For a nonempty family, compose the
meromorphic functions on `Y` with the parameter equivalence `e` and
multiply each by its coefficient. Every product is meromorphic on
`V ∩ e ⁻¹' W`. The first product supplies openness and density of that
domain in every chart. The finite sum is therefore meromorphic there.
The two-function identity principle extends the given equality on the
open patch to the intersection of this domain with `U`.

For an empty family the right side is the entire zero function. The
identity principle gives vanishing throughout `U`, and in particular
on the domain required by the conclusion. This case uses no openness
or density of `V` or `W`.

The proof is the scalar propagation step for the universal form of
Bernstein–Lapid's functional equation in Theorem 2.3 (4), with the
meromorphy predicate from §3.1. The initial equality is supplied by
the hypotheses of the statement.
