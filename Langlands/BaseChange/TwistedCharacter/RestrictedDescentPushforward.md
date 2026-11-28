# Restriction of the tensor identity in descent

`restrictedDescentPushforward` restricts the two source factors of a test
pushforward along open embeddings and extends the target along an open
embedding with closed image. The ambient source factors and the final
target are Hausdorff. The factors, their products used as sources, and
the targets have Borel measurable structures. The first source measure
is finite on compact sets. The source measures and the pullback on the
second factor are s-finite.

The transported pushforward uses the product of the pulled-back source
measures. If the original descent of the target distribution satisfies
a tensor identity of an integration functional and a slice distribution,
evaluation of the new pushforward of a tensor test equals the integral
of its first factor times evaluation of its extended second factor on
the slice distribution.

The comap of the product measure is the product of the comaps of its
factors. This follows by mapping both sides along the product embedding,
where they give the same restriction of the original product measure.
The pushforward identity then follows from `embeddedTestPushforward`.
For the distribution identity, apply the original tensor identity to
the zero extensions of the two factor tests and change variables in
the integral on the first factor.

This restriction is used to evaluate the compact product tests of
Clozel, *Characters of nonconnected, reductive p-adic groups*, §3.4,
printed p. 154. [Original publication](https://doi.org/10.4153/CJM-1987-008-3)
