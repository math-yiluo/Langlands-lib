# Application of the supplied imaginary intertwiner to a finite family

`IsRegularIntertwiningExpansion` collects the expansion data consumed by
`IsImaginaryIntertwiningOperator`. It requires square-integrable target forms,
meromorphic coefficients with a holomorphy domain containing the imaginary
axis, and agreement with `IsIwasawaCompact.intertwiningOperator` throughout a
sufficiently regular source chamber. This is the operator obtained from
`intertwiningIntegral` by multiplying by the inverse target height factor at
the transported parameter \(w\lambda\).

`IsImaginaryIntertwiningOperator.ae_apply_finite_sum` uses that predicate for
one expansion of each source form. At the fixed imaginary parameter, it
uses `MemLp` of each source restriction to construct its class in the inducing
Hilbert space.
Almost-everywhere agreement identifies the supplied vector with the finite
linear combination of these classes. The proof applies the operator to that
sum and distributes the scalar factors, using the representative supplied by
the intertwining hypothesis on each term. The resulting formula holds almost
everywhere for the weighted target `inducedL2Measure`. The expansion lengths and domains can
vary with the source form.

`IsImaginaryIntertwiningOperator.pointwise_eq_of_finite_sum` adds a target
finite presentation of the intertwiner value. The positive definite inducing
norm then identifies its actual adelic function with the finite expansion of
the source image. It applies to a Weyl relation in `symmetricFamilySpace` at
each parameter where both restrictions and the relation hold. This recovers
the pointwise equality needed to compare the two inducing functions under
averaging.

This is derived from the defining agreement in `IsImaginaryIntertwiningOperator`,
which implements the action on a dense class of inducing forms in J. Arthur,
*An introduction to the trace formula* (2005), pp. 34–35 (volume PDF pp. 46–47),
registered as `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`,
SHA-256 `88ba9a23fa62e2f62f14af7a5a2a8ffb062be29fc4590bf39c60c173add0a8a7`.

E. Lapid, *On Arthur's asymptotic inner product formula of truncated
Eisenstein series* (2011), §2, p. 311 (volume PDF p. 320), gives the inducing
form and its split-component quotient norm. The working hypothesis on p. 312
(volume PDF p. 321) describes finite-dimensional target values and the
subsequent discussion gives imaginary-axis holomorphy. The predicate takes
these properties in the form of one supplied finite expansion. The registered
source is `lapid-2011-asymptotic-inner-product-truncated-eisenstein`, SHA-256
`760161175f57a28d2e05de1f5638bc205d33123ae95f67ce4296b4b651fa950b`.
