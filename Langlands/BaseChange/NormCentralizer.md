# Centralizers at an associated regular norm

Henniart–Lemaire, *Changement de base et induction automorphe pour GL_n en
caractéristique non nulle* (2011), §§I.2.2 and I.2.4, identify the twisted
centralizer with the ordinary centralizer when the norm is conjugate to a
regular element of `GL_n(F)`. Section I.2.5 uses the identification to
transport Haar measure. `normCentralizerEquiv` gives the continuous
multiplicative equivalence for a chosen association witness `x` satisfying
`x⁻¹ * cyclicNorm σ l δ * x = baseChange F E n γ`.

Put `δ' = x⁻¹ * δ * entrywiseAut σ n x`. The twisted conjugation formula
and `σ ^ l = 1` show that the norm of `δ'` is the base change of `γ`.
The entrywise automorphism fixes that norm. Its formula on the norm
then shows that `δ'` commutes with the norm. An element in the twisted
centralizer of `δ'` also commutes with the norm, by applying the norm
formula to its stabilizer equation. Those two elements commute with each
other by `commute_of_commute_baseChange`. The stabilizer equation now
forces the coefficients of the centralizer element to be fixed by `σ`.
The same holds for its inverse. Both matrices descend entrywise using
the fixed-element clause of `IsCyclicAlgebra`. Their inverse equations
descend by injectivity of the coefficient map on matrices.

Conversely, any element of `glCentralizer γ` extends to a matrix fixed
by `σ` that commutes with `δ'`, by the same regular centralizer
commutativity. It therefore lies in the twisted centralizer of `δ'`.
Conjugation by `x` takes it back to the twisted centralizer of `δ`.
Conjugation by `x⁻¹` followed by coefficient descent gives surjectivity,
and injectivity of coefficient extension gives injectivity.

Coefficient extension is a closed embedding by
`generalLinear_isClosedEmbedding_algebraMap`. Conjugation is the
composition of two translation homeomorphisms. With the centralizers'
subspace topologies, the resulting bijective group map induces the
domain topology, so it is a homeomorphism. Its forward formula is
`normCentralizerEquiv_apply_val`.
