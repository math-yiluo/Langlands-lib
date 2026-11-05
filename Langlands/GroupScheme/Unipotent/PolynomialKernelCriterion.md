# Affine-line constancy and central additive subgroups of polynomial kernels

This is a derived consequence of Conrad–Gabber–Prasad, *Pseudo-reductive
groups*, second edition (2015), Lemmas B.1.7–B.1.9, printed pp.563–565
(one-based PDF pp.589–591). It combines the polynomial-kernel curve and
geometric adapters; it does not give a polynomial presentation of an arbitrary
unipotent group.

Let `k` be any field, `n` any natural number, and let `f : Fin n → k[X]`
be a row of additive polynomials. Additivity is the existing universal
polynomial identity. Write `G` for the actual categorical kernel of
`polynomialRow f hf : Vₙ → V₁`, where `Vₙ` is the standard vector group.

`exists_closed_kernel_section_of_not_hasConstantAffineLineMaps` proves that
failure of actual affine-line constancy for `G` yields an actual homomorphism
`s : V₁ → G` which is a closed immersion and has an actual homomorphic
retraction `r : G → V₁`, with `s ≫ r = 𝟙 V₁`. The proof extracts a nonconstant
polynomial curve from an actual affine-line morphism and applies the previously
constructed closed-section theorem. `polynomialKernelSectionOfNotConstant`
chooses such a section, and its `_spec` theorem supplies these two properties.

`hasConstantAffineLineMaps_polynomialKernel_iff` identifies actual affine-line
constancy for `G` with the absence of a polynomial tuple `φ` such that some
`φ i` has positive degree and `∑ i, (f i).comp (φ i) = 0`. In one direction,
such a tuple gives a closed one-dimensional vector subgroup, which affine-line
constancy excludes. The other direction uses polynomial extraction from
failure of constancy.

`hasConstantAffineLineMaps_polynomialKernel_iff_not_exists_central_additive`
proves the actual central additive-subgroup criterion for `G`: actual
affine-line constancy is equivalent to the absence of an actual central closed
subgroup with natural one-dimensional vector coordinates on every relative
scheme test. The forward implication is the existing unconditional exclusion
theorem. For the converse, failure of constancy gives the chosen closed section
above. The standard vector group has the required natural coordinates, and the
kernel of a homomorphism from a commutative group is commutative. Consequently
the section is central on every test and every refinement, contradicting the
assumed absence.

`hasConstantAffineLineMaps_polynomialKernel_iff_of_isGalois` proves that actual
affine-line constancy for these kernels is unchanged on mapping all
coefficients through an arbitrary algebraic Galois extension `K/k`. The proof
uses the polynomial-curve equivalence and the previously proved Galois
invariance of polynomial-curve existence. The field `K` has an independent
universe; the two actual kernels occur in separate propositions. No direct
cross-universe base-change comparison is asserted.

The characteristic-zero case is included by the preceding polynomial
arguments, which use exponential characteristic one. This all-field extension
is derived; Appendix B has a standing positive-characteristic assumption.
There is no infinitude, perfectness, smoothness, connectedness, or unipotence
assumption here. The row may be empty. All geometric conditions concern actual
schemes and all-test natural coordinates.

The full published `UnipotentWoundCriterionStatement` for arbitrary smooth
connected affine unipotent groups remains open. General coordinate
presentations, vector-factor decompositions, and the structural reduction from
an arbitrary unipotent group to these kernels remain separate obligations.
