# A finite center basis for norm-kernel summand induction

Worker 86. This internal supporting result derives a finite center basis for the
published `rationalNormKernelSummandInduction` of an irreducible summand of the
restriction of an irreducible smooth representation of a connected reductive group.
It requires no chosen standard family, torus, cuspidality or admissibility hypothesis.

`exists_rationalNormKernelSummandEndCenterBasis` works over a nonarchimedean local field
`k : Type u`, with smooth representation carriers in the independent universe
`v`. The group has its canonical rational-point topology. For irreducible `π`,
irreducible `ρ` of the actual common norm kernel, and an injective morphism
`j : ρ → π|_{⁰G}`, it produces a natural number `m` equal to the complex rank of
that Hom space and a `Fin (m ^ 2)` basis of `End(ind ρ)` over its center.
Affineness and local finite type are supplied by connected reductivity. No
local compactness or nonarchimedean-group premise is needed for this result.

`rationalNormKernelSummandEndCenterBasis` is the corresponding data construction:
classical choice selects `m` and an actual basis, bundled with the equality
identifying `m` with the complex rank of the Hom space. Thus callers receive a
basis with its coordinate equivalence, rather than only an existence
proposition.

The proof uses the finite-length clause of the published
`rationalNormKernelFiniteRestriction`, the countable-dimensional Schur argument
in `finiteDimensional_rationalSummandHom`, the embedding to prove that the Hom
space is nonzero, and `rationalSummand_cyclic_of_isIrreducible`. The published
`NormalHecke.exists_basis_center` then gives the basis. Frobenius reciprocity
identifies its rank with the square of the finite multiplicity of the summand in
the restriction. The center as a subalgebra and as a subring has the same carrier
and scalar action, so the result uses the `Subring.center` of the VI.10.4 target.

`unique_center_right_expansion` translates a finite center basis into unique
expansions with coefficients on the right, using the basis coordinate
equivalence and the commutation property of central elements.
`unique_right_expansion_trans` substitutes the unique center expansions of the
coefficients in a finite right expansion along any ring homomorphism. Uniqueness
first recovers each intermediate coefficient and then its center coordinates.
The result does not require the image of the center to be central in the larger
ring.

`finite_unique_right_expansion_trans` reindexes the product of the two finite
index sets by `Fin (n * m)`.

`leviInducedEndCenterExpansion_of_endExpansion` applies these constructions to
the exact `rationalNormKernelSummandInduction M ρ` and `leviInductionFunctor` of
`InducedProgeneratorEndFreeStatement`. The ambient assumptions are the
Hausdorff nonarchimedean local field, an affine ambient group scheme with
locally compact nonarchimedean rational points, and an actual rational
parabolic with Levi, unipotent radical and semidirect multiplication data. The
Levi is connected reductive by the published rational-Levi theorem, which
supplies the hypotheses of the center-basis result.

For irreducible `π`, irreducible `ρ` and the same injective `j`, this adapter
takes an `n`-element family `b` giving unique expansions
`x = ∑ i, I.map (a i) ≫ b i` with `a i ∈ End Π_D`. It returns a finite family
giving unique expansions of exactly the same form with coefficients in
`Subring.center (End Π_D)`. The constructed family has `n * m²` members, where
`m` is the finite multiplicity above. Additivity and functoriality package the
induction map as a ring homomorphism. Substitution uses the vectors
`b_i * I.map(c_j)` and the product index set, then reindexes by `Fin`.
Here `f ≫ g = g ∘ f`, and multiplication of endomorphisms is composition, so a
right-coefficient product `b_i * I.map(a_i)` is precisely
`I.map(a_i) ≫ b_i`.

These results reuse the published VI.4.4 argument at its actual generality.
They do not construct the induced endomorphism basis required by the first
VI.10.4 lemma, prove its center inclusion, or prove any of the four complete
target propositions. In particular the adapter's expansion premise is the
preceding basis obligation in the first target, rather than an unconditional
construction of that basis. Supercuspidality is unnecessary for the adapter,
but remains a premise of the complete target.

The provenance is internal: these are direct specializations and algebraic
consequences of the published `NormalHeckeHomDetection`,
`RationalNormKernelFiniteRestrictionProof`, `NormalHeckeCenter`,
`RationalSummandSmallProgeneratorStatement` and `LeviCenterDescent`
declarations. No new translation of the source literature is asserted.
