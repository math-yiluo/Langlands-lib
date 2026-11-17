# Formula for actual translation followed by a standard tensor

This internal algebraic adapter proves the composite formula used by
Waldspurger (2003), V.3 formula (1), printed p.295 / PDF p.61, registered as
`waldspurger-2003-plancherel`. It combines the two preceding algebraic stages
into a single pure-tensor equality and a single product-induction evaluation
equality. The carrier group and both representation carrier universes are
independent. The group has the locally compact nonarchimedean structure
needed by the existing normalized inductions, with second countability
and compactness of each displayed parabolic quotient for the tensor
comparisons.

The data are a source semidirect decomposition, its conjugate decomposition
under a displayed group element, and a final decomposition with the same
literal Levi as the conjugate one. The actual subgroup membership
comparisons, closed radicals and their unimodular moduli are displayed.
The input `e` is an inducing representation equivalence from the generic
conjugate object to the specified intermediate/final inducing object.
The vector and smooth-dual factors `vectorFactor` and `dualFactor` consist
of the actual published left translations followed by inducing transport
through `e` and its inverse smooth-dual pullback.

The helper exposes a forward induced intertwiner `J` and a reverse
induced-dual intertwiner `R`, with bijectivity of that particular `R`.
`comparison` is the literal composite of actual coefficient left
translation, pointwise positive-Levi inducing transport `coefficientCongr`,
and `reverseDualTensorComparison` for these `J` and `R`. Its inverse factor
is the inverse of `R` itself, constructed by `reverseInducedDualInverse`.
Thus this helper keeps the algorithm and all its operator inputs visible.

`comparison_tmul` proves the single composite pure-tensor formula. Its
right side is the actual target product-induction tensor of
`J (vectorFactor f)` and `reverseInducedDualInverse R (dualFactor ℓ)`.
`comparison_tmul_eval` proves evaluation at every pair of group elements:
the left side evaluates that same constructed composite on the actual
source product tensor, and the right side is the tensor of the two target
induced function values at the first and second coordinate respectively.
The positive-Levi tensor comparisons and coordinate order are retained.

The implemented proof establishes the composition identity with abstract
carriers before specializing its inputs. It first combines the published
actual translation pure law with `coefficientCongr_tmul`, then applies the
published forward/inverse-reverse tensor pure law. Evaluation follows by
the existing positive-Levi product-induction tensor evaluation theorem.
`ExpandedTensorFormula` and `ExpandedEvaluationFormula` are the exact
Prop-valued versions of these expanded equalities; both are proved in the
same file. All proofs are elementary identities of the constructed maps.

For the actual rational-point operator in `ActualConjugateLeviTensor`,
put `χg = χ ≫ (G.innerIso g).hom`, `gA = conjugateRepresentation χ g A` and
`z' = ActualConjugateLeviTensor.genericParameter ... z`. The actual input
substitution is:

| Helper data | Actual constructed data |
| --- | --- |
| Ambient group | `RationalPoint F G.X`, with its canonical point topology |
| Source decomposition | `decomposition χ`, equivalently `commonDecomposition χ χ rfl` |
| Intermediate decomposition | `commonDecomposition χg χg rfl` |
| Target decomposition | `commonDecomposition χg ψ' hψ'` |
| Source inducing object | `ActualCommonLeviTensor.twistObject χ z.val A` |
| Intermediate/target object | `ActualCommonLeviTensor.twistObject χg z'.val gA` |
| Conjugating element | The actual rational point `g` |
| Subgroup comparisons | `DynamicCoefficientConjugation.parabolic_mem_conjugation`, `levi_mem_conjugation`, `radical_mem_conjugation` at `χ,g` |
| Closedness and unimodularity | `radical_isClosed` and `DynamicOppositeCanonicalScalar.radical_unimodular` at the displayed cocharacters |
| Inducing equivalence `e` | `ActualConjugateLeviTwist.conjugateTwistEquiv χ g z.val A`, with `z'.val` equal by definition to `conjugateParameter χ g z.val` |
| Forward `J` | `ActualCommonLeviTensor.ContinuedPair.operator` for the specified forward continuation `p` at `⟨z'.val, z'.property.choose.1⟩` |
| Reverse dual `R` | `ActualCommonLeviTensor.reverseDual` for the specified `p,q` at `⟨z'.val, z'.property.choose⟩` |
| Reverse bijectivity | `z'.property.choose_spec.2`, on the actual simultaneous generic locus |
| Quotient compactness | The displayed source compact representatives and the intermediate/target compact representatives used by `quotientCompact` |

At these inputs `comparison` is the expression defining the actual
rational-point `genericComparison`: the actual common-Levi tensor after
actual coefficient translation and the canonical conjugate-twist inducing
transport. The two theorems therefore give its forward-translation and
inverse-reverse-dual-translation formula and evaluation in the same
source-normalized coefficient model. This generic algebraic form avoids
repeating the costly concrete carrier conversions of a second specialized
synonym. The actual construction fixes every map in the table; this helper
adds no freely supplied normalized coefficient comparison or compatibility
square to that construction.

The module introduces no Haar measure, coefficient scale, formal degree
or second quotient-duality normalization. The actual application uses the
existing full rational-character parameter group and actual smooth
contragredient. Bijectivity of `R` is the explicit generic-domain input,
not an assertion of all-unitary factor regularity. Continuation existence,
nonempty/dense generic loci, unitary extension, integrated coefficient and
Hermitian form identities, cocycle and Weyl descent remain separate
conclusions or targets of the surrounding development.
