# Conjugation of the actual rational source gamma

This is an internal covariance comparison for Waldspurger's common-compact
normalization in I.1, printed p.240 / PDF p.6, before formulas (2) and Remark
(3). The registered source is `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
The source does not state this comparison as a separately numbered result.

The field has arbitrary universe and is a nonarchimedean local field; no
characteristic-zero assumption is made. The group scheme is affine and locally
of finite type, without a splitness, quasisplitness or reductivity restriction.
Its rational points have their canonical evaluation topology and Borel
measurable space. Local compactness and the closedness of the actual dynamic
parabolics and radicals come from the existing rational-point theorems.

`conjugateCompact g K` specializes `sourceCompactImage` to the existing
`GroupScheme.rationalPointsConjHomeomorph`. Its underlying map is exactly
`x ↦ g x g⁻¹`. Thus the image compact is an actual compact open of the same
rational-point group; its membership equivalence and compactness use the
already proved ambient transport results. If `g` belongs to `K`, subgroup
multiplication and inversion prove that this image equals `K`.

`oppositeCocharacter_conjugate` is just associativity of the actual scheme
morphism composition: precomposition by the power-minus-one map commutes with
postcomposition by the scheme inner automorphism. The proof introduces no
replacement opposite group or cocharacter realization assumption.

`gamma_eq_of_compactPreserving_conjugation` allows two chosen compact opens
whose elements correspond under this conjugation. The existing dynamic
functoriality theorems identify the literal conjugate parabolic and the literal
conjugate opposite radical. At the identity test scheme the constant base
point is the rational conjugating point itself. The exact ambient gamma
transport theorem then applies to the existing intrinsic mass-one subgroup
Haar measures on those original subtypes. It yields equality with the precise
original scale and no free Haar scalar.

`gamma_conjugateCompact` applies this comparison to the transported compact
for every rational conjugating point. `gamma_conjugate_of_mem_compact` applies
it to the same compact when the conjugating point belongs to that compact.
These comparisons require no Iwasawa factorization, compact-limit stability,
chosen components, Levi unimodularity, open-cell embedding, conullness,
convergence or finite positive gamma premise. They compare the already defined
ENNReal double integrals, including their possible infinite values.

This does not establish the source special compact or independence of gamma
between arbitrary parabolics sharing a Levi. In particular it does not assert
that every such pair is conjugate by an element of the chosen compact. The
root-index factorization, special-compact geometry, analytic convergence and
Plancherel conclusions remain separate obligations.
