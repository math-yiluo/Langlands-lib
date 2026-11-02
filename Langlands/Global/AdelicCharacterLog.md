# The actual normalized logarithmic character map

For a number field `F` and an actual group scheme `G` over `Spec F`,
`GroupScheme.rationalCharacters G` is the existing `GroupScheme.HomAdd G Gm`: every
actual rational algebraic character, with pointwise multiplication written
additively. The construction imposes no commutativity, splitness or reductivity
assumption on `G`. `RealCharacterDual F G` is
`Hom_Z(GroupScheme.rationalCharacters G, ℝ)`, implemented as additive homomorphisms with
pointwise real vector-space operations. Its topology is induced by evaluation
in the product of copies of `ℝ` indexed by the actual rational characters.
`dualEval` is real linear and continuous. Evaluation separates dual elements,
so the topology is Hausdorff. Pointwise addition, negation and real scalar
multiplication are continuous; the additive group carries its usual
compatible group uniformity.

`characterLog F G x` evaluates at `χ` as the real logarithm of the existing
normalized character norm `characterNorm F G χ.toMul x`. This is the product
of the normalized local absolute values on the actual character idele; it is
not an arbitrarily chosen family of characters or a coordinate norm.
Evaluation of a sum of characters is multiplication of coefficient units, by
the existing additive point-evaluation map and the actual `Gm` units
equivalence. The normalized norm preserves this multiplication, and the
logarithm of a product of positive values is their sum. This proves the
functional is additive in characters. The same identity proves that
multiplication of adelic points becomes addition of their log functionals.

`characterLog_eq_zero_iff` identifies its kernel with the existing actual
`normOneSubgroup F G`. Positivity of each unit norm makes logarithm zero
equivalent to norm one; no assertion about the rank of the character group
enters this argument. The product formula gives zero on principal rational
points. The existing theorem that every compact subgroup is contained in
the norm-one subgroup gives zero on every supplied compact subgroup.
Each evaluation coordinate is continuous by continuity of the actual character
norm and logarithm on positive real numbers; the induced topology gives
continuity of the whole log map.
`characterLogHom` bundles this map as a continuous homomorphism into the
multiplicative notation for the additive real dual, with the same norm-one
kernel.

The existing `GroupScheme.characterRestrict` gives additive pullback along
an actual group-scheme homomorphism. Precomposition with this pullback defines the continuous
real-linear map `realCharacterDualMap` in the other direction.
`characterLog_map` proves functoriality using the existing actual normalized
character-norm pullback identity.

The source convention is Mœglin–Waldspurger, *Spectral Decomposition and
Eisenstein Series* (1995), I.1.4, printed pp.5–7, especially equation (4) on
p.7: the real space is `Hom_Z(Rat(M), ℝ)` and the pairing with the log map
is the logarithm of the normalized character value. The source concerns Levi
subgroups of connected reductive groups (and finite central covers). The
present elementary construction is an internal extension to arbitrary actual
group schemes over number fields, without central covers. Its pointwise
topology is explicit; identification with a finite-dimensional Euclidean
space requires a separate finite-rank theorem.

This module does not establish character finite generation or freeness,
surjectivity or a topological quotient identification for the log map,
split-centre restriction of finite index, the actual derived split-torus
inclusion, central complement, an Iwasawa decomposition or the
well-definedness of a height extracted from Iwasawa factors. It proves
neither reduction coverage nor finite volume.
