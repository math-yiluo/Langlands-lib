# Actual rational geometric coefficient quotients

This internal adapter identifies the algebraic coefficient quotient in the
proper-target split-stage application. It does not compare orbit functors
or normalized graded pieces.

For the literal stabilizer
`H = (P_I ∩ n P_J n⁻¹).subgroupOf P_I`, define the coefficient homomorphism
`f : H → M_J` by inverse conjugation into `P_J` followed by the original
inducing projection. Let `N = ker(dI.projection).comap H.subtype`.
`map_geometricCoefficientKernel` identifies `N.map f` with the literal
source radical `S = (M_J ∩ n⁻¹ U_I n).subgroupOf M_J`, as equality of
subgroups inside the original inducing Levi.
`geometricCoefficientQuotientEquiv` identifies
`Jacquet.Coinvariants (sigma.comp f) N` with
`Jacquet.Coinvariants sigma S`. Its forward and inverse representative
formulas preserve every vector class. These are ordinary algebraic
quotients; no localized or normalized action is identified here.

For arbitrary subgroup data in a group `A`, the exported homomorphism
`geometricCoefficientProjection` composes the published
`intersectionToSecond PI PJ n⁻¹` with the canonical subgroup equality and
the original inducing projection. Its application theorem states the
literal formula `dJ.projection(n⁻¹ h n)`.

The private `kernelSourceEquiv` uses the elementary kernel criterion for a
semidirect projection. Its forward map sends `x ∈ N` to `n⁻¹ x n` in
`(P_J ∩ n⁻¹ U_I n).subgroupOf P_J`. The inverse sends `y` to `n y n⁻¹`.
The kernel criterion gives membership in `U_I`, and group cancellation
proves the inverse laws. Multiplicativity follows from the same published
conjugation homomorphism. This equivalence proves equality of its image
subgroup. Distributing subgroup images through the composition with
`dJ.projection` gives the image of the original coefficient homomorphism.
The rational `map_sourceRadical_eq` then identifies that image with `S`.

The existing `Jacquet.coinvariantsMapEquiv` transports pullback
coinvariants to image coinvariants. A private generic congruence transports
along the proved image equality, and has its own representative formula.
The composite and its inverse therefore preserve the class of each original
vector. The generic quotient transport uses no cuspidal-support theorem,
despite the location of its imported module.

`geometricCoefficientIntertwiner` pulls back an original inducing
intertwiner along `f` without changing its linear map.
`geometricCoefficientQuotientEquiv_natural` proves that the comparison
commutes with its restriction to `N` and the original map restricted to `S`.
Surjectivity of the original quotient map reduces the equation to the
class of a vector; both sides give the class of its image under the same
intertwiner. The two coefficient carriers have independent universes.

All structural maps retain the original subgroups, original projections
and inverse-conjugation convention. The rational specialization retains
the standard-cocharacter, reductive, maximal split torus, generic
cocharacter and point-normalizer comparison assumptions of the projection
module, for every normalizer point over an arbitrary field with an affine
structural morphism on `G`. Both decompositions are arbitrary decompositions
of the original standard subgroups. No minimality, Coxeter, finite-length,
intersection-decomposition or topology premise is used. The initial
coefficient homomorphism itself is defined for arbitrary group and subgroup
data with only the inducing decomposition. Coefficients use any commutative
ring `R` in an independent universe and arbitrary `R`-modules.

The proof is internal derived content. Its direct inputs are
`intersectionIn_inv_eq_geometricTarget_subgroupOf`,
`Geometric.General.intersectionToSecond`, the literal
`mem_geometricSourceIntersection` and `mem_geometricTargetIntersection`
formulas, `IsSemidirectDecomposition.projection_eq_one_iff`,
`map_sourceRadical_eq`, `Jacquet.coinvariantsMapEquiv`, its representative
formula, and quotient-map surjectivity and induced maps.

Transitively, the source-radical image uses closed stable dynamic limits,
common-torus action stability, conjugation of standard cocharacters,
the comparison with the original Levi projection and its actual section,
as documented in `RationalGeometricStabilizerProjection.md`.
The quotient input in `CuspidalSupport.GroupTransport` uses only the actual
coinvariant lifts and their surjectivity; neither its fixed-vector nor
admissibility transports are needed. The intersection transport uses
elementary subgroup equality and the actual inner automorphism. This
implemented dependency chain uses no geometric expansion, adjointness,
cuspidal support, character independence or Langlands classification,
including Aubert Proposition 3.2 or the defective original application to
Theorem 3.6. The broader imported representation modules do not supply
their target assertions.

The nested coefficient quotient from split stages still needs to be
composed with this comparison and related to the actual localized
source functor. Normalizer and section-action compatibility, smooth
realization, both Haar corrections, distinct-radical balance, compact/full
induction and the actual ordered filtration remain separate obligations.
No normalization factor is discarded here. The full rational geometric K0
expansion remains open.
