# Original pair coefficients restricted to the actual triple CM kernels

Author: Worker 57.

This internal construction identifies the original direct and lower pair
coefficient diagrams after restriction to the actual triple common-kernel
quotients. The comparisons are identities on the complete underlying coefficient
functors. They carry the original pair lattice-inclusion maps to the corresponding
original triple maps, including all exponent reductions.

All declarations lie in
`Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`, with arithmetic carriers in
universe zero.

## Inputs and existing diagrams

The inputs are number fields `E` and `F`, with `E` totally real, `F` totally
complex and CM, an `E`-algebra structure on `F`, and
`IsQuadraticExtension E F`. The ring `A` has compatible `E`, `F` and rational
algebra structures with scalar towers `E → F → A`, `ℚ → E → A` and
`ℚ → F → A`. Fix `n : ℕ`,
`D : CentralSimpleUnitaryData E F A n`, and `Module.Finite ℚ A`.

The coefficient inputs are a number field `K`, a finite-dimensional `K`-module
`W`, an algebraic representation
`ρ : (D.rationalInvolution.baseChange K).AlgebraicRepresentation W`, a rational
finite place `p`, and a natural scalar `m` with `hm : m ≠ 0`. Write
`R = HarrisCoefficientIntegers K p`. The levels `U V T : SmallCMLevel D` have
actual subgroup inclusions `hVU : V.obj.subgroup ≤ U.obj.subgroup` and
`hTV : T.obj.subgroup ≤ V.obj.subgroup`. Put `hTU = hTV.trans hVU`.
No normality of `T` in either larger level is assumed.

Write `X_k` for the existing own coefficient kernel at level `X`, and write
intersections for the literal compact open subgroups. The existing direct pair,
lower pair and triple common levels have subgroups

\[
 P^U_k=T_k\cap(T\cap U_k),\qquad
 P^V_k=T_k\cap(T\cap V_k),\qquad
 L_k=(T_k\cap(T\cap U_k))\cap(T\cap V_k).
\]

Each is normal as a subgroup of `T`, by the existing coefficient-kernel results.
The source group diagram is `Q_k = T/L_k`, implemented by
`cmHarrisTripleCommonGroups`; the two target diagrams are `T/P^U_k` and
`T/P^V_k`, implemented by `cmHarrisLatticeCommonGroups` for `(U,T)` and `(V,T)`.
Here the exact quotients use `.subgroupOf T.obj.subgroup`. All diagrams are
indexed by `ℕᵒᵖ` and retain exponent zero and every original reduction arrow.

The original coefficient diagrams have modules
`Λ_T / (I ^ k.unop • ⊤)`, `Λ_V / (I ^ k.unop • ⊤)` and
`Λ_U / (I ^ k.unop • ⊤)`, where `Λ_X` is the canonical Harris lattice at
`CompactOpenLevel.inverseOpposite X.obj` and
`I = harrisCoefficientScalarIdeal K p m`. Their actions retain the original
inverse-unop convention. At `V` and `U` their actions have already been
restricted to the actual subgroup `T`. The pair and triple constructions factor
these same actions through their respective finite quotient diagrams.

## Actual natural quotient maps and composition identities

`cmHarrisTripleDirectPairGroupMap` and `cmHarrisTripleLowerPairGroupMap`
construct natural group maps from `Q` to the original direct and lower pair
group diagrams. Each component is the actual `smallCMResidualQuotientMap`
induced by `cmHarrisTripleCommonLevel_le_pair` or
`cmHarrisTripleCommonLevel_le_lowerPair`. It retains the representative in `T`.
Naturality follows by applying `smallCMResidualQuotientMap_comp` to both
routes around the exponent square. Both composites are the quotient map of the
same subgroup containment; proof irrelevance identifies its containment proofs.

For each of the two pair maps, the `own_app` theorem identifies its composite
with the pair's `cmHarrisLatticeCommonOwnGroupMap` as the original
`cmHarrisTripleOwnGroupMap`. The `original_app` theorem identifies its
composite with `cmHarrisLatticeCommonCoarseGroupMap` as
`cmHarrisTripleUpperGroupMap` for the direct pair, and as
`cmHarrisTripleMiddleGroupMap` for the lower pair. These are equalities of the
actual component monoid homomorphisms, proved by the same residual quotient
composition theorem. The corresponding `own` and `original` theorems assemble
them into equalities of natural transformations by component extensionality.

## Four identity coefficient comparisons

Let `res_d` and `res_l` denote `EquivariantDiagram.groupRestriction` along the
direct and lower pair group maps. The four definitions have directions

| Definition | Source | Target |
| --- | --- | --- |
| `cmHarrisTripleDirectPairOwnCoefficientIso` | `res_d` of the original direct pair own coefficients | triple own coefficients |
| `cmHarrisTripleDirectPairOriginalCoefficientIso` | `res_d` of the original direct pair original coefficients | triple upper coefficients |
| `cmHarrisTripleLowerPairOwnCoefficientIso` | `res_l` of the original lower pair own coefficients | triple own coefficients |
| `cmHarrisTripleLowerPairOriginalCoefficientIso` | `res_l` of the original lower pair original coefficients | triple middle coefficients |

Each applies `EquivariantDiagram.groupRestrictionCompIso` to the just-proved
component homomorphism identity and the original own or coarse coefficient
diagram. The existing pair coefficient action is the successive restriction of
that original diagram; its corresponding triple action is the direct
restriction. Their underlying functors are the same full original coefficient
functor. The helper therefore constructs mutually inverse equivariant maps
whose underlying natural transformations are both identity. Each `_hom` and
`_inv` normalization states exactly this identity of entire natural
transformations, by reflexivity. The isomorphisms retain every exponent
transition, rather than identifying only individual coefficient modules.

## Original inclusion squares

`cmHarrisTripleDirectPairCoefficientInclusion_square` states

\[
 \operatorname{res}_d(j^{\mathrm{pair}}_{T,U});\beta_d
   =\alpha_d;j^{\mathrm{triple}}_{T,U},
\]

where `α_d` and `β_d` are the homs of the direct own and original coefficient
isomorphisms. `cmHarrisTripleLowerPairCoefficientInclusion_square` gives the
same equation for `res_l`, the two lower isomorphisms and the original
`T`-to-`V` inclusion.

The pair maps are the existing `cmHarrisLatticeCommonCoefficientInclusion`;
the triple maps are the existing `cmHarrisTripleDirectCoefficientInclusion`
and `cmHarrisTripleLowerCoefficientInclusion`. Each underlying transformation
is the unchanged `cmHarrisTorsionSystemInclusion`, followed by forgetting the
`T` action. Extensionality for equivariant morphisms, the identity formulas and
the two category identity laws prove both squares. Thus these comparisons
identify the original included-vector maps and all their reductions.

## Provenance and remaining scope

This is an internal deduction from
`HarrisTaylorCMCoefficientTripleCommon`, its imported original pair and torsion
coefficient constructions, and `GroupRestrictionComparison`. The actual
intersection containments and residual quotient composition law construct the
new group maps and their compatibility. The component identities supply the
hypothesis of the identity restriction comparison; the original inclusion
transformations then give the two commuting squares. No new assertion from
external literature is made, and no desired comparison is assumed as an input.

These are changes of acting quotient for fixed original coefficient diagrams.
They do not establish injectivity or invertibility of reduced lattice
inclusions. Geometric cover changes and identification with the original pair
associated-sheaf maps require further constructions. General lattice
independence, rational adic independence, Hecke compatibility, representability,
arithmetic existence and canonical-model obligations remain in the containing
task. This focused arithmetic unit does not complete that task.
