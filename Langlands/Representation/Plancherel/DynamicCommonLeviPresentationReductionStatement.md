# Presentation-level IV.1.1 to actual common-Levi existence

`Langlands.Plancherel.DynamicCommonLeviContinuation.DynamicCommonLeviPresentationReductionStatement`
is a closed Prop-valued, unproved target for the remaining presentation adapter.
It is an internal derived consequence sought from Waldspurger (2003), IV.1.1,
printed p.278 / PDF p.44, with the integral, compact-picture and rationality
conventions of IV.1, printed pp.276–278 / PDF pp.42–44. The registered original
is `waldspurger-2003-plancherel`. The paper does not state this Lean interface.
The imported complete source target remains
`Langlands.Plancherel.ConditionalParabolicIntertwiningStatement`.

The single analytic premise is that entire source proposition, in field
universe `u`, inducing-carrier universe `uV` and representative-carrier universe
`uW`. The latter two universes are independent of each other and of `u`.
The conclusion for every displayed structural input and every admissible
finite-length common-Levi representation is the actual
`CommonLeviContinuationExists`. There is no hypothesis asserting any source
analytic conclusion, equality of integral families or preservation of rationality.
This target does not assume a realization theorem for arbitrary presentations.

## Exact structural inputs

The field is an arbitrary nonarchimedean local field. The ambient group scheme
`G` is affine and locally of finite type, with `IsConnectedReductive G`.
All point topologies are the canonical ones. Their local compactness,
nonarchimedean group structure and Hausdorff properties are supplied by the
existing dynamic-point instances. Three cocharacters `χ`, `ψ`, `ψ'` have the
displayed equalities `Dynamic.centralizer ψ = Dynamic.centralizer χ` and
`Dynamic.centralizer ψ' = Dynamic.centralizer χ`. No characteristic, splitness,
quasisplitness or positive-rank restriction is imposed.

The target quantifies a commutative group scheme `T`, group schemes
`M`, `P`, `P'`, `Q`, `U`, `U'`, `V`, and the maps
`p : P → G`, `l : M → P`, `p' : P' → G`, `l' : M → P'`,
`a : T → M`, `n : U → P`, `n' : U' → P'`, `q : Q → G`, `v : V → Q`.
`M` is affine and locally of finite type. Both
`r : ParabolicRootPresentation p l a` and
`r' : ParabolicRootPresentation p' l' a` include their full existing
compatibility data. The Levi embeddings satisfy `l ≫ p = l' ≫ p'`;
`n`, `n'`, `v` each satisfy `LeviSubgroup.IsGeometricUnipotentRadical`.
The auxiliary opposite input is exactly
`(Dynamic.parabolic (CommGroupScheme.groupHom (-r'.splitComponentCocharacter)
≫ a ≫ l' ≫ p')).IsRepresentedBy q`, as in the source target. Thus `Q` and `V`
needed for the full-root convergence cone remain explicit.

`Realizes χ ψ p l n` and `Realizes χ ψ' p' l' n'` identify the two parabolic,
common-Levi and radical subgroup functors on every test scheme. The two mono
instances required to form the source relative Weyl group and induced form are
constructed from `r.isCompatible`; `Fintype (relativeWeylGroup r.data.i)` is an
explicit hypothesis, exactly as in the source. No arbitrary root, parameter or
representation equivalence is supplied.

The point subgroups `Ppt`, `P'pt`, `Mpt`, `Upt`, `U'pt` are the exact range
subgroups of the displayed source maps, with `Mpt = parabolicLeviPointSubgroup p l`.
The target retains source `IsSemidirectDecomposition Ppt Mpt Upt` and
`IsSemidirectDecomposition P'pt Mpt U'pt`, closedness of both parabolics and
radicals, and continuity of both semidirect projections. It displays a single
compact open `K`, compactness of `K`, and both source factorizations
`G(F) = Ppt K` and `G(F) = P'pt K`. The corresponding dynamic factorizations
are constructed in the statement through `parabolicPoints_eq` and
`subgroupHomeomorphOfEq`; they are not extra assumptions.

The source measure slots are to be instantiated with the already constructed
`presentationRadicalHaar`, `presentationIntersectionHaar` and
`presentationQuotientMeasure`, using their canonical Borel structures and
proved Haar, regularity, right-invariance and complex Weil compatibility facts.
Their forward images are exactly `radicalHaar ψ' K hK`,
`pairIntersectionHaar K hK ψ ψ'` and `pairQuotientMeasure K hK ψ ψ'`.
Consequently no freely chosen source measure or scale-comparison premise is
needed. The inducing representation for the source is the constructed
`presentationRepresentation χ ψ s A`, on the original carrier of `A`.

## Open proof obligation

The required assembly must transport admissibility and finite length of `A`
to `presentationRepresentation`, apply IV.1.1 with the displayed complete
presentations, auxiliary opposite data, point decompositions and these exact
measures, and transport its squared-modulus conclusion to the actual dynamic
decompositions. These are obligations of the target, not additional hypotheses.

It must compare the actual scalar weak integrands on every ambient group
argument through `unramifiedInductionComparison`, the induced quotient map and
the exact measure pushforward identities. Use the common Levi embedding equality to identify the target presentation’s
point Levi with `Mpt` when applying its comparison map. This must yield transport of the
full standard-integral domain and the actual ambient intertwiner, retaining the
original inducing carrier. The proved compact restriction squares must then
identify the resulting compact operators on both sides. The structural module
proves those squares and measure identities; it does not yet prove this integral
and domain assembly.

For the rational start, IV.1.1 supplies a nonempty open full-root cone `C R`,
full convergence on its twist-orbit saturation and whole-operator rationality
on that saturation. Restrict to `C R` and pull it back along the constructed
`characterComparison`. Prove the resulting canonical region is nonempty and
open and lies in `pairFullDomainRegion`. Transport rationality through
`regularFunctionsComparison`, the proved polynomial/rational reparameterization
laws and the two fixed compact-section maps. The rationality denominator is
chosen before the input vector and must remain nonzero on exactly this restricted
starting region. Finally use the existing `pairContinuation` constructor there.
The full rational-character norm family is `normCharacters χ`, with
`parameterTransport χ` to the literal common Levi; no selected root sublattice
replaces it.

The conclusion includes squared-modulus compatibility, this nonempty open
rational region inside the actual full convergence domain, and nonempty
`PairContinuation` data for the actual restricted compact integral. It asserts
neither a denominator nonzero on the entire full convergence domain nor values
at poles, maximal continuation, unitary regularity, invertibility, composition,
scalar identities or normalized tensor comparisons. The IV.1.1 analytic owner,
the general squared-modulus and geometry owners and subsequent comparison
owners retain their existing tasks. This statement isolates the remaining
adapter proof; its formulation does not claim that proof has been supplied.
