# Corrected actual support filtrations

Author: Worker 194.

This internal prerequisite constructs corrected support subfunctors of actual
normalized induction and their actual images in normalized Jacquet modules.
It constructs the resulting finite filtration for a supplied increasing
empty-to-full chain of Weyl subsets and the natural comparison of two
successive image quotients. The p-adic field and supplied topology are arbitrary;
the field and coefficient universes remain independent. No positive-rank
restriction is imposed.

The module first proves two general facts about an actual group `G`, subgroups
`P,Q` and a subset `U` invariant under left `P` and right `Q`.
A left coset of `P` belongs to the image of `U` exactly when any chosen
representative belongs to `U`: equality of quotient representatives gives a
left factor in `P`, to which invariance applies. Right multiplication by `Q`
preserves that quotient image. Both facts use the Library's actual
`Induction.LeftQuotient` and `quotientRight`, with their existing conventions.

Over a field, `correctedQuotientSupport F B C θ` is the image of
`bruhatSupport F (weylSupport B C θ)` in the left quotient by `P_B`.
The imported matrix-core theorem proves that this actual group support is
invariant under left `P_B` and right `P_C`. Thus its quotient image is
well defined on left cosets and preserved by the actual right `P_C` action.
Its inverse image under the quotient map is exactly the stated matrix
support. It is monotone in `θ`; the empty and full Weyl supports give the
empty and full quotient supports. These assertions include rank zero.

For a supplied p-adic field topology,
`correctedInductionSupport T B C θ` is an actual `RepSubfunctor` of
normalized parabolic induction from `B`, restricted to `P_C`.
It reuses `Geometric.rawSmoothSupportSubfunctor` with the actual quotient
support above, then precomposes with `B.inducingFunctor` for the existing
positive half-modulus character. The objects are the existing smooth
induced functions; covariance, normalization and right translation are
unchanged. Subfunctor naturality follows from the existing pointwise
induced-map construction, and right-parabolic stability uses the proved
right invariance of the support.

`mem_correctedInductionSupport_iff` makes the condition explicit:
every point where the actual induced function is nonzero lies in
`bruhatSupport F.Carrier (weylSupport B C θ)`.
Monotonicity is inherited from support containment. An empty support
forces the actual function to vanish at every point, and the full
support imposes no condition; this proves the zero and full endpoints.
These support subspaces are parabolic stable, not asserted to be
subrepresentations for the full general linear group.

`correctedJacquetSupport T B C θ` applies the existing
`Geometric.parabolicJacquetImageSubfunctor` to this support subfunctor.
It therefore consists of the actual classes of those supported functions
under `C.jacquetMk` in normalized Jacquet restriction.
`mem_correctedJacquetSupport_iff` states precisely the existence of such
a representative, with the nonzero-value support condition explicit.
It is an image construction, not a new abstract filtration object.
`correctedJacquetSupport_eq_of_core_eq` proves that equal Weyl cores
give equal actual image subfunctors.
The image construction preserves the support monotonicity and its
zero/full endpoints, using the existing actual quotient surjectivity
for the full endpoint.

For `θ ⊆ η`, `correctedSupportQuotientIso` is a natural isomorphism from
the quotient of the two actual corrected Jacquet images to normalized
coinvariants of the actual induction support quotient.
It instantiates the published `Geometric.supportImageQuotientIso`;
the needed inclusion of support subfunctors is proved here.
The imported theorem uses smooth normalized coinvariant exactness and
actual quotient maps. This specialization assumes no splitting and
introduces no independent graded-representation identification.

`correctedJacquetFiltration` takes a family of Weyl subsets indexed by
`Fin (m+1)`, with explicit monotonicity, empty initial support and full
final support. Its steps are the actual corrected Jacquet image
subfunctors above. The proved monotonicity and endpoints satisfy every
field of the existing `RepFunctorFiltration`.
The construction does not choose such a chain or prove openness of
any of its supports.

The provenance is internal: the definitions compose the existing actual
support, normalized induction and quotient-image constructions with the
proved Weyl-to-matrix core correspondence. Their elementary containment
and endpoint proofs are implemented directly, and the quotient comparison
reuses the published actual exactness theorem.
This module does not identify images from an alternative uncorrected
support definition, select a length-compatible open Bruhat chain, prove
cross-parabolic preservation by Aubert transition maps, identify a
nonzero stratum or its coefficient, compare orbital integrals or
exterior signs, reflect Jacquet exactness to full-group exactness, or
prove signed effectivity. Those remain obligations for the actual
duality complex.
