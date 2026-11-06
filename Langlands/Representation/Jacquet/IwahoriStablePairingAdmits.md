# Stable pairing from Fitting splittings or admissibility and two Iwahori contractions

Worker 480 constructs a stable evaluation pairing for an admissible smooth
complex representation `ρ` of a topological group `G`; Worker 937 extended the
`Admits` construction to smooth representations whose two compressed actions
have Fitting splittings. The inputs are the
published `D : Langlands.Jacquet.StablePairingData G` and, for every good open
subgroup `K`, the two structural predicates
`IsIwahoriContraction K D.N D.M D.Nbar D.g` and
`IsIwahoriContraction K D.Nbar D.M D.N D.g⁻¹`. The group universe and the
representation-carrier universe are independent. The same fixed `D.g` and the
same good subgroups occur in both predicates.

This is an internal composition of published results. The module imports
`StablePairingProof`, `IwahoriContractionAdmissibility`,
`CompressionSplittingDuality` and
`Smooth.Contragredient.AdmissibleDualityProof`; it makes no additional
literature claim.

`admits_of_iwahoriContractions_of_splits`, added by Worker 937, proves
`D.Admits ρ hs` for any smooth `ρ` (proof `hs` of smoothness) without
finiteness. Besides the two contraction predicates it assumes, for every good
`K`, the published `CompactCompressionSplits` for compression by `D.g` on the
`K`-fixed vectors of the smooth contragredient (`hUpperSplit`) and for
compression by `D.g⁻¹` on the `K`-fixed vectors of `ρ` (`hLowerSplit`): the
supremum of power kernels and the stable image are complementary.
`compactCompression_stableEvaluationDuality_of_splits` turns `hLowerSplit` into
`Admits.duality`. For the upper quotient,
`stableImageJacquetMap_bijective_of_splits` is applied to the smooth
contragredient, the upper predicate and `hUpperSplit`; its surjectivity is
exactly `Admits.upper_surjective`. The published
`powerKernelSup_eq_ker_of_iwahoriContraction` gives the required kernel
inclusion. The lower predicate applies the same two theorems to `ρ`, with
`D.Nbar` as the quotient subgroup, `D.g⁻¹` as the compression element and
`hLowerSplit`. These give `Admits.lower_surjective` and `Admits.lower_kernel`.
Normalization of both subgroups by `D.M` is supplied by `D.hMN` and
`D.hMNbar`.

`admits_of_iwahoriContractions` proves the existing `D.Admits ρ hρ.1` for an
admissible `ρ`. The neighborhood cofinality of `D.Good` gives a compact open
subgroup inside every open subgroup. The published
`isAdmissible_smoothContragredient_of_compact_cofinal` therefore supplies
admissibility of the actual smooth contragredient. Finite-dimensional fixed
spaces of `ρ` and of its smooth contragredient give both splittings through the
published `powerKernelSup_isCompl_stableImage`, and the previous theorem applies.
(Its original proof assembled the fields directly from finite dimensionality;
Worker 937 rerouted it through the splitting version.)

`stablePairingOfIwahoriContractions` chooses the bilinear pairing furnished by
the published `exists_isStablePairing`, using the newly proved `Admits`.
Its domain is the actual upper coinvariants of the smooth contragredient;
its values are complex linear functionals on the actual opposite coinvariants
of `ρ`. The specification theorem gives the published stable evaluation law.
The injectivity theorem applies the published `IsStablePairing.injective`.
No assertion of surjectivity onto the full algebraic dual is made.

The module retains the structural `StablePairingData` and both contraction
predicates. It does not construct them for reductive rational-point groups,
identify normalized Levi actions, prove an opposite-modulus comparison, or
prove analytic irreducibility or rational rank-one self-association. Those
remain separate obligations of the host proof.
