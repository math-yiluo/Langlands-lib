# Stable pairing from admissibility and two Iwahori contractions

Worker 480 constructs a stable evaluation pairing for an admissible smooth
complex representation `ρ` of a topological group `G`. The inputs are the
published `D : Langlands.Jacquet.StablePairingData G` and, for every good open
subgroup `K`, the two structural predicates
`IsIwahoriContraction K D.N D.M D.Nbar D.g` and
`IsIwahoriContraction K D.Nbar D.M D.N D.g⁻¹`. The group universe and the
representation-carrier universe are independent. The same fixed `D.g` and the
same good subgroups occur in both predicates.

This is an internal composition of published results. The module imports
`StablePairingProof`, `IwahoriContractionAdmissibility`, and
`Smooth.Contragredient.AdmissibleDualityProof`; it makes no additional
literature claim.

`admits_of_iwahoriContractions` proves the existing `D.Admits ρ hρ.1`.
The neighborhood cofinality of `D.Good` gives a compact open subgroup inside
every open subgroup. The published
`isAdmissible_smoothContragredient_of_compact_cofinal` therefore supplies
admissibility of the actual smooth contragredient. Admissibility of `ρ` supplies
the finite-dimensional fixed spaces required by `Admits.finite`.

For the upper quotient, the published
`stableImageJacquetMap_bijective_of_iwahoriContraction` is applied to the smooth
contragredient and the upper predicate. Its surjectivity is exactly
`Admits.upper_surjective`. The corresponding published
`powerKernelSup_eq_ker_of_iwahoriContraction` gives the required kernel
inclusion. The lower predicate applies the same two theorems to `ρ`, with
`D.Nbar` as the quotient subgroup and `D.g⁻¹` as the compression element.
These give `Admits.lower_surjective` and `Admits.lower_kernel`. Normalization
of both subgroups by `D.M` is supplied by `D.hMN` and `D.hMNbar`.

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
