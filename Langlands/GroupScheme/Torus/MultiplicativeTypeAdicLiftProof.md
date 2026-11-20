# Adic lifting for homomorphisms from isotrivial groups of multiplicative type

`Langlands.GroupScheme.multiplicativeTypeAdicLift` proves
`MultiplicativeTypeAdicLiftStatement.{u}` in every universe. Let `A` be
noetherian and `I`-adically complete and separated. The source `H` becomes
diagonalizable over a finite étale surjective cover of `Spec A`, and the
target `G` is smooth and affine over `Spec A`. Every homomorphism over
`Spec (A/I)` lifts to `Spec A`. Two lifts of the same homomorphism are
conjugate by a point of `G` reducing to the identity modulo `I`.
[Target statement](MultiplicativeTypeAdicLiftStatement.md)

The proof obtains infinitesimal lifting from
`HomScheme.multiplicativeTypeInfinitesimalLift_of_cohomology`. It supplies the
published degree-one and degree-two cohomology vanishing theorem, the
square-zero deformation theorem, and flatness and affineness of
multiplicative-type groups. Over an affine square-zero thickening the geometry
applies to the source over the thickening and the vanishing to its reduction.
The square-zero theorem uses this vanishing to correct a scheme-map lift to
a homomorphism and to correct a lifted conjugating point. The infinitesimal
reduction iterates the resulting lifting property over nilpotent thickenings.
[Infinitesimal reduction](../HomScheme/InfinitesimalCohomologyReduction.md) ·
[Square-zero deformation](../HomScheme/SquareZeroCohomology.md)

The proof then applies
`multiplicativeTypeAdicLift_of_infinitesimal_of_homComparison` with
`multiplicativeTypeAdicHomComparison`. The adic reduction views the splitting
cover as an fppf cover to obtain the multiplicative-type hypothesis. It
recursively lifts the prescribed homomorphism through the quotients
`A/I^(n+1)` and uses surjectivity of Hom restriction to algebraize the
compatible system. For two lifts it starts with the identity at level zero
and recursively lifts and corrects the conjugators. Affineness and adic
completeness give a global point from these compatible conjugators.
Injectivity of Hom restriction identifies the conjugated homomorphism with
the second lift. The equality `I^(0+1) = I` identifies level zero with the
quotient in the target statement.
[Adic reduction](MultiplicativeTypeAdicLiftReduction.md) ·
[Adic Hom comparison](MultiplicativeTypeAdicHomComparisonProof.md)

The adic construction follows SGA 3, Exposé IX, Corollaire 7.3 in the
Gille–Polo recomposed edition, 2009, p. 59 (original margin p. 72), using
Théorème 7.1 for Hom comparison and the infinitesimal lifting furnished by
Théorème 3.6. The registered source is `sga3-expose-ix-gille-polo-2009`,
SHA-256 `7c1e3d5b9d01ad01d0dd7b8b62045d012052e7890fb37adc3e7934ebb5fd6fc3`.
