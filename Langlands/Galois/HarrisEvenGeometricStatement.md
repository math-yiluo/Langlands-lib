# The even-real-degree branch of the cuspidal Harris reduction

Author: Worker 773.

`HarrisEvenGeometricPowerStatement` states the endpoint of the Clozel,
Kottwitz and Hodge–Tate comparisons before multiplicity removal. It
retains the CM composite, regular algebraicity, conjugate self-duality,
square-integrable place, and rational-prime splitting of the cuspidal
Harris target. It requires rank at least two and even real degree.
For each prescribed complex embedding `e : E → ℂ`, it asks for a number
field `L` with complex embedding `ι` and `j : E → L` satisfying
`ι ∘ j = e`. It asks for a collection of actual Galois representations
over every completion of `L`, with the same positive multiplicity `a`
in the arithmetic Frobenius polynomials and in the Hodge–Tate
decomposition at the label induced by `j`. `HarrisPowerSystem` supplies
the common finite set, monic polynomial roots, purity and normalization.
`HarrisLabelledWeights` supplies the injective list of twists at every
coefficient place. The list can depend on the coefficient place.

The proposition specifies the output of the geometric construction.
The proof requires the following comparisons for the same actual
multiplicity representations.

1. **Division algebra and transfer.** A rational prime split in `K₀`
   gives a pair of conjugate places, both square-integrable by
   conjugate self-duality and transport of the local component. The
   even real degree gives the parity branch of
   `ClozelOnePlaceExistenceStatement`. Use the division algebra with
   involution, signature `(n−1,1)` at the prescribed place and definite
   signature at the others. At rank two there is a second real place,
   so the hypothesis of `HarrisSignatureCharts.reflexField_eq_distinguishedImage`
   has the second disjunct. For the induced CM type,
   `CMType.clozelReflexField_inducedFromImaginaryQuadratic` identifies
   Clozel's composite reflex field with the given copy of `E`.
   Clozel's transfer is Jacquet–Langlands to the division form, stable
   descent to the unitary group, and extension to the similitude group
   with the central character correction. The actual automorphic transfer,
   occurrence, and compatibility of the selected local factors with
   the Library's PEL tower are obligations of this branch.
2. **Multiplicity and arithmetic polynomials.** Apply
   `CMHarrisKottwitzLambdaAdicStatement` to the actual
   `cmHarrisLambdaHeckeMultiplicityObjects`. The comparison needs occurrence
   and concentration in middle degree, so the multiplicity used here is
   the common positive absolute value of Kottwitz's integer. The pure
   polynomial of that degree, its rationality over a common field and
   its comparison with the normalized unramified `GL(n)` polynomial
   are part of the input. The character twist in Clozel's §5 changes
   the weight to `n−1`. In the CM case it can be algebraic of nonzero
   weight. The characteristic polynomials of the cohomological spaces
   are actual powers, and the monic root can be recovered over the
   same characteristic-zero coefficient field by its successive
   coefficients. This needs the geometric-model, fixed-vector and
   canonical-model comparisons retained in the published PEL statements.
3. **Labelled Hodge–Tate comparison.** The published
   `CMHarrisLambdaCohomologyHodgeTateStatement` concerns the underlying
   space of finite-level cohomology. The geometric coefficient
   construction makes this theorem applicable, but the regularity
   assertion here additionally needs the coefficient-equivariant
   comparison at the selected label and the middle-degree Hecke
   multiplicity calculation. Cohomological archimedean descent and the
   regular algebraic weights give the distinct graded pieces, one for
   each highest-weight entry with its shift. Occurrence and the comparison
   of the Hecke multiplicity give dimension `a` in each piece. Embedding
   `E` into `L` realizes the chosen label at each completion. The
   comparison is required at every coefficient place of this one family.

`Clozel1991Theorem57Statement` supplies a published version of the
Frobenius-power conclusion on the reflex field for `n ≥ 3`. The endpoint
here also needs rank two and the labelled comparison for the same
collection. The published `Clozel1993Theorem26Statement` and
`CMHarrisTheorem57Statement` use supercuspidality in their respective
routes. The even-degree branch can use the square-integrable hypothesis
above without their extra hypotheses.

`HarrisEvenNormalizedExistenceStatement` is the corresponding output
with power one and semisimple representations. It keeps the specified
complex embedding and the labelled regularity at all coefficient
places, as needed for common-field quadratic patching.
`HarrisEvenMultiplicityReductionStatement` is the implication from the
geometric power endpoint, `TaylorLabelledMultiplicityRemovalStatement`
and `RegularHodgeTateCoefficientDescentStatement`. Its proof applies
the local statements at each coefficient place. The all-element power
identity gives rational trace by division by `a`. The scalar model
has the original unramified matching and the prescribed purity through
the same Frobenius polynomials. All three declarations are unproved
statements, and the even-degree output is stronger than the final
sum-of-pure-families conclusion.

## Sources

- L. Clozel, *Représentations galoisiennes associées aux représentations
  automorphes autoduales de GL(n)*, 1991, Proposition 2.3 and prescribed-place
  remark, pp. 105–106, Proposition 4.11, pp. 129–130, and §5.2–5.3,
  pp. 133–144, especially Theorem 5.7, p. 142, and the central and weight
  correction in its proof. Registered `clozel-1991-selfdual-galois`,
  SHA256 `9de7c13c9ae108e481de170327a06e44845cf87a6aabc1d5600176ee695e91ac`.
- R. Kottwitz, *On the λ-adic representations associated to some simple
  Shimura varieties*, 1992, Theorem 1, p. 657, and purity in §5, p. 661.
  Registered `kottwitz-1992-lambda-adic-simple-shimura`, SHA256
  `749af5541a59187e6f9d1089dec9a0e591a2059173da739c7384ff3a7d0dd799`.
- M. Harris, *Supercuspidal representations in the cohomology of Drinfel'd
  upper half spaces*, 1997, §3, pp. 100, 102–103, and §4, p. 104.
  Registered `harris-1997-drinfeld-cohomology`, SHA256
  `aea284b917442459028b710dbfd9ae537631490504f3bc6d54a1e76ee697e0d9`.
- M. Harris, *Galois properties of cohomological automorphic forms on
  GL(n)*, 1999, proof of Theorem 5.7(i), pp. 313–314, for the geometric
  origin of the coefficients via the universal abelian scheme. Registered
  `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA256
  `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.
- G. Faltings, *p-adic Hodge theory*, 1988, Chapter III, Theorem 4.1,
  p. 298, for the underlying cohomological Hodge–Tate comparison.
  Registered
  `provided-1991b7d5032d5fe94ca932ccbeccf293bafd80aa29a350ed2fda545cf46b9440`,
  SHA256 `2eb8b02f9e3e7662e1e79229488ee7e98240e23f221f1c9aaa7bec79cf329024`.
- M. Harris and R. Taylor, *The Geometry and Cohomology of Some Simple
  Shimura Varieties*, 2001, VII.1.9, pp. 227–228, for the even-degree
  construction with specified archimedean embedding and its regular
  graded pieces. Registered
  `harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA256
  `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
