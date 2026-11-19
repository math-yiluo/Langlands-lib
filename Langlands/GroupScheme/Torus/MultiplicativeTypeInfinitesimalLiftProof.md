# Infinitesimal lifting of homomorphisms from groups of multiplicative type

`Langlands.GroupScheme.multiplicativeTypeInfinitesimalLift` proves
`MultiplicativeTypeInfinitesimalLiftStatement.{u}` in every universe. If `J` is a
nilpotent ideal of a commutative ring `A`, `H` is a group scheme of multiplicative
type over `Spec A`, and `G` is smooth over `Spec A`, every homomorphism
`H_{A/J} → G_{A/J}` lifts over `A`. Two homomorphisms with equal reductions are
conjugate by a section of `G` over `Spec A` whose restriction to `Spec (A/J)` is
the identity. [Published statement](MultiplicativeTypeInfinitesimalLiftStatement.md)

The Lean proof applies `multiplicativeTypeInfinitesimalLift_of_cohomology`. It
uses `IsMultiplicativeType.flat` and `IsMultiplicativeType.isAffineHom` for the
source over the affine test and `multiplicativeTypeLowDegreeVanishing` for its
pullback to the square-zero quotient. The vanishing proof uses split averaging
to obtain range membership for each scalar-extended differential. Flat descent
gives range membership over the base, which produces the regular coboundaries.
[Assembly](../HomScheme/InfinitesimalCohomologyReduction.md),
[source geometry](RelativeMultiplicativeTypeGeometry.md),
[vanishing](../Cohomology/MultiplicativeTypeVanishingProof.md)

`squareZeroHomomorphismCohomology` corrects an initial scheme-map lift by a
kernel-valued cochain. It lifts prescribed conjugators using smoothness and
correction by a kernel point. The nilpotent induction factors a quotient by
`I` through the quotient by `I²`, where the image of `I` is square-zero, and
applies the induction hypothesis to `I²`. Specializing the resulting relative
lifting property to the identity test of `Spec A` gives the homomorphism lifts
and lifts the identity conjugator when the reductions agree.
[Square-zero deformation](../HomScheme/SquareZeroCohomology.md),
[nilpotent induction](../HomScheme/InfinitesimalReduction.md)

This is the finite-type case of Théorème 3.6 in SGA 3, Exposé IX, including
the conjugacy conclusion it draws from Corollaire 3.3 in the Gille–Polo
recomposed edition, pp. 38–39. The square-zero argument corresponds to
Conrad, *Reductive group schemes* (2014), Remark B.2.4 and Corollary B.2.6,
pp. 285–287.
[Source references and scope](MultiplicativeTypeInfinitesimalLiftStatement.md)
