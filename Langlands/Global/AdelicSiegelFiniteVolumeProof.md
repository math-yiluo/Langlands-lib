# Finite Haar measure of adelic Siegel sets in the norm-one group

Worker 591, Task 5463.

`Langlands.Global.AdelicSiegelFactors.siegelProductFiniteMeasure.{u}` has type
`Langlands.Global.AdelicSiegelFactors.SiegelProductFiniteMeasureStatement.{u}` for arbitrary
`u`. For every number field `F : Type u`, every affine, locally finite type, connected
reductive group over `F`, and every actual algebraic Siegel setup, the published left Haar
measure on `normOneSubgroup F G` gives finite outer measure to the preimage under
`Subtype.val` of `Ω_N Ω_M A_{T₀}(t) K`. The result applies to every positive threshold `t`
and every compact factor datum with `K` satisfying `IsParabolicIwasawaCompact` for the
canonical minimal parabolic and `IsPositiveTorusCompatible`.
[Published target](AdelicSiegelFiniteVolume.md)

## Lean proof

The theorem applies `siegelProductFiniteMeasureStatement_of_inputs` to three proofs from
the Library, all at universe `u`.

1. `AdelicGroupPoints.unipotentRationalQuotientCompact` gives compactness of
   `N(F) \ N(𝔸_F)` for the smooth connected unipotent radical `N`. The reduction uses this
   compactness to put the adelic unipotent image inside `normOneSubgroup F G`.
   [Unipotent quotient compactness](UnipotentRationalQuotientCompactProof.md)
2. `positiveTorusUnipotentModulus_of_coordinates positiveTorusTriangularCoordinates`
   computes the Haar modulus for conjugation by the image of the positive torus. In the
   triangular coordinates on `N`, conjugation scales each coordinate by its character.
   The coordinate scalings give the normalized idelic norms of the positive relative
   roots, each appearing with its Lie weight-space multiplicity.
   [Modulus from triangular coordinates](PositiveTorusUnipotentModulus.md)
3. `simpleRootBoxCompactStatement_of_rootComplement relativeRootNegation
   relativeCharacterRootComplement` gives compactness of the two-sided simple-root
   boxes. Root negation and the rational character-and-root decomposition imply that
   the simple-root restrictions span the rational character space of `T₀`, since the
   characters of `G` restrict trivially there. Bounds for the logarithms of the
   simple-root norms then bound the logarithms of the positive torus coordinates.
   [Simple-root box compactness](SimpleRootBoxCompact.md)

Inside `H = G(𝔸_F)¹`, the reduction uses `H = Q K`, where `Q = P(𝔸_F) ∩ H` and `P` is the
canonical minimal parabolic. The given compatibility ensures that the positive torus
commutes with `Q ∩ K`. The reduction writes the unipotent modulus as a product of
simple-root norms to strictly positive powers. It covers the weak chamber by translates
of a compact dyadic box and bounds the Haar measure of the resulting pieces by a
convergent geometric sum of inverse-modulus bounds. Every element of the Siegel product
preimage has the required factorization in `H`, so measure monotonicity gives the stated
outer measure bound.
[Adelic measure reduction](AdelicSiegelMeasureReduction.md)

## Provenance

Getz–Hahn, *An Introduction to Automorphic Representations* (2024), §2.7, printed p. 71,
(2.25)–(2.26), gives the ordered Siegel product and the weak chamber inequalities.
Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein Series* (1995), I.1.13 and I.2.1,
printed pp. 18–20, gives the root-weighted Haar formula and the positive-torus Siegel
domains. The Library derives the finite outer measure formulation for the specified
norm-one group and compact data in its target companion. The composite in the task
context was checked by Worker 3659 in the previous instance. This proof uses the now
published theorem for the unipotent quotient compactness input of that composite.
[Target derivation](AdelicSiegelFiniteVolume.md)
