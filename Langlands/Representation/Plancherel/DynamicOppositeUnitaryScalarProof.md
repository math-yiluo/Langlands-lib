# Full-unitary regularity and nonnegativity of the actual opposite scalar

`Langlands.Plancherel.conditionalDynamicOppositeUnitaryScalar` proves
`ConditionalDynamicOppositeUnitaryScalarStatement.{u,uV}`. It applies over
any nonarchimedean local field and connected reductive group in the
statement, with independent field and representation-carrier universes.
The proof uses the original forward and reverse continuations and their
convergence regions, the supplied irreducibility locus and the
square-integrability data modulo the supplied central subgroup. It uses the
canonical scalar \(j_P\) for the original \(K\)-normalized radical measures.

## Gallery factors

The supplied irreducibility locus gives irreducibility of the coefficient
representation. Square integrability supplies admissibility. Choose a
split component of the actual common Levi and pull back the coefficient
along `parameterHomeomorph`.

For a rank-one wall, `DynamicCommonLeviIrreducibility.hasOpenIrreducibilityLocus`
applies square integrability to obtain an irreducible twist at the source
vertex. `representedDynamicInductionEquiv` and `intrinsicGalleryCoefficient_twist`
identify the corresponding represented induction. The openness theorem for
the represented family gives a nonzero principal open, which
`exists_galleryRegularIrreduciblePrincipalOpen` intersects with regularity in
both orders. On this open Schur's lemma gives the scalar of the represented
composite. `hasGenericRankOneGalleryFactorCoordinates_of_wall` uses induction
in stages through the wall Levi to preserve the scalar under complement
translations of the valuation lattice. The maximal proper parabolic in
that Levi leaves at most one coordinate outside the complement. For a
same-chamber step, `hasGenericRankOneGalleryFactorCoordinates_of_sameChamber`
uses distance-additive composition and the identity operator at a repeated
vertex to give a constant factor.

## Comparison with the canonical rational function

`hasDenseRankOneProduct_of_oppositeGallery` uses a finite distance-additive
gallery from the original cocharacter to its opposite. It intersects the
edge opens with simultaneous represented `PQ` regularity and multiplies the
edge scalars at their fixed Haar scales. The represented endpoint comparison
uses compact tests to identify the endpoint operators with the given
continuations. On the intersection with common continuation regularity and
the nonzero locus of the canonical numerator, equality of the scalar
actions on a nonzero induced vector identifies the product with the
canonical rational function. Common-regular positivity with the original
square-integrability data gives \(j_P \ne 0\).

## Regularity and values on the unitary locus

`conditionalDynamicOppositeUnitaryScalar_of_denseRankOneProduct` inverts the
pointwise product. Successive rational multiplicative differences cancel
one translation-invariant factor at each step. The resulting identities
force every prime divisor of a reduced denominator to be associated to a
linear factor in one valuation coordinate. The existing inverse norm
bound on a dense subset of the unitary locus excludes any such factor
that vanishes at a unitary parameter. The reduced denominator therefore
witnesses algebraic regularity at every unitary parameter. Continuity
extends the nonnegative real values from the dense common regular unitary
locus, including to points where the chosen continuations have poles.

## Source and axioms

The gallery composition, wall descent and scalar product correspond to
Waldspurger, *La formule de Plancherel pour les groupes p-adiques (d'après
Harish-Chandra)*, 2003, IV.1 (12), (14) and IV.3 (4)–(6). The conclusion on
the inverse is the regularity and nonnegativity part of V.2.1, where the
Plancherel density is \(j^{-1}\) times a positive measure constant. The Lean
proof uses the algebraic argument with multiplicative differences described
above. The registered source is `waldspurger-2003-plancherel`, PDF SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.

The theorem uses `propext`, `Classical.choice` and `Quot.sound`.
