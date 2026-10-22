# Character twisting on exact virtual representations

Worker 20 constructs the scalar-character action on the published exact-relation
virtual group. The implementation reuses the actual representation twist and its
published algebra laws. It does not replace the exact quotient by a split group
or by an irreducible basis.

## Actual representations and exactness

For a field `K`, a group `G`, and a character `χ : G →* Kˣ`, the published
`FiniteRepresentation.twist χ A` retains the vector space and replaces the action
by `g ↦ χ(g) • A.representation g`. The coefficient, group, and carrier universes
are independent.

`rank_twist` is definitional because the vector space is unchanged.
`isShortExact_twist_iff` is also definitional: the published
`Langlands.twistIntertwining` retains each underlying linear map. Injectivity,
surjectivity, range, and kernel are consequently exactly the original conditions.
The three representation carriers in this equivalence may have independent
universes. No equivariant splitting is required.

`twistOneEquiv`, `twistMulEquiv`, and `twistInvEquiv` give actual invertible
intertwiners for the identity, product, and inverse-character laws. They reuse
`Langlands.twist_one`, `twist_twist`, and `twist_inv_twist` from the published
algebra-law proof, then use the reflexive representation equivalence.

For complex representations, `isContinuous_twist` reuses
`Weil.OperationClosure.continuous_twist`. The predicate is the published
continuity into the usual finite-dimensional complex endomorphism topology.
Continuity of the unit-valued character supplies continuity of the scalar
multiplier. No discrete topology on the coefficient field is introduced.

## Descent and inverse

Let `P` and `Q` be predicates on actual finite representations in one carrier
universe. `twistClassWith` accepts the explicit closure implication
`∀ A, P A → Q (FiniteRepresentation.twist χ A)`. It descends twisting to genuine
isomorphism classes using the already published `FiniteRepresentation.twistEquiv`.

`twistClassWith_isExactAdditive` applies the proved exactness equivalence and the
target quotient's exact relation. `ExactGrothendieckGroup.twist` is therefore
the actual integer-linear quotient lift. Its values on genuine classes and on
representations are proved. `degree_comp_twist` reduces equality of linear maps
to genuine class generators, then applies `rank_twist`. `degree_twist` is its
pointwise form, and `twistDegreeZero` restricts the same map to the kernels of
the degree maps.

`twist_one` and `twist_comp` prove the identity and composition laws on the
quotient. For composition, the caller supplies the appropriate closures from
`P` to `Q`, from `Q` to `R`, and from `P` to `R` for the product character.
The resulting map does not depend on how those proof terms were supplied.
Generator extensionality and the actual `twistMulEquiv` establish equality.

`twistEquivalence χ P hχ hχinv` assumes only closure of `P` under `χ` and
`χ⁻¹`. The inverse linear map is the constructed inverse-character twist.
Both inverse identities are proved on class generators using the actual
inverse-twist representation equivalences. An arbitrary `P` is not assumed
invariant under isomorphism or closed under any other operation.

`continuousTwist` specializes `P` to the published continuity predicate and
proves both closures. It is thus an unconditional automorphism for every
supplied continuous character. Inversion of continuous characters uses the
usual topological group of complex units. The acting group and carrier
universes remain independent.

## Original source and provenance

John Tate, *Number theoretic background*, Corvallis Part II (1979):

- Section 2 opening, printed page 9 / retained PDF page 18, specifies continuous
  complex representations, their isomorphism classes, and the exact-additivity
  criterion for extension to the virtual group.
- Section 2.2, printed page 10 / PDF page 19, defines the norm characters
  `ωˢ` and uses character twists of Weil representations.
- Section 3.4.5, printed page 15 / PDF page 24, uses the unramified twist
  `Vωˢ` in the local-constant formula. This module constructs its action on
  virtual representations; it does not assert that formula.

Literature ID: `tate-1979-number-theoretic-background`.
Retained original:
`/home/taskhub/central-library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part II.pdf`.
SHA-256:
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
These original pages were read directly.

The algebraic part is an explicitly derived generalization from continuous
complex Weil representations to finite-dimensional representations over any
field and any explicitly selected object families. The exactness, rank, quotient
descent, and automorphism proofs are intrinsic construction obligations, not
separately numbered theorems claimed from Tate. The continuous specialization
recovers the source's object class on a supplied topological group.

All external project imports are published constructions or proofs. This pair
is submitted with `Langlands/LocalFactor/SpectralTwist.lean` and its Markdown.
No local Weil group, reciprocity map, local constant system, self-dual measure,
or existence theorem is selected.

## Shared twist interface correction

Worker 111 extracted the four common helpers into
`Langlands.Weil.Representation.TwistProperties`, with Worker 21 supplying the
original declaration comparison and consumer validation. The original authorship
and mathematical provenance above remain unchanged. This module imports the
shared interface and retains its original import path. All four fully qualified
names in `Langlands.FiniteRepresentation` remain available: `rank_twist`,
`twistOneEquiv`, `twistMulEquiv`, and `isContinuous_twist`.

The canonical continuity call is `isContinuous_twist chi hA`, or
`isContinuous_twist chi (A := A) hA`. The former class-only spelling
`isContinuous_twist chi A hA` is replaced by one of these forms; the exact and
spectral consumers already used the canonical implicit representation argument.
The other three callable interfaces, universe parameter order, `rank_twist` simp
attribute, genuine scalar twists, and usual complex topology are preserved.
See the shared module's Markdown for the extraction and migration details.
