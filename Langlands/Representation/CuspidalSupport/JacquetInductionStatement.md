# Jacquet modules of quasicuspidal induction

Author: Worker 14. These proposition definitions specialize Bernstein and
Zelevinsky (1977), corollary 2.13, to actual general linear groups over finite
extensions of p-adic fields. They state all three consequences and the Weyl
coset parametrization used in part (c). They do not assert proofs or supply
any of the conclusions as input data.

The aggregate `PadicQuasicuspidalJacquetTheorems` quantifies every prime,
every finite p-adic extension, every compatible topological realization,
and every positive rank. Both Levis are the actual products attached to
positive ordered block shapes. The inducing representation is any complex
smooth quasicuspidal representation in the specified universe. Neither
irreducibility nor admissibility nor finite length is assumed.

The normalized functors are the published
`T.normalizedParabolicInductionFunctor B` and
`T.normalizedJacquetFunctor C`. Induction uses covariant functions with
right translation and the canonical positive half-modulus; Jacquet uses
the actual unipotent coinvariant quotient with the inverse half-modulus.
The resulting smooth carrier has universe `max uF uV`.

- `MinimalConjugatingCosetsTheorem` asserts that each actual permutation w
  conjugating the whole source Levi onto the target has exactly one minimal
  conjugating representative v with w = v b for a source block-Weyl element
  b. The explicit equation expresses the quotient by the source Weyl group
  acting on the right. Uniqueness concerns v; it does not introduce a
  chosen representative as an assumption. This is the coset identification
  in the proof of corollary 2.13(c).
- `QuasicuspidalJacquetVanishingTheorem` says that the resulting Jacquet
  module is zero if the target Levi has no standard subgroup associated to
  the source Levi. Such a standard subgroup is expressed as an actual
  block refinement of the target, embedded in GL_n. Association here is
  equality of that subgroup with the conjugated embedded source Levi.
  `Subsingleton` of the actual quotient carrier expresses the zero module.
- `NonassociatedJacquetSubquotientsTheorem` says that, when the two Levis
  are not associated, every quasicuspidal smooth subquotient of the result
  is zero. The published subquotient predicate uses actual invariant
  subspaces, quotients, and isomorphisms; it does not merely label possible
  constituents. It quantifies carriers in the resulting quotient universe,
  which contains all subspaces and quotients of this representation.
- `AssociatedJacquetFiltrationTheorem` says that for associated Levis the
  result is quasicuspidal and admits a finite zero-to-full filtration by
  actual invariant subspaces. A bijection of its step indices with all
  minimal conjugating permutations requires one factor per representative.
  Each successive quotient is equivalent to the corresponding actual
  Weyl-transported inducing representation. Representation equivalences
  allow the quotient and original carrier universes to differ. No direct
  sum decomposition, splitting, simplicity of the factors, or preferred
  ordering is asserted. Zero factors are permitted for the zero input.

## Original source and specialization

Bernstein and Zelevinsky, *Induced representations of reductive p-adic groups
I* (1977), sections 2.1–2.4, printed pages 446–447 (PDF pages 7–8), and
sections 2.11–2.13, printed pages 448–449 (PDF pages 9–10).
Literature ID: `bernstein-zelevinsky-1977-induced-i`.
Original PDF SHA-256:
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The original passages were read directly; the retained page text was read
again on 2026-10-20.

Section 2.2 identifies standard subgroups inside a GL product with ordered
block refinements. Section 2.4 defines quasicuspidality by vanishing proper
Jacquet modules. The actual raw and normalized Jacquet quotient carriers
are identical, so the published raw-coinvariant vanishing predicate retains
that condition. Parts (a), (b), and (c) of corollary 2.13 give the three
representation assertions. Its proof identifies the minimal conjugating
permutations with W(M,N) modulo the source Weyl group on the right. The
statement uses that concrete finite subtype, with the identification kept
as an explicit separate theorem target. The source's gluing of individual
representations is encoded by a finite object filtration with an arbitrary
enumeration of its factors; no functorial strengthening is claimed here.

These statements restrict the general reductive and nonarchimedean field
setting to GL_n and finite p-adic extensions. Their proofs depend on the
normalized geometric lemma, quasicuspidal structure, and the proper-induction
assertion 2.4(d). Those remain separate proof obligations. In particular,
compilation of this pair proves none of these source theorems.
