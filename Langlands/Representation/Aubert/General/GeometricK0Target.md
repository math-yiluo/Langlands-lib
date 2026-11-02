# Actual normalized intersection terms and the general geometric-lemma K0 target

Author: Worker 165, task `e3d69272-2599-4a08-a934-cb11f2493e30`.
The normalized functors and exact-K0 mechanisms are the separately authored
Worker 23 adapters and the published generic smooth-representation library.
The filtration and actual orbit-functor work remains with Worker 14 and the
existing Renard geometric-lemma owners.

This module constructs the actual normalized intersection terms and declares
`Langlands.Aubert.General.GeometricK0ExpansionStatement`, the separate Prop
target for Aubert 1995, identity (1.3), printed p.2181 / PDF p.3.
It proves neither that identity nor a connected-reductive instance of the
intersection-decomposition or finite-length prerequisites.

## Actual intersections and transport

For actual subgroups `A`, `B` and an ambient element `n`, the definitions are
`geometricSourceIntersection A B n = B ∩ n⁻¹ A n` and
`geometricTargetIntersection A B n = A ∩ n B n⁻¹`, using literal subgroup
intersection and images under `MulAut.conj`. These are not subgroup labels.
`geometricIntersectionMembership` proves that inverse conjugation
`x ↦ n⁻¹ x n` identifies membership in the target with membership in the
source. The proof expands subgroup-image membership using the inverse of
the conjugation equivalence, cancels inverse factors and interchanges the
two conjunctions. In a topological group `isClosed_map_conj` expresses
the conjugate subgroup as the preimage under that continuous map; the two
intersection closedness lemmas then use closedness of both factors.

Fix standard subsets `I`, `J` and a minimum double-coset representative
`w ∈ D(I,J)` with an actual normalizer lift `n`. The six subgroups used
by the term are the following actual intersections in the same ambient group:

| Role | Source inside `M J` | Target inside `M I` |
| --- | --- | --- |
| Levi | `M J ∩ n⁻¹ (M I) n` | `M I ∩ n (M J) n⁻¹` |
| Parabolic | `M J ∩ n⁻¹ (P I) n` | `M I ∩ n (P J) n⁻¹` |
| Radical | `M J ∩ n⁻¹ (U I) n` | `M I ∩ n (U J) n⁻¹` |

`GeometricSourceDecomposition` and `GeometricTargetDecomposition` name
the semidirect decompositions of these exact parabolics into these exact
Levis and radicals, using their `subgroupOf` copies inside the indicated
ambient Levi. They do not supply arbitrary replacement subgroups.
`GeometricIntersectionDecompositions` is the separate realization
proposition requiring both decompositions for every minimum representative
and every lift. Its truth remains required at the actual connected-reductive
specialization. The parameter used to form the K0 target is a proof of
this named proposition, not an assumed geometric-lemma class equation.

## Actual functors and exact maps

The ambient group is locally compact and nonarchimedean; all `M I` and
`U I` are closed. Their actual intersections above therefore have the
closedness needed by the normalized functors. The definitions in namespace
`Langlands.Aubert.General` are:

- `geometricSourceJacquetFunctor`: Worker 23's
  `leviNormalizedJacquetFunctor` for the actual source intersection parabolic
  inside `M J`. Its target is the smooth category of the source intersection
  Levi, identified with its `subgroupOf` copy by the actual continuous
  equivalence. Its action is the actual coinvariant action with the inverse
  half Haar-modulus twist.
- `geometricTargetInductionFunctor`: `leviNormalizedInductionFunctor` from
  the actual target intersection Levi to `M I`, using the actual target
  intersection parabolic. It inflates along its actual Levi projection,
  twists by the positive half Haar modulus and takes smooth induction.
- `geometricTermFunctor`: the composite of that source Jacquet functor,
  `conjugationFunctor n (geometricIntersectionMembership ..)` and that
  target induction functor, on the full smooth categories with saturated
  carrier universe `max uG uV`.
- `GeometricTermFiniteLength`: four visible representation-theoretic
  prerequisites, finite-length preservation and preservation of finite-length
  short exact sequences for the source Jacquet and target induction functors.
  Conjugation transport is an actual continuous-equivalence pullback; its
  preservation properties are already published.
- `geometricTermK0`: the actual integer-linear maps of those two restricted
  functors, through `FiniteLengthGrothendieckGroup.map`, composed with the
  actual `conjugationK0`.
- `geometricTerm_hasFiniteLength` derives finite length of the actual
  composite by source Jacquet preservation, the published equivalence
  pullback preservation theorem, and target induction preservation.
- `geometricTermK0_ofRepresentation` proves the actual-class formula:
  `[A]` maps to the class of `geometricTermFunctor.obj A`, with the preceding
  derived length witness. The proof applies the generic map generator
  formula to the source Jacquet functor, then the conjugation generator
  formula and then the target induction generator formula. It proves no
  geometric expansion.

The source-to-target subgroup map is forward conjugation by `n`.
The representation transport is the inverse pullback, with action
`σ(n⁻¹ x n)` on the target intersection Levi. No free term endomorphism,
unrelated graded label or field equal to the desired expansion is used.

## Exact expansion and proof boundary

`GeometricK0ExpansionStatement` states the equality of integer-linear maps

`r_I ∘ i_J = ∑_(w ∈ D(I,J)) i_(target,w) ∘ Ad(n_w) ∘ r_(source,w)`.

The left side uses `jacquetK0` and `inductionK0` of the same actual ambient
families. Their named `ParabolicFiniteLength` premises are explicit.
The right side sums `geometricTermK0` over the actual finite subtype of
minimum representatives. The Weyl group is the actual
`N_G(T)/Z_G(T)`, with full-centralizer denominator, a supplied finite
enumeration and a Coxeter system on that quotient. Every section of the
normalizer quotient is quantified. Such sections are available by choice
from quotient surjectivity; no assertion of the expansion or of elementwise
lift independence follows merely from supplying one.

The finite simple-root type can be empty. No field, splitness, quasisplitness,
characteristic-zero or positive-rank restriction is introduced by this
generic actual-subgroup target. Identifying the supplied families, torus,
quotient, Coxeter indexing and minimum representatives with the standard
ones of the connected reductive rational-point group remains required.
The subgroup-level construction does not prove the relative-root comparison.

The intended proof must specialize the existing actual geometric filtration
and apply the published
`SmoothRep.filtrationGrothendieckStatement`, which obtains the exact class
sum from actual smooth gluing and finite length of the total functor.
The missing work is that specialization and the graded-piece comparisons,
not another abstract additivity theorem. In Worker 14's general orbit
convention the term is represented by `P_J * w⁻¹` on `P_J \ G / P_I`;
the inversion comparison with `W_I \ W / W_J` is a separate obligation.
The actual orbit functor has two Haar correction twists. Proving its
identification with the normalized intersection composite requires both
corrections, parabolic modulus and half-modulus comparisons, a smooth
realization, and any required compact-induction/full-induction comparison.
Setting input characters to one does not discard these corrections.

All finite-length, exactness, filtration, smoothness and normalized
graded-piece comparison assertions are representation-theoretic work.
They are outside the parent's finite external Chapter V structural boundary.
The standing explicit pause on the upstream ClosedSemidirect task is
unchanged; this target neither resumes it nor claims an accepted interface
from its private draft. No proof of the geometric lemma or assertion of
classification independence is made here; a future proof must record
its actual declaration-level dependencies.

Source: registered original `aubert-1995-duality`, SHA256
`57af9c46769f6edd8e142ddaf465e89acfa2f2147db222d26879a28a06df9693`,
printed p.2180 / PDF p.2 for double-coset and inverse-conjugation conventions,
identity (1.3) and the following standard-Levi remark on printed p.2181 /
PDF p.3. Aubert cites BZ Lemma 2.11(b) there. The elementary intersection,
closedness and continuous-transport constructions are internal encodings
of those actual subgroups; they are not additional source theorems.
