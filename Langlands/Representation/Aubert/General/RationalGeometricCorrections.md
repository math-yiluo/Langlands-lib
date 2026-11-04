# Original epsilon corrections for the actual rational compact comparison

This internal construction by Worker 184 specializes both original Haar
correction characters to the actual rational-point parabolic families. It also
identifies the target correction with the canonical half of the compact
integral character already constructed in `RationalGeometricCompactHaar`.

Write `A = G(k)`, `P_I`, `M_I`, `U_I` and `P_J`, `M_J`, `U_J` for the
original parabolics, Levis and radicals, and let `n` be the given actual point
normalizing the torus. The domain of both characters is the literal subgroup

`L_t = (M_I intersect n M_J n⁻¹).subgroupOf M_I`.

The whole target intersection parabolic is
`K = (M_I intersect n P_J n⁻¹).subgroupOf M_I`.
These are the published `geometricTargetIntersection` subgroups with their
original induced topologies. The construction permits an arbitrary field and
affine group scheme under the displayed hypotheses; it does not impose a new
representation-universe restriction or a choice of normalizer section.

## Actual transports and both characters

`geometricCommonLeviInclusion` is the generic inclusion induced by
`M_J ≤ P_J`. Its rational specialization `geometricCommonLeviInTarget` uses
`dJ.levi_le`. Both application lemmas state that the ambient group element is
unchanged. The generic helper avoids reducing the large scheme-point group
when checking the application identity.

`geometricEpsilonOne` specializes
`geometricSourceCorrectionCharacter` with the original data
`(M_J, M_I, U_J, P_I, n)`. Its transport to `L_t` acts by `x ↦ n⁻¹ x n`.
`geometricEpsilonTwo` specializes `geometricTargetCorrectionCharacter` with
`(M_I, M_J, U_I, P_J, n⁻¹)`. Its transport is the original subgroup-equality
transport and preserves the point. Both characters retain the original positive
radical half times the inverse correction-subgroup half. The semidirect
decompositions supply radical normalization; their Levi containments followed
by each parabolic's self-normalization supply the other normalizer premises.

The source correction uses closedness of `U_J` and `P_I`; the target correction
uses closedness of `U_I` and `P_J`. The character definitions assume a locally
compact topological ambient group. Under `NonarchimedeanGroup A`, the two
`isOpen_ker_geometricEpsilon*` lemmas pull back the existing original open-kernel
proofs. `geometricEpsilonOneSmoothCharacter` and
`geometricEpsilonTwoSmoothCharacter` package these exact monoid homomorphisms
as smooth characters.

## Comparison with the original compact integral

The generic lemma
`geometricTargetCorrectionIntersectionModulus_eq_ambient` uses the literal
identity

`intersectionSource U_I P_J n⁻¹ = geometricTargetIntersection U_I P_J n`.

It compares the two closed-normalizer Haar characters at any points with the
same ambient value. The private congruence lemma proves this by substituting
the subgroup equality and using subtype extensionality; proof irrelevance
identifies the closedness witnesses. No freely chosen modulus is introduced.

Let `c = geometricCommonLeviInTarget`,
`δU = geometricCompactRadicalModulus` and
`δC = geometricCompactCorrectionModulus`. The two modulus-comparison lemmas
prove equality of monoid homomorphisms on `L_t`:

- `geometricEpsilonTwo_radicalModulus_eq` identifies the original target radical
  modulus with `δU.comp c`.
- `geometricEpsilonTwo_correctionModulus_eq` identifies the original target
  correction-subgroup modulus with `δC.comp c` by the generic ambient lemma
  and the point-preserving inclusion.

`geometricEpsilonTwo_eq_half` then rewrites the original target character as

`(complexCharacter (positiveHalfCharacter δU) * inverseHalfCharacter δC).comp c`.

These are the canonical positive real square roots, not selected square-root
branches. Finally, `geometricEpsilonTwo_sq` specializes the original correction
square identity, rewrites both positive moduli, and applies
`geometricCompactHaarCharacter_eq_ambient`. At every `l : L_t` it proves

`geometricEpsilonTwo l ^ 2 = geometricCompactHaarCharacter (c l)`.

The last theorem additionally retains closedness of `P_I`, local compactness
of `geometricCompactKernel`, and the explicit measurable/Borel structures on
that kernel and `geometricCompactKernelIntersection`, exactly as in the
compact Haar comparison. No measure or representation hypothesis is erased by
this equality.

## Provenance, dependencies and remaining work

This is an internal specialization and transport argument. Its proof bodies
use the generic `GeometricIntersectionCorrections` character definitions,
`geometricTargetCorrectionCharacter_eq` and `_sq`, the generic open-kernel
lemmas, and `RationalGeometricCompactHaar`'s two positive characters and
`geometricCompactHaarCharacter_eq_ambient`. The ambient congruence also uses
the original `Geometric.General.isClosed_correctionSubgroup` and the actual
intersection-membership and transport-application lemmas. Those dependencies
supply the original forward-conjugation Haar convention and the existing
inverse-conjugation integral ratio.

The new proof bodies use no geometric-lemma expansion, adjointness, cuspidal
support, character independence, or Langlands classification. The imported
module closure includes the actual rational geometric targets and compact
comparison machinery; importing those interfaces supplies no expansion proof.

The construction does not assert cancellation of both corrections, balance
between distinct radicals, an identification of normalized coefficient
representations, compact/full induction comparison, or the final exact K0
expansion. All displayed analytic hypotheses are internal comparison inputs
that remain to be discharged from the unchanged final target.
