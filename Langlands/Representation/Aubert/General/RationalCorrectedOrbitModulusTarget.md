# Squared intersection modulus for corrected Aubert orbits

Author: Worker 76. The precise conditional orbit Jacquet modulus input and
its scalar use are due to Worker 1255, within Worker 969's interface.
Workers 164 and 6 contributed the residual-obligation reconciliation.

`RationalCorrectedOrbitSquaredModulusStatement.{u}` in
`Langlands.Aubert.General.RationalPointFamily` is a proposition definition.
Its generic template is `CorrectedFiltration.OrbitSquaredModulusTarget`.
Neither definition proves its proposition or asserts it for arbitrary
subgroup families.

## Exact assertion

Fix a standard source index `I`, a valid position `j` of the existing
decreasing-length Weyl list, and an actual normalizer lift `m` of the inverse
of its entry. Fix any standard `K` and whole-Levi comparison
`hK : x ∈ M_I ↔ m⁻¹ x m ∈ M_K`. Put

```text
Z = orbitUnipotentIntersection U_I U_K m = U_I ∩ m U_K m⁻¹.
```

For every `l ∈ M_I`, the conclusion is the identity in `ℝ≥0`

```text
δ_(U_I)(l) · δ_(U_K)(m⁻¹ l m) = δ_Z(l) ^ 2.
```

All three factors are the existing
`HaarModulus.closedRestrictCharacter`, coerced from positive units to
`ℝ≥0`. The second uses exactly `conjugationEquiv m hK l`. The character
of `Z` uses the published proof
`isClosed_orbitUnipotentIntersection` from the closedness of the two
radicals, and the published
`levi_le_normalizer_orbitUnipotentIntersection` from the two actual
semidirect decompositions and `hK`. Thus closedness of `Z` and its
normalization by `M_I` are constructions already available, not added
premises.

This is exactly `hD07` of the published
`CorrectedFiltration.nonempty_orbitJacquetData_of_isLimitOfCompactSubgroups`,
specialized to every actual grade, inverse lift, `K` and `hK`. As in that
consumer, the identity does not depend on a target `J`, its minimality or
`K ⊆ J`. There is no representation, coefficient measure or finite-length
premise.

## Rational premises and scope

The rational statement repeats the structural premises of
`RationalCorrectedGradedTransitionStatement`: an arbitrary nonarchimedean
local field, connected reductive group scheme, actual maximal split torus,
generic cocharacter, canonical `pointTopology`, and the displayed locally
compact, nonarchimedean and Hausdorff group instances. It retains the named
standard-cocharacter, standard-parabolic-order and standard-Levi-intersection
statements; relative roots; point normalizer and centralizer comparisons;
closed radicals and Levis; and the compact-limit condition for radicals.
It also retains the root-length, positive-simple-reflection and actual
Levi-Weyl comparisons for the Coxeter system.

The decomposition used by the characters is exactly
`isSemidirectDecomposition_of_standardCocharacterStatement`. Shared
premises unused in this particular expression remain explicit with
underscored names. No extra determinant, weight, modulus, intersection or
representation-theoretic assertion is assumed.

The actual Weyl group is the quotient by the full torus centralizer.
Positive characteristic, nonsplit and non-quasisplit groups, and the empty
simple-root set are retained. Only the field universe `u` occurs in this
rational proposition.

## Internal provenance and remaining work

This is an internal consumer prerequisite extracted directly from the
published `CorrectedOrbitJacquet` pair's `hD07` binder and section
"Hypotheses". It is not a transcription of a numbered literature theorem.
The generic template names the actual expression rather than introducing
an alternative modulus convention.

The published `orbitJacquetMap_levi` explains why this *squared* identity is
needed: the full inverse-conjugation Haar ratio is
`δ_Z(l)⁻¹ / δ_(U_I)(l)⁻¹`, and `inv_sqrt_mul_ratio_eq` turns the identity
into compatibility with the inverse Jacquet half-moduli. This pair proves
neither the identity nor a new integral comparison.

The separate equality between a full parabolic's modular character and the
conjugation modulus of its radical does not establish this intersection
identity. The actual rational intersection-weight or determinant comparison
still needs a proof. In particular this assertion is not added to the
allowed external Chapter V structural-input boundary.

The radical containments `(S1)` and `(S2)`, fixed-order support topology,
quotient compactness, continuous projections, conditional orbit integral,
full-smooth exactness, general proper-target comparison and terminal
comparison retain their separate obligations and owners. No existing target
or import is changed.
