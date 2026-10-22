# Complete p-adic arithmetic normalization proof

Lean proof author: Worker 27. The closing theorem is `Langlands.padicNormalization`,
with target `Langlands.PadicNormalizationStatement`. It proves the entire
universally quantified proposition. The named intermediate theorems give
reusable residue, discrete-order, integer-ring, ramification, absolute-value
and topology interfaces. Worker 12 reused the Lean proof unchanged, verified
its exact accepted dependencies and complete scope, and expanded this
explanation. Both workers are credited in the proof submission.

The carrier universe is arbitrary. The closing theorem introduces every
prime `p`, every `F : PadicField p`, and each supplied
`T : F.TopologicalData` from the accepted proposition. It adds no hypothesis.
The integer and residue structures and scalar maps are exactly the accepted
ones derived from `T`. Constructing `TopologicalData` for arbitrary algebraic
extensions remains a separate task.

The closing theorem assembles all seven groups in their accepted order:

| Accepted law group | Implemented component results |
| --- | --- |
| `ResidueArithmeticLaws` | `finite_residueField`, `residueScalarMap_injective`, `residueDegree_pos`, `residueCardinality_gt_one`, `residueCardinality_eq_pow`, and the accepted `residueCharP` certificate |
| `DiscreteOrderLaws` | Surjectivity and uniformizer results, `ord_zero`, `ord_one`, `ord_mul`, `ord_inv`, `min_ord_le_ord_add`, `ord_surjective_nonzero`, and the positive ramification-index identification |
| `ResidueAbsoluteValueLaws` | Zero, one, positivity, nonnegativity, nonzero formula, multiplication, ultrametric inequality and uniformizer value for `normalizedAbs` |
| `IntegralExtensionLaws` | `integers_isIntegralClosure`, `isIntegral_iff_mem_integers`, `integers_finite`, `integers_free`, `integers_finrank`, and both unit-ball criteria |
| `RamificationDegreeLaws` | `span_prime_eq_maximalIdeal_pow`, `map_base_maximalIdeal`, `ramificationIdx_eq`, `inertiaDeg_eq`, `ramificationIndex_mul_residueDegree`, and `extensionDegree_pos` |
| `NormalizedComparisonLaws` | `ord_algebraMap`, `normalizedAbs_algebraMap_degree`, `normalizedAbs_eq_canonicalNorm_pow_degree`, and the degree-one component results |
| `NormalizationTopologyLaws` | Both supplied-topology comparisons, `normalizedAbs_balls_basis`, `normalizedAbs_topology_eq`, and `normalizedAbs_topology_eq_canonicalModule` |

`padicNormalizationBasic` packages the first three groups; the closing
`padicNormalization` combines them with the remaining four. All supporting
results stay in this one proof module.

The consolidated statement and proof both compiled with no errors or
warnings. A separate diagnostic assigned the closing theorem to the entire
universe-polymorphic target and inspected its transitive axiom closure:
only `propext`, `Classical.choice` and `Quot.sound` occur. The diagnostic
also checked the types and axiom closures of the degree, spectral-norm
comparison and topology comparison theorems. This establishes native
development checks, not registered independent proof verification.

Worker 12 repeated compilation of both accepted definition modules, the
accepted statement and this unchanged proof with the pinned Lean executable.
The full-target assignment and the degree, norm and topology declaration
inspections all succeeded without diagnostics. The reported axiom closures
again contain only `propext`, `Classical.choice` and `Quot.sound`.

The first part uses the finite actual residue field supplied by the local
field structure and Mathlib's finite vector-space cardinality formula.
The discrete valuation is the actual valuation composed with its ordered
value-group isomorphism to `WithZero (Multiplicative Int)`. Its logarithm
gives the additive order, with zero explicitly assigned order zero. The
base prime has strictly subunit multiplicative valuation, so its additive
order and the resulting natural ramification index are positive.
Since `q > 1`, comparison of powers of `q` transports valuation comparisons
to the normalized absolute value. This proves multiplicativity and the
ultrametric inequality, splitting out every zero case.
The integer order retains `ord 0 = 0`. Product additivity uses two nonzero
premises, and its sum inequality also excludes a zero sum, exactly as in the
target. Inversion, the base order formula, absolute-value multiplication and
the ultrametric inequality retain their all-element scopes.

For a nonzero base element, its p-adic valuation equals that of the
corresponding integral power of `p`. `ValuativeExtension` transports both
valuation inequalities to the extension. The discrete value-group
isomorphism and logarithm then give `ord_F(a) = e * ord_p(a)`.
Together with `q = p^f`, this yields the base absolute-value formula
with exponent `e*f`.

To compare to the spectral norm before knowing `e*f = [F:Q_p]`, the proof
raises the normalized absolute value to the positive real exponent
`1/(e*f)`. The result is a genuine absolute value: multiplicativity,
the zero criterion and the triangle inequality follow from the already
proved laws and the ultrametric inequality. It extends the given norm on
`Q_p`. Mathlib's `spectralNorm_unique_field_norm_ext` identifies it with
the canonical spectral norm. Raising back to the positive integer power
`e*f` proves `normalizedAbs(x) = canonicalNorm(x)^(e*f)` for all `x`,
including zero.

This positive power comparison identifies both unit balls with the actual
valuation integer ring. For an element of the spectral-norm unit ball,
the spectral-value criterion bounds all coefficients of its monic minimal
polynomial by one. They therefore lie in the actual base integer ring.
The polynomial lifts to a monic polynomial over that ring and proves
integrality. Conversely, an element integral over the base integer ring
is integral over the extension integer ring by the explicit scalar tower;
the valuation integer ring is integrally closed, so it contains the
element. This constructs the actual integral-closure certificate.
Mathlib's integral-closure results now prove that the integer extension
is finite and free, with rank equal to the field-extension degree.
The field extension is separable because it has characteristic zero;
no Galois hypothesis is imposed.

For the ramification formula, the actual integer ring is also shown to be
the integer ring of the discrete valuation. The chosen element of
valuation `exp (-1)` generates its maximal ideal. Its `e`-th power has
the same valuation as `p`, whereas the next power has strictly smaller
valuation. Thus the ideal generated by `p` is exactly the `e`-th maximal
ideal power and is not contained in the next one. The actual base integer
ring is identified with `PadicInt p` by the identity on the underlying
field. Since `p` is irreducible there, the base maximal ideal is generated
by `p` as well. Mathlib's ideal-exponent ramification characterization and
its comparison with the localization-length definition therefore give
the ramification index `e`.

The induced base-residue equivalence identifies the actual base residue
field with `ZMod p`. Applying the finite-field cardinality formula to the
actual residue extension and comparing it with `q = p^f` identifies its
inertia degree with `f`, by injectivity of powers of `p > 1`.
The extension integer ring is local, so it has only its maximal ideal
above the nonzero base maximal ideal. Mathlib's finite flat
ramification-inertia sum formula consequently has exactly one term.
It proves `e*f` equals the integer-module rank and hence `[F:Q_p]`.
Substitution gives the required spectral-norm exponent.

The final part proves the base-embedding formula also at zero, proves
positivity of the extension degree, and derives the degree-one values
`e = f = 1`, `q = p` and equality of normalized and canonical norms.
The supplied topology is the canonical module topology by its explicit
certificate. The finite-dimensional topology theorem over the complete
base field identifies this topology with the spectral-norm topology.
Under that norm topology, the normalized absolute value is the positive
integer power of the norm. Its balls are open, and a norm ball of radius
`delta > 0` is the absolute-value ball of radius `delta^degree`.
These balls therefore form a basis, proving both generated-topology
equalities without introducing a competing global instance.

Source and normalization provenance: Serre, *Local Fields*, Greenberg
English translation, GTM 67 (1979), Chapter II, section 1, printed
pages 26–28; section 2, Proposition 3 and Corollaries 1–4, pages 28–30;
section 5, page 36. Source ID `serre-1979-local-fields`, PDF SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
The proof above describes the implemented Mathlib route, including the
spectral-norm comparison before the degree identity.
Worker 12 read these original pages in the retained PDF and verified its
fingerprint. The key Mathlib interfaces were also checked in the pinned
source: `spectralValue_le_one_iff` and
`spectralNorm_unique_field_norm_ext` in
`Analysis/Normed/Unbundled/SpectralNorm.lean`, lines 202 and 770;
`IsIntegralClosure.finite`, `module_free` and `rank` in
`RingTheory/DedekindDomain/IntegralClosure.lean`, lines 175, 183 and 192;
`Ideal.sum_ramification_inertia_eq_finrank` in
`RingTheory/RamificationInertia/Basic.lean`, line 72; and
`isModuleTopologyOfFiniteDimensional` in
`Topology/Algebra/Module/FiniteDimension.lean`, line 271.

Project definition inputs: accepted and published `Langlands.LocalField.Definitions`,
artifact `ac4cb7d5-5dd1-44b6-9d56-f0ec6c70bce0` version 1; the arithmetic
definition artifact `e3d7bbd4-f2b9-4970-a60f-bf6aa0b34bb2` version 1,
published without edits at commit
`9db46907db3181b0c1dfd287b8ab2f1f02054cab`, final review receipt
`5d095fa472fd49acb7a360c6f2ade9de`.
The exact accepted statement is
`62e8bb5c-3f54-449e-bbd6-98de9dc15781` version 1, review
`0b7b6215-c076-4dc8-b66c-c64b7a718b5e`. It passed automated validation
and Reviewer 80's independent semantic review without changes, and was
published at commit `d0f5322f745425b08ae8e72c1031206f45cb049e`, final review
receipt `77c874fe6b7f463f91d916a661066cce`. The complete final review and
both published files were read; the saved draft matches them exactly and
the full dependency closure is current. Its target fingerprint is
`365a833e72aab523dab2fb6fd0f822ea24741377a9366660a7b9b8b554c10391`;
its Lean source SHA256 is
`27f6b841c15cf1e4dffcb40126f95ea329c08d91ab9950d8fe645a94683eedc6`
and its Markdown SHA256 is
`245db7bd9d6b10a8e9cb2882021f2d210a396aa1149e9a8adeb9a889bc7d753b`.
The proof is to be submitted only through a native proof task bound to this
exact statement and closing declaration. Environment:
`2ecc41bc-2901-4e34-96c5-6d98fbb3c74d` version 1, Lean 4.34.0,
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
Independent proof checking, independent semantic review and current proof
publication remain required. Reuse must preserve Worker 27's authorship.
