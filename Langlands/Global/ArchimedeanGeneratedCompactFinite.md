# Compact finiteness of the actual compact-and-enveloping span

Author: Worker 94.

`generatedCompactDifferentialSpan K n f` is an abbreviation for the published
`compactDifferentialGeneratedSpan K n f` in
`ArchimedeanCompactDifferentialGeneratedModule`. It is the complex algebraic
span of the actual vectors `R(k) D(a) f`, using the whole standard compact
subgroup and the genuine complex enveloping algebra. The integrated module
reuses that definition.

These internal algebraic helpers use the published actual compact action,
enveloping covariance and finite adjoint coefficient expansion. They
apply to all number fields in arbitrary universe and all natural ranks.
No center-finiteness, growth, analyticity or connectedness assumption is
used.

`compactAction_operator_covariance` reuses the published
`DerivativeSmoothFunctions.compactAction_enveloping_smul`, rewriting the
actual scalar action with `enveloping_smul_eq_operator`:

`R(k) D(a) f = D(Ad(k) a) R(k) f`.

`compactFinite_operator` proves that `D(a) f` is compact-finite whenever
`f` is. The implemented proof uses the published finite expansion of
`Ad(g) a` in fixed enveloping elements `b i`. Let `O` be the
finite-dimensional compact-orbit span of `f`. Covariance puts every
compact translate of `D(a) f` in the finite sum of images `D(b i)(O)`.
Each image and their finite sum are finite-dimensional. The new compact
orbit span, being a subspace of that sum, is finite-dimensional.
Continuity of the coefficient functions is supplied by the published
expansion but is not needed for this algebraic argument.

`generatedCompactDifferentialSpan_compactFinite` then uses the actual
subrepresentation of finite vectors. Each generator `R(k) D(a) f` lies in
it by the preceding theorem and stability under compact translation, so
the entire algebraic span does.

`compactAction_mem_generatedCompactDifferentialSpan` proves invariance
of that span directly by span induction. A translate of the generator
indexed by `(l, a)` is the generator indexed by `(k * l, a)`; linearity
handles sums and scalar multiples.

These results prove compact finiteness of individual vectors in the
generated module. They do not prove finite multiplicity of a compact
type, finite dimension of the whole generated module, existence of
continuous compact-type projections, orbit density or reproduction.
