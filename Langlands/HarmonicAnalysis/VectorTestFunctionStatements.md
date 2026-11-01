# Vector-valued disjoint indicators and canonical tensor-map assertions

This statement family records David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, II.1.2, printed p.32 /
PDF p.38, equations (II.1.2.3) and (II.1.2.4) and the paragraph immediately
following them. That paragraph explicitly extends the disjoint-indicator
lemma from printed p.31 / PDF p.37 to arbitrary complex vector spaces.
The registered original is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The namespace is
`Langlands.HarmonicAnalysis.VectorTestFunctionStatements`. Each declaration
is a closed `Prop`-valued definition. These are statements only; this module
provides no proofs of them.

## Source scope and actual carriers

Each of the four component assertions quantifies over a type `X : Type uX`
with its supplied `TopologicalSpace X`, and instances `T2Space X`,
`LocallyCompactSpace X`, and `TotallyDisconnectedSpace X`. These are precisely
Renard's t.d. spaces, defined on printed p.30 / PDF p.36 as Hausdorff spaces
with a compact-open neighborhood basis. The published theorem
`Langlands.Topology.isLocallyProfinite_iff_mathlib` identifies the two
formulations. No topology is replaced or chosen.

The coefficient type `V : Type uV` has only `AddCommGroup V` and `Module ℂ V`.
The universe parameters `uX` and `uV` are independent. There is no topology,
dimension restriction, basis choice, countability assumption, or
nonemptiness assumption on the coefficient space or domain. In particular,
empty domains and the zero vector space are included.

All carriers and maps are imported from
`Langlands.HarmonicAnalysis.VectorTestFunction`:

- `LocallyConstant X V` is Renard's \(C^\infty(X,V)\).
- `Space X V` is the actual submodule of these functions whose underlying
  function has compact support, namely \(D(X,V)\).
- `SchwartzBruhat X` is the existing scalar carrier \(D(X)\). The published
  `scalarEquiv` identifies it with `Space X ℂ` without changing evaluation.
- `compactBilinear f v` is the actual compact test \(x\mapsto f(x)v\).

Support means the closure, in the given topology on `X`, of the set where
the function is nonzero. This agrees with Renard's support convention on
printed p.30 / PDF p.36. All vector space operations are pointwise.
Every tensor product below is algebraic over \(\mathbb C\).

## Declaration correspondence

`DisjointIndicatorDecomposition` states the vector-valued decomposition
used in the paragraph following (II.1.2.4). For every `f : Space X V`,
it gives a natural number `n`, sets `U i` indexed by `Fin n`, witnesses
that each is clopen and compact, and vectors `v i : V`. The sets are
pairwise disjoint, and the asserted equality is

\[
  f=\sum_{i\in\operatorname{Fin}(n)} \chi_{U_i}\,v_i
  \qquad\text{in }D(X,V).
\]

Each summand is explicitly
`compactBilinear (Langlands.Hecke.TestFunction.characteristic (hUo i) (hUc i))
(v i)`. Thus the equality is in the actual `Space X V`, with the existing
scalar characteristic functions, rather than merely an equality in a
replacement carrier. A compact open is closed in a Hausdorff space, so the
clopen witnesses express exactly the source's compact opens. The index
`n` may be zero; no set or coefficient is required to be nonempty or
nonzero. This includes the empty expansion of the zero test.

`SmoothTensorInjective` states injectivity of the published
`smoothTensorMap`:

\[
 C^\infty(X,\mathbb C)\otimes_{\mathbb C}V
 \longrightarrow C^\infty(X,V),\qquad
 f\otimes v\longmapsto [x\mapsto f(x)v].
\]

This is exactly the canonical injection in (II.1.2.3).

`CompactTensorInjective` states injectivity of the published
`compactTensorMap`:

\[
 D(X)\otimes_{\mathbb C}V
 \longrightarrow D(X,V),\qquad
 f\otimes v\longmapsto [x\mapsto f(x)v].
\]

This is the analogous injection in (II.1.2.4). Its source uses the original
scalar `SchwartzBruhat X` and its target is `Space X V`.

`CompactTensorSurjective` states surjectivity of this same actual
`compactTensorMap`. This is the conclusion of the paragraph immediately
following (II.1.2.4), where Renard uses the finite disjoint-open
decomposition. Together, `CompactTensorInjective` and
`CompactTensorSurjective` state exactly that this already constructed
complex-linear map is bijective, the source's resulting algebraic linear
isomorphism assertion. No tensor property or chosen linear equivalence
is an input to any declaration.

`Assertions` is the closed conjunction of the preceding four statements,
with both universe parameters retained explicitly in each conjunct. This
aggregate is an internal packaging of precisely this source passage.
Proofs of the four assertions and any chosen equivalence construction
remain successor work.
