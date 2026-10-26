# Spanning compact induction by translated local sections

Worker 630 defines the proposition
`Langlands.Induction.CompactLocalSectionSpanning.{uG,uV}`.
It states that actual compact induction is spanned over `ℂ` by right
translates of the published compact double-coset sections centered at `1`.
This pair supplies a statement for a separate proof; it proves no spanning
theorem.

## Exact scope

The definition has no external parameters. Its proposition quantifies over:

- `G : Type uG`, with `Group G`, `TopologicalSpace G`,
  `IsTopologicalGroup G` and `T2Space G`;
- the literal compact-open identity-neighborhood basis
  ```lean
  ∀ O : Set G, IsOpen O → (1 : G) ∈ O →
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ O
  ```
- every subgroup `H : Subgroup G` with `IsClosed (H : Set G)`;
- every `V : Type uV`, with `AddCommGroup V` and `Module ℂ V`;
- every `sigma : Representation ℂ H V`.

The group and coefficient universes are independent. The function carrier is the published
`CompactFunctions H sigma : Type (max uG uV)`. The coefficient space is
algebraic, with no topology, norm, completeness, dimension or finiteness
assumption. Neither `H` nor any section subgroup is assumed normal.

For these data, the conclusion is exactly `Submodule.span ℂ S = ⊤`, where
the generator set is the following explicit comprehension in that actual
function carrier:

```lean
{f : CompactFunctions H sigma |
  ∃ (g : G) (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (v : V) (hv : v ∈ fixedVectors sigma (conjOpenSubgroup H K 1).toSubgroup),
    f = compactInduced H sigma g
      (compactDoubleCosetSection H sigma K hK 1 v hv)}
```

All such `g`, compact open `K`, vectors `v` and fixed-vector proofs `hv`
are allowed. The section constructor takes `H`, `sigma`, `K`, `hK`, the
center `1`, `v` and `hv` in precisely that order. Its required subgroup
`conjOpenSubgroup H K 1` consists of the elements of `H` whose underlying
elements of `G` lie in `K`; it represents `H ∩ K`.

## Actual functions and action

The imported
[`CompactLocalSection`](CompactLocalSection.md) constructs
`compactDoubleCosetSection` inside the existing `CompactFunctions`. Its
value at `h * 1 * k` is `sigma h v`, and it vanishes outside `H * K`.
The individual hypothesis `hv` makes this prescription independent of a
factorization. The constructor carries covariance, a single open right
stabilizer for the entire function, and compactness of its actual
projected nonzero support.

The published `compactInduced H sigma g` is the actual right-translation
operator: evaluation of its value on a function `s` at `y` is `s(y * g)`.
Consequently the displayed generator is an actual translated section in
compact induction. Its support lies in `H * K * g⁻¹`. The set is not a
formal collection of symbols or a replacement function module.
`Submodule.span` takes finite complex linear combinations in this existing
module.

No global `IsSmooth sigma` is imposed. Each section vector supplies its own
fixed-vector proof, and every member of `CompactFunctions H sigma` already
has a uniform open right stabilizer. The statement assumes neither
compactness of the whole quotient `H \ G` nor a finite decomposition of its
functions. It has no measures, lifting, exactness or integral hypotheses
and asserts nothing about coinvariants or quotient-integral injectivity.

## Intended finite-support proof route

The following explains the intended argument for a future proof; none of
these steps is a premise or a theorem proved in this pair.

Fix an actual `f : CompactFunctions H sigma`. Its uniform open right
stabilizer contains a compact open subgroup `K` by the literal basis
hypothesis. The projected double cosets `H * x * K` form an open cover of
`H \ G`. Apply compactness only to the actual projected nonzero support of
`f`, which is compact by its membership in `CompactFunctions`. Choose a
finite subcover indexed by representatives in the nonzero support and
retain one representative of each distinct double coset. Covariance and
right invariance keep each such double coset inside the nonzero support,
so they give a disjoint finite partition of that support.

At a chosen representative `x`, covariance and right `K`-invariance imply
that `f(x)` is fixed by `H ∩ x K x⁻¹`. The published
`eval_mem_fixedVectors` in
[`CompactQuotientProof`](CompactQuotientProof.md) supplies this evaluation
fact once right invariance is expressed as fixed-vector membership.
The actual section
`compactDoubleCosetSection H sigma K hK x (f(x)) hv` therefore reproduces
`f` on `H * x * K` and vanishes elsewhere. Summing these finitely many
sections should give `f`.

To match the generator set centered at `1`, put `L = x K x⁻¹`.
Conjugation makes `L` compact and open, and the same vector `f(x)` is fixed
by `H ∩ L`. The section centered at `x` should equal the right translate
by `x⁻¹` of the section centered at `1` for `L`: at `y`, that translate
evaluates the identity-centered section at `y * x⁻¹`. This also explains
the translation direction in the statement. The needed finite-cover,
section-sum and conjugation identities remain proof obligations.

The existing `exists_finset_doubleCoset_cover` assumes
`CompactSpace (LeftQuotient H)`. That assumption is absent here, so that
theorem cannot directly supply this argument's finite cover. The future
proof must use the compact projected support of each actual `f`.

## Provenance and ownership

This is an internal finite compact-support decomposition target derived
from the published actual-function definitions, right-translation action,
and double-coset section construction. Worker 199 specified the interface
and intended proof route; Worker 630 authored this Lean/Markdown pair.
Its sole import is
`Langlands.Representation.Induction.CompactLocalSection`, which imports
`CompactQuotientProof` and the underlying
[`Definitions`](Definitions.md). All published pairs remain unchanged.
This statement is not a quotation or formalization of a spanning lemma in
Bernstein and Zelevinsky (1977); no external source theorem is used as a
premise or claimed as proved.

Worker 199 retains the proof successor and the final actual
quotient-integral bijectivity assembly in task
`cbaf9d61-f090-41e3-8269-9ae5a6992693`. Reusable finite compact-support
decomposition should be coordinated with Worker 182's compact-surjectivity
work before proof implementation. This pair contains only the focused
statement.

## Development check

The module compiled without errors or warnings in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean 4.34.0, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`).
Inspection of the exact declaration reported a definition returning
`Prop`, with level parameters `uG` and `uV`. Its axiom closure contains
only `propext`, `Classical.choice` and `Quot.sound`.
These development checks establish neither the truth of the spanning
proposition nor independent acceptance or publication.
