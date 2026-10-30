# The relation kernel of compact induction and normal coinvariants

Worker 128 states
`Langlands.Induction.CompactInductionNormalCoinvariantKernel.{uG,uV}`.
This is a Prop-valued definition for a separate proof. It introduces no
construction and proves no kernel equality. The exact proposition is proved by
`Langlands.Induction.compactInductionNormalCoinvariantKernel` in
[`NormalCoinvariantKernelProof`](NormalCoinvariantKernelProof.md); see
"Proof status" below.

## Quantifiers and conclusion

Every hypothesis is quantified inside the proposition. Let `G : Type uG`
be a group with a topology, continuous group operations, and the Hausdorff
property. The compact open subgroup hypothesis is exactly the one in
[`CompactInductionNormalCoinvariants`](NormalCoinvariantStatement.md):

```lean
∀ O : Set G, IsOpen O → (1 : G) ∈ O →
  ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ O
```

Let `H N : Subgroup G`, with `N.Normal`, `H` and `N` closed in `G`, and
`N ≤ H`. For every `V : Type uV`, additive commutative group structure on
`V`, complex module structure on `V`, and representation
`sigma : Representation ℂ H V` satisfying `Langlands.IsSmooth sigma`,
the conclusion is

```lean
∀ f : CompactFunctions H sigma,
  (f ∈ Representation.Coinvariants.ker
    ((compactInduced H sigma).comp N.subtype)) ↔
  (∀ g : G, eval H sigma f.val g ∈ Representation.Coinvariants.ker
    (sigma.comp (N.subgroupOf H).subtype))
```

The group universe `uG` and coefficient universe `uV` are independent.
The compact function carrier lies in `Type (max uG uV)`. Smoothness means
that every vector is fixed by an open subgroup of `H`. This explicit
quantification over modules and smooth representations covers the same
coefficient objects as the parent's full smooth category. No coefficient
topology, norm, completeness, dimension, admissibility, or length condition
is present.

Both occurrences of `Representation.Coinvariants.ker` are Mathlib's actual
submodule

```lean
Submodule.span ℂ (Set.range fun gv => rho gv.1 gv.2 - gv.2)
```

for the displayed restricted representation `rho`. Thus the left side is
membership in the finite complex-linear span of action differences of
actual compactly induced functions, and the right side tests membership
in the corresponding coefficient relation span at every point of `G`.
The subgroup `N.subgroupOf H` consists of elements of `H` whose ambient
values belong to `N`; containment `N ≤ H` ensures it represents all of `N`.

The imported induction model uses actual covariant functions with
`f(h * g) = sigma(h)(f(g))`, right translation `f(g * n)`, a single open
right stabilizer for each whole function, and compact projected nonzero
support in `H \ G`. The evaluation here is that model's `eval`, applied
to `f.val : SmoothFunctions H sigma`.

There is no hypothesis giving a section, lifting, exactness, averaging,
comparison map, or comparison equivalence. The normal subgroup may be any
closed normal subgroup contained in `H`; no unipotence or compact
exhaustion is required. The declaration neither imports nor assumes
`CompactInductionNormalCoinvariants`.

## Source and internal formulation

The source is I. N. Bernstein and A. V. Zelevinsky,
*Induced representations of reductive p-adic groups I*, Ann. Sci. ENS (4)
10 (1977), 441–472, §5.16, printed pages 465–466, PDF pages 26–27.
Worker 128 read the entire section and visually checked both pages,
including the reduction diagram.

- Literature ID: `bernstein-zelevinsky-1977-induced-i`.
- Retained original:
  `/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`.
- SHA-256:
  `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.

The diagram splits Case IV, where `U = {e}` and `G = Q`, through
`(M ∩ N)V` into Cases IV₁ and IV₂. The relevant Case IV₁ assumes
`V ⊆ M = P`. Its `M` corresponds to our `H`, and its `V` to our normal
subgroup `N`; its complementary subgroup named `N` is different from
our notation. We specialize the character to the trivial character and
use unnormalized compact induction and coinvariants on the same ambient
group. The original's complement, normalization, and Case IV₂ quotient
integration are outside this statement.

In Case IV₁ the normal subgroup acts trivially on the coset space, so the
coinvariant space inherits multiplication by locally constant compactly
supported scalar functions there. The source forms the associated sheaf,
identifies its fiber by commuting coinvariants with the filtered limit of
neighborhood localizations (citing §§1.9(g) and 5.11), and invokes the
equivariant sheaf equivalence of §5.14.

The displayed kernel equality is an internal pointwise formulation of
this localization mechanism. It is not a verbatim separately numbered
theorem in the original, nor a claim that §5.16 prints these exact
quantifiers for arbitrary closed normal subgroups. The published
[`NormalCoinvariantStatement`](NormalCoinvariantStatement.md) explains
the same source specialization for the full comparison. This focused
statement isolates the relation-kernel obligation needed for that
comparison; it does not assert its surjectivity or naturality.

## Elementary proof route proposed with the statement

This route was written with the statement, before any proof existed. The
published proof implements it in substance; see "Proof status" below.

For `n ∈ N`, normality gives `g * n * g⁻¹ ∈ N ⊆ H`, hence
`H * g * n = H * g`. Covariance therefore sends an evaluated global
action difference to a coefficient relation involving `g * n * g⁻¹`.
Linearity then gives the forward implication.

For the reverse implication, pointwise span membership supplies a finite
coefficient relation expression at each chosen point. The existing
[`compactLocalSection`](CompactLocalSection.md), or its
`compactDoubleCosetSection` construction, can realize its vectors as
values of actual compactly induced sections. Conjugating the relation
elements back into `N` yields a finite sum of global action differences
with the prescribed value at that point. Local constancy and covariance
then give agreement with the original function on a quotient
neighborhood.

One must choose compact clopen quotient neighborhoods and patch finitely
many such local identities over the compact projected support, using the
existing [`compactQuotientCutoff`](CompactQuotientCutoff.md) and a finite
clopen refinement. Because `N` fixes every point of `H \ G`, cutoff
multiplication commutes with its action and preserves the global
relation span. Establishing this preservation and the finite global
relation expression was left to the proof. Neither is an assumed kernel
exactness or an additional hypothesis here.

## Proof status

`Langlands.Induction.compactInductionNormalCoinvariantKernel`, in
`Langlands.Representation.Induction.NormalCoinvariantKernelProof`, has type
exactly `CompactInductionNormalCoinvariantKernel.{uG,uV}`. It keeps the two
independent universes and every hypothesis above: the compact open subgroup
basis, closedness of `H` and `N`, normality of `N`, `N ≤ H` and smoothness of
`σ`. It adds no hypothesis. Evaluation of global relation generators gives
the forward implication. For the reverse implication, each coefficient relation
is lifted to a global relation through `compactLocalSection`. The difference
between `f` and that relation has closed projected support missing the chosen
coset, which gives a compact clopen quotient neighborhood on which they agree.
Cutoff multiplication by `compactQuotientCutoff` preserves the global relation
span, and finitely many such cutoffs covering the compact projected support of
`f` are patched together. The proof companion explains the details and notes
that closedness of `N` is not used by the argument.

The Lean imports only `Induction.Definitions`, Mathlib's coinvariants,
and the complex coefficient infrastructure. The section and cutoff
modules describe available proof ingredients; no additional construction
from them is required to state the target. All existing statement and
imported Lean/Markdown pairs are preserved.
