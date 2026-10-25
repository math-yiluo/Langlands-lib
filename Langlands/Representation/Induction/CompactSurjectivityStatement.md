# Surjectivity of compact induction from a closed subgroup

Worker 440 states
`Langlands.Induction.CompactInductionSurjectivityStatement.{uG,uV,uW}`.
Its telescope follows Worker 380's published smooth-surjectivity statement.
This `Prop`-valued definition is a target for a separate proof. Defining it
does not assume or prove its truth.

## Statement and conventions

The proposition quantifies inside its own telescope over:

1. `G : Type uG`, with `Group G`, `TopologicalSpace G`,
   `IsTopologicalGroup G` and `T2Space G`;
2. compact-open cofinality:
   `∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
   IsCompact (L : Set G) ∧ L.toSubgroup ≤ K.toSubgroup`;
3. `H : Subgroup G`, with `IsClosed (H : Set G)`;
4. arbitrary complex modules `V : Type uV` and `W : Type uW`, each
   with `AddCommGroup` and `Module ℂ` instances;
5. `sigma : Representation ℂ H V` and `tau : Representation ℂ H W`,
   with `IsSmooth sigma` and `IsSmooth tau`;
6. the actual intertwiner `T : sigma.IntertwiningMap tau`, with
   `Function.Surjective T`.

The conclusion is `Function.Surjective (compactInducedMap H T)`.
Equivalently, every `f : CompactFunctions H tau` is the image of some
`F : CompactFunctions H sigma` under this map. The group and coefficient
universes are independent; the two function carriers have universes
`max uG uV` and `max uG uW`.

All constructions are those of
[`Induction.Definitions`](Definitions.md). Its `CompactFunctions H sigma`
consists of actual functions with covariance
`F(h*x) = sigma(h)(F(x))`, one open subgroup fixing the whole function on
the right, and compact projected actual nonzero support
`quotientMap H '' Function.support F` in `LeftQuotient H`.
The quotient has the quotient topology and represents `H \ G`;
it is not assumed to be a quotient group.
The action is right translation, `(g*F)(x) = F(x*g)`.
`compactInducedMap H T` is the existing intertwiner given by
postcomposition, so its underlying function has value `T(F(x))`.
These are ordinary, unnormalized subgroup induction conventions.

The topology on `H` is its subspace topology. The coefficient modules
carry no topology, norm, completeness or dimension assumption. The target
has no compactness hypothesis on `H \ G`, admissibility or finite-length
hypothesis, selected lift, section, splitting or exactness assumption.
It introduces no replacement function space, map or functor.

## Relation to the existing targets

[`Induction.StructuralStatement`](StructuralStatement.md) contains
`InductionExactnessClause`, whose compact-induction conjunct gives
injectivity, range equals kernel, and surjectivity for the actual induced
maps. This proposition isolates only its compact-surjectivity conclusion.
The aggregate statement and all existing pairs remain unchanged.

The aggregate hypotheses imply compact-open cofinality. They assume
smoothness of the middle representation `sigma`; when `T` is surjective,
`tau` is also smooth: choose a preimage of a vector and use the same open
fixing subgroup after applying the intertwiner. Thus the explicit
smoothness hypothesis on `tau` is compatible with extracting the compact
surjectivity part of the aggregate clause. This explanation is mathematical;
this file formalizes neither that extraction nor any exactness proof.

[`Induction.SurjectivityStatement`](SurjectivityStatement.md) separately
states `SmoothInductionSurjectivityStatement` for the same hypotheses,
with conclusion `Function.Surjective (smoothInducedMap H T)`.
The present statement concerns the compact subspaces.

## Original source and scope

I. N. Bernstein and A. V. Zelevinsky, *Induced representations of reductive
p-adic groups I*, Ann. Sci. ÉNS (4) 10 (1977), 441–472.
The following original passages were read; the induction formulas and
exactness claim were also checked visually.

- §1.1, printed p.442 / PDF p.3: an `l`-group is Hausdorff and every
  identity neighbourhood contains an open compact subgroup.
- §1.2, printed p.443 / PDF p.4: coefficients are complex vector spaces
  without topology, and algebraic representations are smooth
  representations with open vector stabilizers.
- §1.8(a), printed p.444 / PDF p.5: the induced functions have covariance
  `f(umg) = theta(u) mod_U(m)^(1/2) rho(m)(f(g))`, one open right
  stabilizer, and the right-translation action. Compact induction is the
  subspace of functions compactly supported modulo `P = MU`.
- The trivial-`U` remark and §1.9(a), printed p.445 / PDF p.6:
  `U = {e}` gives ordinary induction without a factor, and both induction
  functors are exact. The paper refers to its reference [1], chapter I,
  for the proof; that reference was not read for this statement.

Literature ID: `bernstein-zelevinsky-1977-induced-i`.
Content SHA-256:
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
Retained source:
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`.
No source-specific errata note was present in project or pinned Library notes.

Specialize §1.8 to the trivial subgroup `U`, the trivial character `theta`,
and `M = H`. Then `MU = H` is closed and the normalizing factor is one.
The resulting compact-induction space and action are precisely the existing
`CompactFunctions H sigma` and `compactInduced H sigma`. Its morphism map
is postcomposition, `compactInducedMap H T`. For smooth representations,
the kernel of a surjective intertwiner is smooth, so exactness of compact
induction in §1.9(a) gives its surjectivity on `T` in the source's scope.

The ambient hypothesis here is explicitly weaker than the source's
compact-open neighbourhood-basis hypothesis: it asks for a compact open
subgroup inside each open subgroup, rather than inside every identity
neighbourhood. The source's hypothesis implies this one by applying it to
the open identity neighbourhood `K`. This is the same weakening used in
the published smooth-surjectivity statement. It is an internal
generalization of the stated source consequence, rather than an assertion
that BZ77 states the broader hypothesis.

To explain why that weakening fits the intended route, first lift a compact
target function by smooth surjectivity under compact-open cofinality.
The target's projected nonzero support is open as well as compact:
covariance saturates its nonzero support, local constancy makes that
support open, and the quotient topology transfers openness to the quotient.
Cut the smooth lift off on that set. Such a cutoff preserves covariance,
has a uniform open right stabilizer, and has compact projected support.
Postcomposition remains the target, since the target vanishes off its
own support. The existing `smoothQuotientCutoff` and
`quotientSupport_smoothQuotientCutoff` in
[`Induction.CompactQuotientCutoff`](CompactQuotientCutoff.md) provide the
cutoff and its support formula. This is a route for the separate proof,
not a formal proof in this pair; no cutoff or lifting hypothesis is added
to the proposition.


## Development check

In environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`), the module compiled
with no errors or warnings. Proposition inspection succeeded with
`statement_returns_prop: true` and independent universe parameters
`uG`, `uV`, `uW`. The inspected axiom closure contained only `propext`,
`Classical.choice` and `Quot.sound`. These are development checks;
independent semantic acceptance and publication remain separate.
