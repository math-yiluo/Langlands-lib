# Surjectivity of smooth induction from a closed subgroup

Worker 380 states
`Langlands.Induction.SmoothInductionSurjectivityStatement.{uG,uV,uW}`.
This is a proposition definition and a target for a separate proof.
Defining it does not assume its truth, and this file proves nothing.

## The statement

The proposition quantifies, inside its own telescope, over:

1. a type `G : Type uG` with `Group`, `TopologicalSpace`,
   `IsTopologicalGroup` and `T2Space` instances;
2. the hypothesis that compact open subgroups are cofinal among open
   subgroups:

   `∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
     IsCompact (L : Set G) ∧ L.toSubgroup ≤ K.toSubgroup`;
3. a subgroup `P : Subgroup G` with `IsClosed (P : Set G)`;
4. complex vector spaces `V : Type uV` and `W : Type uW`, as additive
   commutative groups with `Module ℂ` structures;
5. representations `sigma : Representation ℂ P V` and
   `tau : Representation ℂ P W`, with `IsSmooth sigma` and `IsSmooth tau`;
6. an intertwiner `q : sigma.IntertwiningMap tau` with
   `Function.Surjective q`.

Its conclusion is `Function.Surjective (smoothInducedMap P q)`.

So every smooth induced function for `tau` is the pointwise image under `q`
of a smooth induced function for `sigma`.
The topology on `P` is Mathlib's subspace topology. Smoothness of `sigma` and
`tau` therefore means that every vector is fixed by an open subgroup of `P`.
The three universes are independent. The induced function spaces live in
`Type (max uG uV)` and `Type (max uG uW)`. The coefficient spaces carry no
topology. There is no hypothesis of compact quotient `P \ G`, admissibility,
finite dimension or finite length. No lift, section or splitting is supplied,
and no proposition-valued data replaces a hypothesis.

All objects are the existing ones imported from
`Langlands.Representation.Induction.Definitions`:

- `SmoothFunctions P sigma` consists of Mathlib's covariant functions
  (`Representation.coindV P.subtype sigma`), with `f(p*x) = sigma(p)(f(x))`.
  Each function also has one open subgroup of `G` fixing it under right
  translation.
- `smoothInduced P sigma` is right translation, `(g*f)(x) = f(x*g)`.
- `smoothInducedMap P q` is postcomposition `f ↦ q ∘ f`, restricted to these
  smooth functions. It is the actual map underlying `smoothInductionFunctor`.

This is unnormalized induction, with no modulus factor.
`IsSmooth` is the published predicate from
`Langlands.Representation.Smooth.Definitions`.
The file adds only the proposition, with no new construction or substitute
functor.

## The compact-open cofinality hypothesis

The hypothesis says that every open subgroup of `G` contains a compact open
subgroup. It is implied by the `l`-group hypothesis of Bernstein–Zelevinsky
§1.1: every neighbourhood of the identity contains an open compact subgroup.
To see this, apply that hypothesis to the open neighbourhood `K` of the
identity. In particular, the neighbourhood-basis hypothesis of
`Induction.StructuralStatement` implies the present one.

The weaker cofinality form is what the lifting route below uses.
A smooth induced function has some open right stabilizer, and the route
needs a compact open subgroup inside it. Applied to `K = ⊤`, the hypothesis
gives a compact open subgroup of `G`, so `G` is locally compact.

The Hausdorff hypothesis is retained as requested by the task and as in
Bernstein–Zelevinsky's definition. The route below does not use it: a closed
subset of a compact set is compact in any topological space.

## Relation to `InductionExactnessClause`

`Induction.InductionExactnessClause` in
`Langlands.Representation.Induction.StructuralStatement` is unchanged by this
file. That pair is also unchanged. Under the aggregate hypotheses of
`Induction.StructuralStatement`, the clause states full exactness of both
smooth and compact induction.

The present proposition isolates only one of its six conjuncts: surjectivity
of the smooth induced map. Its hypotheses are explicit sufficient topological
ones. Smoothness of `tau` is assumed as a separate hypothesis. The
mathematical point below explains why this is no essential restriction.
The image of a vector fixed by an open subgroup is fixed by the same subgroup,
so `tau` is smooth whenever `sigma` is smooth and `q` is surjective.
Together with the implication of cofinality noted above, the new proposition
mathematically yields the smooth-surjectivity conjunct of the clause for a
closed subgroup under the aggregate hypotheses. That derivation is explanatory
and is not formalized here. Injectivity, the range–kernel equality and every
compact-induction conjunct are not part of this statement.

## Original source

I. N. Bernstein and A. V. Zelevinsky, *Induced representations of reductive
p-adic groups I*, Ann. Sci. ÉNS (4) 10 (1977), 441–472.
These passages were read in the original, with the formulas checked visually:

- §1.1, printed page 442 / PDF page 3. A Hausdorff topological group is an
  `l`-group if every neighbourhood of the identity contains an open compact
  subgroup.
- §1.2, printed page 443 / PDF page 4. Representations are on complex vector
  spaces with no topology. `Alg G` is the category of algebraic, that is
  smooth, representations: every vector has an open stabilizer.
- §1.8(a), printed page 444 / PDF page 5. For closed subgroups `M`, `U` with
  `M` normalising `U`, `M ∩ U = {e}`, closed `P = MU`, and a character
  `θ` of `U`, the space `I(L)` consists of functions `f : G → L` with
  (1) `f(umg) = θ(u) mod_U^{1/2}(m) ρ(m)(f(g))` and
  (2) an open subgroup `K_f` with `f(gk) = f(g)`. `G` acts by right
  translation; this gives `I_{U,θ}(ρ)`.
- The remark at the top of printed page 445 / PDF page 6. If `U = {e}`, the
  functors `I`, `i` become ordinary induction without any factor.
- §1.9(a), printed page 445 / PDF page 6. The functors `I_{U,θ}` and
  `i_{U,θ}` are exact. The paper refers to its reference [1], chapter I,
  for the proof; that reference was not read for this statement.

Literature ID: `bernstein-zelevinsky-1977-induced-i`.
PDF SHA-256:
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
Retained file:
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`.

**Correspondence.** Specialize §1.8 to `U = {e}`, the trivial character
`θ`, and `M = P`, this file's closed subgroup. Then `MU = P` is closed, and
the factor `θ(u) mod_U^{1/2}(m)` is identically one. Condition (1) becomes
`f(pg) = sigma(p)(f(g))`, and condition (2) is the one open right stabilizer
of `SmoothFunctions`. The action is the same right translation, so
`I_{{e},1}(sigma)` is `smoothInduced P sigma`. Its morphism map is
postcomposition, which is `smoothInducedMap`.

A surjective morphism `q : sigma → tau` in `Alg P` has kernel in `Alg P`,
since subrepresentations of smooth representations are smooth. Thus
`ker q → sigma → tau → 0` is short exact. Exactness of `I` in §1.9(a) then
gives surjectivity of `I(q)`, which is the present conclusion. The source works
with `l`-groups. The present ambient hypothesis is the weaker cofinality
condition explained above, with closedness of `P` kept explicitly. The
proposition records only this surjectivity consequence of §1.9(a), not full
exactness and not the compact-induction part.

## Fixed-vector lifting route (not a proof)

The following route explains the hypotheses; no part of it is formalized here.

Let `f` be a smooth induced function for `tau`, fixed on the right by an open
subgroup `K`. By cofinality, choose a compact open subgroup `L ≤ K`; then `f` is
also right `L`-invariant. Fix `g` in `G`. The subgroup `P ∩ gLg⁻¹` is open in
`P`, and it is compact because `P` is closed and `gLg⁻¹` is compact.
Covariance and right `L`-invariance show that `f(g)` is fixed by
`P ∩ gLg⁻¹`. This is the published `Induction.eval_mem_fixedVectors`, with
`Induction.conjOpenSubgroup`, in
`Langlands.Representation.Induction.CompactQuotientProof`.

Since `sigma` and `tau` are smooth and `q` is surjective, the fixed vectors of
this compact open subgroup lift. Averaging over the finite quotient by the
stabilizer of a preimage gives a fixed preimage. This is the published
`Compact.fixedVectorSurjectivity` in
`Langlands.Representation.Compact.SurjectivityProof`, applied to the group `P`.
Here division by finite cardinalities in `ℂ` is used.

Choose one representative `g` in each double coset `P g L` and a fixed lift
`v_g` of `f(g)`. Define `F(p g l) = sigma(p)(v_g)`. This is well defined
because `v_g` is fixed by `P ∩ gLg⁻¹`. `F` is covariant, fixed on the right
by `L`, and satisfies `q ∘ F = f`. No compactness of `P \ G` is used, since
infinitely many double cosets are allowed.

## Development evidence

The pair was checked in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`,
with Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Compilation had no errors or warnings. Inspection reported the declaration's
universe parameters `uG`, `uV`, `uW` and `statement_returns_prop: true`. The
only axioms reported were `propext`, `Classical.choice` and `Quot.sound`.
Compilation and inspection are development evidence; independent semantic
review and publication remain separate.
