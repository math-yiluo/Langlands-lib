# Compact clopen neighborhoods and cutoffs on a left quotient

Worker 128 constructs compact clopen neighborhoods and compactly induced
function cutoffs in `Langlands.Induction`. This is internal derived
infrastructure for finite partition gluing, using the existing actual quotient
`LeftQuotient P = Quotient (QuotientGroup.rightRel P)`. Its points are left
cosets `P x`, and `quotientMap P x` is the existing projection. No quotient group
structure or normality of `P` is used. The module does not assert a local section
or a closed-orbit extension theorem.

## Compact clopen neighborhoods

For a nonarchimedean locally compact group `G`, a subgroup `P` closed in `G`,
a point `y : LeftQuotient P`, and an open set `U` containing `y`,
`compactClopenQuotientNeighborhood P hP y U hU hy` returns

```lean
{C : Set (LeftQuotient P) // IsCompact C ∧ IsClopen C ∧ y ∈ C ∧ C ⊆ U}
```

`compactClopenQuotientNeighborhood_spec` exposes these four properties.
`exists_compactClopen_quotientNeighborhood` supplies the corresponding
existence lemma directly. These declarations require `Group G`,
`TopologicalSpace G`, `NonarchimedeanGroup G`, and `LocallyCompactSpace G`;
`NonarchimedeanGroup` supplies continuity of the group operations. No separate
ambient Hausdorff assumption is needed, so the requested Hausdorff case is
included. The closedness assumption on `P` supplies the Hausdorff quotient.

Choose a representative `x` of `y`. The inverse image of `U` under
`k ↦ quotientMap P (x * k)` is an identity neighborhood. The published
`Langlands.compactOpenSubgroupBasis` gives a compact open subgroup `K` inside
it. Take `C` to be the image of `x K` under the quotient projection. Continuity
makes this image compact, and openness of translation and of the quotient map
makes it open. The quotient is Hausdorff by
`QuotientIntegration.leftQuotient_t2Space P hP`, so compactness also gives
closedness. The identity belongs to `K`, establishing membership of `y`, and
the choice of `K` gives containment in `U`. The operation selects one of these
sets by classical choice; it assumes no zero-dimensional quotient instance.

## The uniform open stabilizer

For any topological group and any subgroup `P`,
`quotientRight_one` and `quotientRight_mul` prove the identity and composition
laws of the existing right quotient action. Its composition law is

```lean
quotientRight P (g * h) y = quotientRight P h (quotientRight P g y)
```

`continuous_quotientRight_joint` proves joint continuity in `(g, y)` by
precomposing with the product of the identity and the actual open quotient
map. On representatives this is the continuous map `(g, x) ↦ [x * g]`.

`quotientSetStabilizer P C` is the actual subgroup whose elements satisfy
`∀ y, quotientRight P g y ∈ C ↔ y ∈ C`. Its multiplication and inverse laws
follow from the right action laws. The two membership lemmas for
`quotientSetStabilizer` and `compactQuotientOpenStabilizer` expose precisely
this criterion.

For compact open `C`, `quotientSetStabilizer_isOpen` proves this subgroup open.
For every `y ∈ C`, joint continuity and openness give a neighborhood of
`(1, y)` whose translates lie in `C`. The pinned Mathlib lemma
`IsCompact.eventually_forall_of_forall_eventually` makes this uniform over
all of `C`. Intersect the resulting identity neighborhood with its inverse.
Both `g` and `g⁻¹` then send `C` into itself; applying the inverse proves the
membership equivalence for every quotient point, including points outside
`C`. Thus the subgroup contains an identity neighborhood and is open.
`compactQuotientOpenStabilizer P C hc ho` bundles this subgroup with its
proved openness. This argument needs neither closedness of `P`, local
compactness of `G`, nor clopenness beyond the given compactness and openness
of `C`.

## Function cutoffs and exact support

The coefficient ring `R`, group `G`, and module `V` have independent universes
`uR`, `uG`, and `uV`. The cutoff constructions require a commutative ring `R`,
an additive commutative group `V` with an `R`-module structure, a topological
group `G`, an arbitrary subgroup `P`, and an actual representation
`σ : Representation R P V`. In particular, they apply over `ℂ` with independent
group and coefficient-module universes. They require no topology on `V` and
no smoothness assumption on `σ`.

For a compact open quotient set `C`,
`smoothQuotientCutoff P σ C hc ho f` cuts off a `SmoothFunctions P σ` element.
It is constructed using `smoothFunctionOf` and has evaluation

```lean
if quotientMap P x ∈ C then eval P σ f x else 0
```

The theorem `eval_smoothQuotientCutoff` gives this formula. Left multiplication
by `P` leaves the quotient class unchanged, so the original covariance and
linearity of `σ p` prove covariance of the cutoff. Choose the input function's
uniform open right stabilizer and intersect it with
`compactQuotientOpenStabilizer P C hc ho`. Every element of this intersection
preserves both the quotient membership condition and the input value, hence
fixes the entire cutoff function. This proves smoothness in the existing
uniform-stabilizer sense, rather than merely pointwise local constancy.

The requested operation is

```lean
compactQuotientCutoff (P : Subgroup G) (σ : Representation R P V)
  (C : Set (LeftQuotient P)) (hc : IsCompact C) (hcl : IsClopen C)
  (f : CompactFunctions P σ) : CompactFunctions P σ
```

`eval_compactQuotientCutoff` gives the displayed formula with `f.val` as the
input and `(compactQuotientCutoff P σ C hc hcl f).val` as the output. The
support lemmas `quotientSupport_smoothQuotientCutoff` and
`quotientSupport_compactQuotientCutoff` prove the exact equality of projected
nonzero supports with `C ∩ quotientSupport P (eval P σ f)` or its `f.val`
version, respectively. This follows directly from the conditional formula and
the image definition of projected support. The theorem
`quotientSupport_compactQuotientCutoff_subset` extracts containment in `C`
and in the original projected support.

The output's projected support is closed by the published
`isClosed_quotientSupport` theorem for actual smooth covariant functions.
Its containment in compact `C` proves actual compactness, which supplies the
`CompactFunctions` certificate. The clopen interface matches the gluing
application; internally its openness suffices together with compactness.
Finally, `compactQuotientCutoff_uniform_stabilizer` explicitly exposes a
single open subgroup fixing the whole output under right translation.

## Provenance and scope

These are internal constructions derived from existing Library definitions
and pinned Mathlib, not a transcription of a new literature statement.
The project imports are `Analysis.Local.QuotientTopology`,
`Topology.CompactOpen.NeighborhoodBasis`, and
`Representation.Induction.CompactQuotientProof`; the latter imports the
existing induction definitions. Quotient openness and Hausdorffness come
from the first module, the compact open subgroup basis from the second, and
covariance plus closedness of projected support from the third.

The compactness argument for openness of the setwise stabilizer adapts the
method in the published `Representation.Hecke.CommonInvarianceProof`:
uniformize a continuous local condition on a compact set and then also use
inverse elements. No private helper from that module is imported. The
Mathlib ingredients are `Topology/Compactness/Compact.lean`, the product and
continuity API for open quotient maps, and `Subgroup.isOpen_of_mem_nhds` in
`Topology/Algebra/OpenSubgroup.lean`. No additional proposition-only
prerequisite, assumed local section, or new axiom is introduced.

Prepared environment: `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0,
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`. Compilation is
development evidence; independent semantic review and publication are
separate requirements.
