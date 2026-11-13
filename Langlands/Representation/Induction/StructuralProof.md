# Proof of the structural properties of induction

Worker 5459 proves the published proposition
`Langlands.Induction.StructuralStatement` (module
[`StructuralStatement`](StructuralStatement.md)) as
`Langlands.Induction.structuralStatement_holds`. The statement pair and all
imported pairs are unchanged. This module adds no hypothesis, axiom or
assumed theorem field.

## Exact target

```lean
theorem structuralStatement_holds :
    StructuralStatement (G := G) (U := U) (V := V) (W := W)
```

The variable block is exactly the one of the statement module: a group
`G : Type uG` with a topology, and complex modules `U : Type uU`,
`V : Type uV` and `W : Type uW`, with four independent universes. The
remaining hypotheses come from the proposition itself. These are
`IsTopologicalGroup G`, `T2Space G`, the compact-open neighbourhood basis of
the identity, and a closed subgroup `H`. The declaration's axioms are
`propext`, `Classical.choice` and `Quot.sound`.

The final proof introduces these hypotheses and derives two consequences of
the neighbourhood basis:

- cofinality: every open subgroup `K` contains a compact open subgroup `L`,
  by applying the basis to the open set `K`;
- local compactness (`locallyCompactSpace_of_compactOpenBasis`): applying the
  basis to `Set.univ` gives a compact open subgroup, which is a compact
  neighbourhood of `1`. Mathlib's
  `IsCompact.locallyCompactSpace_of_mem_nhds_of_group` then gives
  `LocallyCompactSpace G`.

It then assembles the seven clauses below. Clauses 3 and 4 were already
proved in the Library and are reused as they stand.

## Clause 1: Frobenius reciprocity

`smoothFrobeniusEquiv` is an explicit complex-linear equivalence:

- forward map `frobeniusRestrict`: `f ↦ (u ↦ f(u)(1))`. It is an
  `H`-intertwiner because `f(rho(h) u)(1) = f(u)(1*h) = f(u)(h*1) =
  sigma(h)(f(u)(1))`, using `f`'s `G`-equivariance and covariance
  (`eval_covariant`);
- inverse `frobeniusInverse`: an `H`-intertwiner `φ` gives
  `u ↦ (x ↦ φ(rho(x) u))`. Covariance follows from the intertwining property
  of `φ`. The open stabilizer of `u` (from `IsSmooth rho`) fixes this
  function on the right. It is built with the published constructor
  `smoothFunctionOf`. Right translation matches `rho`, so the map is a
  `G`-intertwiner.

The two composites are the identity: `f(rho(x) u)(1) = f(u)(x)` and
`φ(rho(1) u) = φ(u)`. The formula `e f u = eval H sigma (f u) 1` holds by
`rfl`. Only smoothness of `rho` is used.

## Clause 2: exactness

Let `0 → rho → sigma → tau → 0` be exact, with `sigma` smooth.
`InductionExactnessClause` does not assume that `tau` is smooth. The proof
derives it: each `p(v)` is fixed by an open subgroup fixing `v`.

- Injectivity of both induced maps is pointwise injectivity of `i`.
- Image equals kernel, for both maps. Inclusion: `p ∘ i = 0` pointwise.
  Reverse inclusion: if `p ∘ F = 0`, every value `F(x)` has a preimage under
  `i`. `injectiveLift` picks these preimages with `Classical.choose`.
  Injectivity of `i` makes the resulting function covariant and invariant
  under the same open subgroup as `F`. Its nonzero support equals that of
  `F` (`support_injectiveLift`), so `injectiveCompactLift` keeps compact
  quotient support. Then `i ∘ lift = F` pointwise.
- Surjectivity: the published `smoothInductionSurjectivity`
  ([`SurjectivityProof`](SurjectivityProof.md)) and
  `compactInductionSurjectivity`
  ([`CompactSurjectivityProof`](CompactSurjectivityProof.md)). They are
  applied with the cofinality consequence, the closedness of `H`, and the
  smoothness of `sigma` and of `tau`.

## Clause 3: compact quotient

This is the published `compactQuotientClause_holds`
([`CompactQuotientProof`](CompactQuotientProof.md)).

## Clause 4: character twists

This is the published `inductionTwist`
([`CharacterTwistProof`](CharacterTwistProof.md)).

## Clause 5: central action

For central `z` (which lies in `H`), `f(x*z) = f(z*x) = sigma(z)(f(x)) =
chi(z) f(x)`. This uses `Subgroup.mem_center_iff`, covariance and the
hypothesis on `sigma`. Function extensionality
(`structural_smooth_ext`, resp. the published `compactFunctions_ext`) gives
the equation for smooth and for compact induction.

## Clause 6: induction in stages

The equivalences are the published `smoothStagesEquiv`
([`SmoothTransitivity`](SmoothTransitivity.md)) and `compactStagesEquiv`
([`CompactTransitivityProof`](CompactTransitivityProof.md)). The compact
version uses closedness of `H` and `P` and the derived
`LocallyCompactSpace G`. Both function formulas `(e F)(x) = F(x)(1)` hold by
`rfl`.

## Clause 7: the open-subgroup adjunction

`openSubgroupAdjunctionEquiv` uses the published constructions of
[`OpenAdjunction`](OpenAdjunction.md):

- the forward map is `T ↦ (resIntertwining H tau T).comp unitMap`;
- the inverse is the coset sum `cosetSum`.

The inverse laws are the published `cosetSum_resIntertwining_comp`,
`cosetSum_unitMap` and `cosetSum_comp_unitMap`.

Let `f` vanish outside `H`. The support formula `e T (f(1)) = T f` reduces
to `unitMap (f(1)) = f`, which holds pointwise:

- on `x ∈ H`, `eval_unitFunction` gives `sigma(x)(f(1))`, and covariance
  gives `f(x) = sigma(x)(f(1))`;
- off `H`, both sides are zero.

Smoothness of `tau` is not needed.

## Provenance

The task cites Renard III.2.2–III.2.8 for these properties. The statement's
Markdown fixes the correspondence with the original literature, namely
Bernstein–Zelevinsky 1977, §1.9, in its unnormalized specialization. This
proof makes no further literature claim. Its route is the direct one
described above and uses no Haar measure. The new declarations in this
module are `structural_smooth_ext`, the Frobenius maps, the exactness lifts,
the clause theorems, `openSubgroupAdjunctionEquiv`,
`locallyCompactSpace_of_compactOpenBasis` and the final theorem.

The local compactness helper is imported from `CompactTransitivityProof`, where the identical compact-neighbourhood argument is shared with compact induction in stages.
