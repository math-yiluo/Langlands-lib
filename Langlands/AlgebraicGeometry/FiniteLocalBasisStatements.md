# Finite local basis and rank targets for scheme modules

This module defines three propositions for arbitrary schemes in universe `u`.
It proves none of them. Each proposition quantifies all its schemes, morphisms
and modules, and combines a finite-local-basis implication with the
corresponding implication for every specified natural-number rank.

The variable-rank condition used throughout is exactly

```lean
∃ q : SheafOfModules.LocalGeneratorsData.{u} M,
  q.IsLocallyFreeData ∧ q.IsFiniteType
```

Here `q` is a single covering family with generating sections on the
restrictions of `M`. The first condition makes each map from the free sheaf on
those generators an isomorphism. The second makes each generator index type
finite. Their sizes may vary between members of the cover. Forgetting either
condition supplies, respectively, Mathlib `SheafOfModules.IsFiniteType` or
`SheafOfModules.IsLocallyFree`. Thus no separate theorem extracting finite
bases from unrelated covers is needed to use these targets.

The fixed-rank condition is the existing
`Langlands.Scheme.Modules.IsLocallyFreeOfRank M n`: it requires local bases
whose index types are equivalent to `Fin n`. None of the propositions
asserts existence of one global constant rank on a disconnected scheme or
uniqueness of rank on an empty scheme. They assume no quasi-compactness,
connectedness, nonemptiness or affineness.

## The three combined targets

`Langlands.Scheme.SmoothDifferentialsFiniteLocalBasisRankStatement` quantifies
every `f : X ⟶ S`. Its first clause asserts that `Smooth f` implies the
finite-local-basis condition for the constructed
`Langlands.Scheme.relativeDifferentials f`. Its second clause asserts, for
every `n : ℕ`, that `SmoothOfRelativeDimension n f` implies
`IsLocallyFreeOfRank (relativeDifferentials f) n`. These are Mathlib's
geometric smoothness predicates. In particular, the relative-dimension
predicate uses standard-smooth affine neighborhoods of each point; it is
not an assumed rank witness for this differential sheaf.

`Langlands.Scheme.Modules.PullbackFiniteLocalBasisRankStatement` quantifies
every `f : X ⟶ Y` and `M : Y.Modules`. It asserts preservation of the
finite-local-basis condition, and separately of every fixed rank, by
`(AlgebraicGeometry.Scheme.Modules.pullback f).obj M`. This is the actual
module-sheaf pullback, with no hypothesis on the morphism.

`Langlands.Scheme.Modules.DualFiniteLocalBasisRankStatement` quantifies
every `M : X.Modules`. It asserts preservation of the finite-local-basis
condition, and separately of every fixed rank, by
`Langlands.Scheme.Modules.dual M`. This is the existing internal Hom into
the structure module. Its sections are morphisms of restricted sheaves on
over-categories, compatible on smaller opens. It is not the pointwise
linear dual of each section module.

## Sources and derived provenance

The smooth differential target is an internal formulation of the Stacks
Project, Lemma 29.35.12 (02G1): smooth morphisms have finite locally free
differentials, with rank at a point equal to the dimension of the fibre
there. Definition 29.35.13 (02G2) then defines smoothness of relative
dimension `n` using constant differential rank. Mathlib instead implements
the standard-smooth affine-neighborhood criterion. Proving the bridge from
that criterion to the actual sheafification-based differential construction
is part of the later proof obligation. The statement does not obtain its
rank conclusion by adopting the source's rank-based definition as a
hypothesis.

Definition 17.14.1 (01C6), parts (2) and (3), gives the local finite-basis and
fixed-rank meanings. Lemma 17.14.3 (01C8) states preservation of local
freeness by pullback. The finite-basis and same-rank refinements here are
derived by pulling back each local free presentation: pullback carries the
structure sheaf to the structure sheaf and preserves its direct sums,
retaining the finite index set. The cited lemma itself does not explicitly
state these two refinements.

The dual target is an elementary derived consequence of finite dual bases
and the internal-Hom construction in the opening of Section 17.22 (01CM).
On an open with a finite basis, the coordinate maps into the structure
sheaf form its dual basis. They are morphisms of restricted sheaves and
restrict compatibly on smaller opens, as required by the actual
`ModuleDual` construction. Finiteness identifies the resulting finite
product with the finite direct sum, preserving the number of generators.
Section 17.22 supplies the definition of internal Hom; we do not attribute
this preservation target to a stronger theorem quoted from that section.

Retained originals, read for these locators:

- `stacks-smooth-differential-rank-2026-10-22`, folder SHA256
  `a20ebb3b9b37ee166cb66decf78eed5aae44e5ed93634cf911eee19d224c1bc5`,
  `01V4.html`, Lemma 29.35.12 (02G1), its proof, and Definition 29.35.13
  (02G2).
- `stacks-local-freeness-invertibility-sections-2026-10-21`, folder SHA256
  `6d1641a9deb284be889ee6e2630a2be6e57cc5985c80af2c9da7d17543ed0785`,
  `01C5.html`, Definition 17.14.1 (01C6), parts (1)–(3), and
  Lemma 17.14.3 (01C8).
- `stacks-relative-differentials-internal-hom-2026-10-21`, folder SHA256
  `9c075370ba97d8876785c5486425c6c661765e747452c026583f4dc51f1e1133`,
  `01CM.html`, opening internal-Hom definition and scalar action.

## Intended use and scope

These are three separate targets for later exact-target proofs. The smooth
proof can reuse the canonical affine-chart differential comparison assigned
in task `586717a0-e6c1-4905-a566-e913537ab5c8`, together with Mathlib's
standard-smooth Kähler differential bases and ranks.

For an abelian scheme, the intended later assembly applies smoothness to
its structure morphism, pulls the resulting bases back by its identity
section, and dualizes. This module leaves the existing
`Langlands.AbelianScheme.LieLocalFreenessRankStatement` and all imported
definitions unchanged. The two transport targets alone do not prove that
Lie statement. No arbitrary-module dual/pullback base-change isomorphism
is asserted here.

Worker 124 authored this statement package using Worker 309's explicit
single-cover formulation and decomposition, with Worker 132's recorded
source and interface analysis.
