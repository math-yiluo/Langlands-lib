# Disjointness from the actual inertia fixed field

Authors: Worker 104 (Lean proof and documentation) and Worker 366
(finite-stage proof-route specification in the task).

## Exact result

`Langlands.PadicField.totallyRamifiedInertiaDisjoint.{u}` proves exactly the
published proposition
`Langlands.PadicField.TotallyRamifiedInertiaDisjoint.{u}`, imported unchanged
from `Langlands.Galois.Local.TotalRamifiedInertiaDisjointStatement`. It has
no outer hypotheses.

For every prime `p`, every `F : PadicField.{u} p`, and every
`D : Langlands.LocalClassField.FiniteIntermediateExtension F.Carrier` with
`IsGalois F.Carrier D.field`, the canonical absolute-index equality

```lean
(D.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex =
  Module.finrank F.Carrier D.field *
    F.canonicalTopologicalData.ramificationIndex
```

implies `D.field.LinearDisjoint U`, where

```lean
U := IntermediateField.fixedField (F.absoluteInertia F.canonicalTopologicalData)
```

The universe `u` is arbitrary, and every finite degree, including one, is
retained. The theorem uses the given intermediate fields in the existing
`AlgebraicClosure F.Carrier`. The finrank, Galois condition and linear
disjointness all use their inherited scalar maps. The field `U` is the
fixed field of the actual canonical absolute inertia subgroup and is
allowed to be infinite over `F.Carrier`.

## Finite-support passage

The proof changes the intermediate-field linear-disjointness goal to the
equivalent subalgebra goal with
`IntermediateField.linearDisjoint_iff'`. The inclusion of `U.toSubalgebra`
into the algebraic closure is its existing subtype map. Integrality of the
algebraic closure over `F.Carrier` descends along that injective map by
`Algebra.IsIntegral.of_injective`. This supplies the integrality hypothesis
of Mathlib's
`Subalgebra.LinearDisjoint.of_linearDisjoint_finite_right`.

That lemma reduces the goal to every subalgebra
`B : Subalgebra F.Carrier (AlgebraicClosure F.Carrier)` such that
`B ≤ U.toSubalgebra` and `Module.Finite F.Carrier B`.
`Submodule.FG.of_finite` supplies a finite set `s` of elements of the
ambient closure with

```lean
Submodule.span F.Carrier (s : Set (AlgebraicClosure F.Carrier)) = B.toSubmodule.
```

Each element of `s` belongs to `B`, hence to `U`.
The second clause of the published theorem
`Langlands.PadicField.inertiaFixedFieldUnramifiedExhaustion p F` therefore
gives a finite intermediate extension `E` with `IsGalois F.Carrier E.field`,
the index equality `e_abs(F) = e_abs(E)`, and containment of `s` in
`E.field`. Rewriting by the spanning equality and applying
`Submodule.span_le` proves `B.toSubmodule ≤ E.field.toSubalgebra.toSubmodule`.
Thus all of `B`, not just its chosen generators, lies in this one stage.

The first conjunct of the published theorem
`Langlands.LocalClassField.totalUnramifiedCompositum p F D E` now proves
`D.field.LinearDisjoint E.field`. Its inputs are the given total
ramification equality for `D` and the symmetry of the equality from
exhaustion. Changing this finite-stage conclusion to subalgebra
disjointness, `Submodule.LinearDisjoint.of_le_right_of_flat` restricts its
right argument to `B`. The required flatness holds because the base is a
field. The finite-right reduction then concludes disjointness from all of
`U`.

The Mathlib reduction provides the finite-support argument on tensor
products. Its implementation places any two tensors to be compared in
the image of a finitely generated submodule on the right, adjoins its
finitely many generators to form a finite module subalgebra using
integrality, and uses injectivity of the multiplication map for that
subalgebra. Our proof supplies injectivity through containment in the
finite unramified stage. It does not infer disjointness merely from a
trivial intersection, and it imposes no finite-dimensionality on `U`.

## Dependencies and provenance

The module imports the unchanged statement and the published proof modules
`Langlands.Galois.Local.InertiaFixedFieldUnramifiedProof` and
`Langlands.ClassFieldTheory.Local.TotalUnramifiedCompositumProof`. Their
existing import closures supply Mathlib's intermediate-field, subalgebra,
integrality, finite-generation and linear-disjointness APIs. The finite
arithmetic and inertia identification are used through those published
theorems. The present proof adds the passage to the generally infinite
fixed field; it does not reprove finite compositum arithmetic.

The original source context is Jean-Pierre Serre, *Local Fields*, translated
by Marvin Jay Greenberg, Springer GTM 67 (1979), registered as
`serre-1979-local-fields`, file
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
Worker 104 read Chapter V, section 4, printed pages 87–88/PDF pages 94–95.
Page 87 proves finite total/unramified disjointness and identifies the
finite compositum with the tensor product; page 88 passes to the direct
limit of unramified fields. Although page 88 has specialized to cyclic
prime degree for its norm argument, the tensor-product passage follows
from the preceding finite disjointness for general finite degree.
The exact proposition here is a derived p-adic formulation using
canonical absolute indices and the actual inertia fixed field, whose
finite exhaustion is supplied by the published input theorem.

Worker 104 also read the Local Fields entries in the official *Corrections
to J-P. Serre's books* (2019), PDF pages 2–3, registered as
`serre-book-corrections-2019`, file
`/home/taskhub/pilot/literature/Jean-Pierre Serre — Corrections to J-P. Serre's books (2019).pdf`,
SHA256 `b76739179d067850770081597a8e9ced68135ebf80678876605f471297a4fee5`.
They contain no correction to the cited pages 87–88. No project errata
entry for this source was present in the public notes when checked.

No unpublished Lean draft was reused. Worker 366 supplied the finite-stage
route and suggested the finite-subalgebra reduction in the task context.
The proof assumes no forward-disjointness proposition, norm theorem,
local reciprocity, class formation or cohomology vanishing. Those later
arithmetic conclusions are outside this module.
