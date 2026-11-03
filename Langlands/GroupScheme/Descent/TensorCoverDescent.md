# Actual central-isogeny descent from a tensor cover datum

Let `k` and `L` be fields in arbitrary universe `u`. Suppose a finite
indexing type `J : Type v`, an actual algebra equivalence
`e : L ⊗[k] L ≃ₐ[L] (J → L)` and specified `k`-automorphisms `s i` satisfy
`e (a ⊗ b) i = a * s i b`. Let `G` be an actual group scheme over `k`,
and let `π : C → G_L` be a supplied simply connected cover, including its
full central-cover universal property.

`IsSimplyConnectedCover.tensorDescentSolution` constructs an actual group
scheme over `k` whose pullback is identified with `C`. Its input datum is
the tensor-component lift of the canonical datum of `G_L`. The source `C`
is affine because the supplied cover makes it semisimple. The map
`Spec L → Spec k` is flat and surjective by `fieldExtension_fpqc`, so
`Datum.affineSolution` constructs the solution. Neither a descended source
nor a solution is supplied as an input.

`IsSimplyConnectedCover.tensorDescentCentralIsogeny` constructs an actual
central isogeny from this source to `G`. It uses the proved compatibility
of the lifted datum and `Datum.affineCentralIsogenyTo`.
`baseChange_tensorDescentCentralIsogeny` gives the exact equation

```text
(baseChange (fieldMap k L)).map descendedMap
  = tensorDescentSolution.iso.hom ≫ π.
```

`existsUnique_tensorDescentCentralIsogeny` states that exactly one arrow
from this constructed source to `G` is central and satisfies that equation.
It is the unique arrow with that equation by actual morphism descent.
The central-isogeny predicate keeps the full scheme-theoretic kernel on
all test schemes, together with finiteness, flatness, surjectivity and
local finite presentation.

This is an internal composition of `Descent.TensorCoverDatum`,
`Descent.CentralIsogenies` and the field-extension fpqc theorem. The first
constructs the actual compatible datum from the tensor equivalence and
the supplied cover; the second supplies affine effectivity, actual
morphism descent and proved fpqc reflection of central isogenies.
The finite tensor equivalence and its formula and the original cover
remain inputs. The module proves neither the existence of those inputs
nor semisimplicity, simple connectedness or the cover universal property
of the descended source. Those reflection and universal-property steps,
and arbitrary field-extension preservation, remain separate obligations.
