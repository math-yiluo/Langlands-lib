# Combined local norm neighborhood theorem

Author: Worker 564.

`Langlands.Global.AdelicFunctoriality.localNormNeighborhood.{u,v}` proves
exactly
`Langlands.Global.AdelicFunctoriality.LocalNormNeighborhoodStatement.{u,v}`
from [LocalNormNeighborhoodStatement](LocalNormNeighborhoodStatement.md).
The field universes are independent: for arbitrary number fields
`K : Type u` and `L : Type v` with `Algebra K L`, both the finite and
infinite local norm images on multiplicative units are neighborhoods of
one. Each branch covers every pair of places and every lying-over
witness quantified in the published target. The norm maps, completion
algebras and topologies are those of that target.

The proof introduces the fields and their structure instances and splits
the conjunction. For a finite pair `p, q` and witness `h`, it installs
`h` as a local instance with `let _ := h` and applies
`range_finiteLocalNorm_mem_nhds (K := K) (L := L) p q`.
For an infinite pair it installs the corresponding witness in the same
way and applies `range_infiniteLocalNorm_mem_nhds`. These are Worker
269's published theorems in
[LocalNormNeighborhood](LocalNormNeighborhood.md), which supply all the
local mathematics. The infinite theorem requires only `NumberField K`,
so it applies under the target's hypotheses.

This module assembles those results and adds no hypotheses to the
published proposition. In particular it includes real places below
complex places and does not require the extension to be cyclic or
Galois. It leaves the target and all imported files unchanged.

## Derived provenance

The source is Emil Artin and John Tate, *Class Field Theory*, AMS Chelsea,
2009, Chapter V §4, proof of Theorem 2, printed p.17 / PDF p.26.
Registered source: `artin-tate-2009-class-field-theory`, SHA-256
`af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`,
retained at
`/home/taskhub/central-library/Artin-Tate--Class Field Theory--2009.pdf`.
The passage and appended errata on PDF p.202 were read; those errata
make no correction to this passage.

Artin and Tate use local norm neighborhoods in the principal adjustment
of an idele. This theorem packages that local input for number fields.
The component theorems use the inverse function theorem for powers near
one and the norm-of-base-scalar identities, as explained in their paired
Markdown. The present proof reuses those theorems directly. It does not
construct a principal adjustment or prove the global theorem.
