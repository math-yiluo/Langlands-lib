# Euler characteristics of actual sheaf cohomology over a field

This file defines the Euler characteristic using the published actual derived
sections functors, with the field structure supplied by the actual structure
morphism `f : X ⟶ Spec K`. Its source is the Stacks Project, Section 33.33,
Definition 33.33.1 and the finiteness explanation immediately following it
([tag 0BEI](https://stacks.math.columbia.edu/tag/0BEI)), retained as
`stacks-euler-characteristics-0BEI-2026-11-01`.

`HasFiniteCohomology f M` requires both of the following:

- Each actual vector space `(relativeCohomology f n).obj M` is finite
  dimensional over `K`, expressed by `Module.Finite K`.
- There is a natural bound `N` such that all these cohomology objects in
  degrees `n ≥ N` are zero, expressed by the categorical predicate `IsZero`.

`eulerCharacteristic f M h` is the integer alternating sum, in nonnegative
degrees, of the dimensions of those actual vector spaces. The function takes
an explicit proof `h : HasFiniteCohomology f M`. Its value uses Mathlib's
`finsum`; the bound in `h` ensures finite support of the summand, and the
finite-dimensionality clause ensures that `Module.finrank` is the ordinary
vector-space dimension. No vanishing bound is chosen in the definition, and
the value does not depend on the supplied proof of finiteness.

The source defines this invariant for coherent modules on proper schemes
over a field and justifies these two finiteness properties geometrically.
This file isolates the invariant whenever those properties hold, without
requiring properness or coherence as redundant parameters. It does not prove
the geometric finiteness assertions for proper coherent modules, an
additivity formula, a Hilbert polynomial, or any degree comparison. Those
remain separate proof obligations. The finite-cohomology predicate is an
internal expression of the source's stated finiteness conditions, not an
assumed numerical rank or degree formula.
