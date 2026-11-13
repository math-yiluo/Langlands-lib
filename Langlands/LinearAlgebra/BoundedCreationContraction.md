# Generation from creation and contraction in a bounded family

Author: Worker 327.

This is a derived internal argument in linear algebra. Let `M n` be modules
over an arbitrary commutative ring `R`, and let a finite type `ι` index
creation maps `c i n : M n → M (n+1)` and contraction maps
`d i n : M (n+1) → M n`. The required relations, on every positive
degree `M (n+1)`, are

```text
d_i c_j + c_j d_i = δ_ij id.
```

The modules vanish in every degree strictly larger than `card ι`.
There is no assumption on characteristic, finite generation, the degree-zero
module, or a multiplication on these modules.

`creationSpan` contains all of `M 1`, and in each larger degree is the sum
of the images under all creation maps of the preceding submodule.
The relations show by induction that contractions preserve these submodules:
a contraction of `c_j x` is either `x - c_j d_i x` or `-c_j d_i x`.

The main finite-set argument `mem_of_contractions_mem` works for any family
of submodules stable under creation and contraction. Suppose that every
contraction of `x` in a finite set of directions belongs to the submodule.
If the degree of `x` plus the number of directions exceeds the bound, then
`x` belongs to the submodule. Induct on the set of directions. With no
directions left, boundedness gives `x = 0`. Otherwise create in one direction.
All remaining contractions are negatives of creations applied to the
original contractions, so induction puts this created element in the
submodule. Applying the contraction in the removed direction and the
diagonal relation recovers membership of `x`.

`creationSpan_eq_top` applies this argument with all directions and inducts
on positive degree. Thus the creation span is the whole module in every
positive degree. In particular, `iSup_range_degreeOne_eq_top` states that
the images of `c i 1 : M 1 → M 2` span all of `M 2`.

For a proposed cohomological application, creation would be multiplication
by a basis of H¹, and contractions would come from components of the
coproduct. This module constructs none of that geometric data and does
not identify any actual cohomology functor. Equality between the dimension
of H¹ and the cohomological bound would supply the number of directions.
The argument is internal and proved directly using submodules and the
displayed linear-map relations; no external structure theorem is invoked.
