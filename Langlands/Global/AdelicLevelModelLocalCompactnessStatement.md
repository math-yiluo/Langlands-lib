# Local compactness of arithmetic-level model points

`AdelicLevelModelLocalCompactnessStatement` states Corollary 3.7 of Brian
Conrad, *Weil and Grothendieck approaches to adelic points* (December 31,
2011), printed page 9. It has one function-field clause and one number-field
clause, in any common universe `u`.

Each clause concerns the actual points of a finite-type model `X` over its
outside-`S` integer ring, valued in the actual arithmetic-level ring.
`LocallyOfFiniteType X.hom` and `QuasiCompact X.hom` express finite type.
The topology is precisely `curvePlaceLevelModelPointTopology` or
`numberFieldLevelModelPointTopology`, induced from the product of the
independently constructed point topologies on the actual local base changes.
The conclusion is local compactness for every such model, together with
Hausdorffness when the structure morphism is separated. Local compactness
has no separatedness premise.

The function-field clause uses the original `k`-algebra structure on `F`,
a compatible scalar tower through `RatFunc k`, and `FunctionField k F`.
The constants `k` are finite. In particular, the completions at actual curve
places are locally compact and their completed valuation rings are compact.
There is no separability assumption on the rational-function presentation.
The number-field clause permits every number field and includes every
archimedean completion. Its finite set `S` indexes only the finite places
at which the completion field replaces its integer ring.

Both clauses retain the original outside-`S` integer actions and actual
relative scheme points. Models need not be affine or separated; the
Hausdorff conclusion alone asks for separatedness. No topology comparison,
compactness, local compactness or Hausdorffness is assumed as input.

Conrad uses nonempty finite sets of places containing all archimedean
places. Here `S` may be empty: every archimedean place is already included
in the number-field factors, and the function-field empty level has only
integer-ring factors. This is an explicit derived extension of Corollary
3.7. The integer bases remain Noetherian at the empty set; finite-type
models therefore still have the actual product-point comparison. Each
integer-valued local point space is compact by the compact local-ring
point theorem. The finitely many field-valued factors are locally compact.
Splitting these two groups of factors gives local compactness of their
product even when the model is nonseparated. For a separated model, each
local point space is Hausdorff, and so is the product.

This file defines the proposition to be proved. It does not prove
Corollary 3.7, assert local compactness over infinite constant fields, or
supply the separate topological properties of full adelic points.

Source: registered literature `conrad-2011-weil-grothendieck-adelic-points`,
SHA-256 `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`,
printed page 9, Corollary 3.7 and its proof. The empty-level allowance is
derived as described above.
