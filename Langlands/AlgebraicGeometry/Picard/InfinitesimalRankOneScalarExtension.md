# Actual scalar extension of patched rank-one modules

This is an internal ring-and-module prerequisite for infinitesimal Picard
gluing. It uses the published `InfinitesimalRankOnePatching` construction.
All four commutative rings `R`, `A`, `B`, `C` lie in an arbitrary common
universe `u`. The actual `R`-algebra maps to `A` and `B`, and ring maps
`a : A → C`, `b : B → C`, form a categorical pullback in `CommRingCat`.
For a specified unit `c` of `C`, write `P_c` for the existing submodule of
`A × B` whose elements satisfy `a(z.1) = c * b(z.2)`.

Suppose a unit `v` of `B` maps to `c`. The definitions `firstEquiv` and
`secondEquiv` construct actual linear equivalences

- `A tensor_R P_c ≃_A A`;
- `B tensor_R P_c ≃_B B`.

Their elementary-tensor formulas are respectively `t tensor z ↦ t * z.1`
and `t tensor z ↦ t * z.2`. Thus these are the scalar-extended pair
projections, with their given coordinates. Each equivalence is uniquely
determined by its formula, and the independence lemmas show that neither
result depends on which lifted unit was used to construct it.

The construction base changes the inverse of the published frame
`r ↦ (p(r), v⁻¹ * q(r))`, then uses Mathlib's
`AlgebraTensorModule.rid`. On the second leg it also multiplies by `v⁻¹`,
using `Units.mulLeftLinearEquiv`. Applying the two coordinate functions to
the frame's inverse identity proves the two elementary-tensor formulas.
Tensor extensionality then proves uniqueness and independence. The theorem
`exists_scalarExtensionEquivs` uses the published actual unit-lifting theorem
to supply both identifications for every `c` when `b` is surjective and its
kernel ideal is nilpotent. Only that existence step assumes surjectivity
and nilpotence.

For multipliers `x` in `A`, `y` in `B`, and units `c`, `d` satisfying
`a(x) * c = d * b(y)`, the published diagonal map sends
`P_c` to `P_d` by `(z.1,z.2) ↦ (x*z.1,y*z.2)`. The two
`diagonalMap` compatibility lemmas prove, on every tensor element, that its
scalar extensions become multiplication by `x` and `y` under the respective
identifications. The corresponding `diagonalEquiv` lemmas specialize these
identities to the prescribed unit isomorphisms. The proofs use the coordinate
formulas on elementary tensors and additivity.

For the overlap comparisons, additionally use actual algebra structures
`R → C`, `A → C`, `B → C` with both scalar-tower compatibilities, and take
`a`, `b` to be these algebra maps. The definitions `firstOverlapEquiv` and
`secondOverlapEquiv` are actual `C`-linear equivalences `C tensor_R P_c ≃_C C`.
They use `cancelBaseChange` to pass through `C tensor_A (A tensor_R P_c)`
and `C tensor_B (B tensor_R P_c)`, respectively, base change the two
identifications above, and apply the corresponding right unit equivalence.
Their elementary-tensor values are `t * a(z.1)` and `t * b(z.2)`.
The theorem `overlap_compat` proves on every element `w` that
`firstOverlapEquiv(w) = c * secondOverlapEquiv(w)`. Its proof reduces by
tensor induction to the defining equation of `P_c`, so the original specified
overlap multiplier is retained.

The provenance is internal: the published frame and unit lifting, Mathlib's
base-change, tensor-associativity and unit-multiplication equivalences, and
elementary ring identities give these constructions directly. No additional
external theorem is assumed. This module does not construct sheaves from
modules, patch arbitrary line bundles, establish the scheme Picard-groupoid
comparison, or prove field Picard-sheaf representability. Those geometric
obligations remain separate, including the exact infinitesimal-gluing proof.
