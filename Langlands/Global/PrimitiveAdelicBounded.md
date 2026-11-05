# Compact representatives for bounded primitive adelic heights

This module constructs a compact set in the actual space `Fin n → Adeles F`
that meets every principal-scalar class of primitive vectors whose normalized
height is at most a prescribed real number `R`. The field is any number field
`F : Type u`, and `n` is any natural number. It uses the height, content idele
and compact normalized set from the preceding three primitive-vector modules.

The construction implements the compactness step in T. A. Springer,
*Reduction theory over global fields* (1994), §1.8, printed p.210 (PDF p.4),
following properties (a)–(d). Registered original:
`springer-1994-reduction-global-fields`, SHA256
`774f5531200db07140b30ffb8f4adce8cf3a3914ca9f38b796f2a2d24ff18496`.
The norm-one idele fundamental set is the existing
`NormOneIdeleClass.exists_isCompact_fundamentalSet F`. The scalar-root formula
and extension to parameter zero are explicit implementation choices for this
step. Local vector norms are maximum coordinate norms, and the global height
retains the complex-place multiplicity.

`realScalarAdele F r` has archimedean value `r` in the real subfield of every
infinite completion and finite part one. This is a continuous map on all real
parameters. For a positive unit `r` it is exactly the value of the existing
`PositiveRealIdeles.full F r`. At zero its archimedean part vanishes while its
finite part remains one; its definition does not assert it is a unit.

Write `d = [F : ℚ] > 0`. The positive unit `scalarRoot F h` has underlying
value `h^(1/d)` and its `d`-th power is `h`. The existing normalized idelic norm
of `PositiveRealIdeles.full F r` is `r^d`, so this root supplies a scalar idele
with norm `h`. If `h ≤ R`, the root is at most `max 1 R`: either it is at most
one, or its `d`-th power is at least itself.

Given a compact norm-one fundamental set `C`, `boundedRepresentativeSet F n C R`
is the image of

`[0, max 1 R] × C × normalizedSet F n`

under `(r, c, y) ↦ realScalarAdele F r • (c.val • y)`. This image is compact
by continuity of multiplication in the actual adelic topology. Including the
parameter zero makes the parameter interval compact without requiring a
positive lower height bound.

For a primitive vector `x`, the content factorization writes `x = t.val • y`
with `y` normalized and `|t| = height(x)`. Split off the scalar idele `s` of
norm `height(x)`, obtained from `scalarRoot`. The idele `s⁻¹ t` has norm one.
Choose a principal scalar `a` with `a s⁻¹ t ∈ C`. Commutativity gives
`a x = s.val • ((a s⁻¹ t).val • y)`, which lies in the compact image when
`height(x) ≤ R`. This proves the covering theorem for any supplied fundamental
set, and the existing norm-one fundamental-set theorem provides the final
unconditional existential assertion.

This unit does not yet prove finiteness of bounded-height rational classes,
existence of rational height minima, rank-one reduction, or the general
reductive Siegel-cover theorem. Those require further arguments.
