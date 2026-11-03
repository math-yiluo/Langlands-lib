# Finite power index in the whole prescription local product

Author: Worker 53.

These are internal deductions from the Library's proved finite local power
index theorem, its archimedean root arguments, and Mathlib's quotient
isomorphisms. They implement the local finiteness input used in the
finite-order prescription argument of Artin and Tate, *Class Field Theory*
(AMS Chelsea, 2009), Chapter X, Section 2, printed pp.77–80 (one-based
PDF pp.86–89). The registered source is
`artin-tate-2009-class-field-theory`, SHA-256
`af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`.
The proof here only establishes finite index, and does not assert openness
of the power subgroups or an unconditional global prescription.

`finiteIndex_power_range_pi` transports finiteness across Mathlib's
`QuotientGroup.mulEquivPiModRangePowMonoidHom`: the quotient of a product by
its power subgroup is isomorphic to the product of the factor power quotients.
There are finitely many factors, each quotient is finite, so their product
is finite. The indexing universe and factor universe are independent.
`finiteIndex_power_range_prod` identifies the binary product's power subgroup
with the product of the two factor power subgroups and applies the finite-index
product instance.

`infiniteCompletion_power_finiteIndex` handles every infinite completion and
every nonzero natural exponent by reusing the published
`Arithmetic.SUnitIdelePowerQuotient.infinite_power_finiteIndex`, whose statement
is identical. That proof transfers a real place to the reals and uses
the positive real `d`th root to show that either a unit or its negative is a
`d`th power. The quotient is the image of the two-element type `Bool`, through
the classes of `1` and `-1`; this proves actual finiteness. The positive-root
calculation is the one used in
`Langlands.ClassField.Global.index_infiniteUnitPowers_le_two`. A bound on the
natural-number index alone would not suffice, since the index of an infinite
quotient is zero. At a complex place, the existing theorem identifies the
power subgroup with the whole group.

`infiniteAdeles_power_finiteIndex` identifies units of the whole infinite adele
ring with the product of the infinite completion unit groups using
`MulEquiv.piUnits`. The finite-product result and transport of power ranges
along that equivalence give finite index. All real sign components remain.

Finally, `prescriptionLocalProduct_power_finiteIndex` uses
`Langlands.ClassField.Global.localPowers_finiteIndex` at the selected actual
finite completions, applies the finite-product result, and combines this with
the whole infinite factor. Its field universe is unrestricted. This supplies
the finite-image hypothesis for the profinite separation argument when combined
with the separate proved topology of the actual idele-class power quotient.
