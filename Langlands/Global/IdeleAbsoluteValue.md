# Actual normalized idelic absolute value

`Langlands.Global.IdeleAbsoluteValue` constructs the normalized absolute value on
actual number-field ideles and their actual principal quotient. The number field
`F : Type uF` has arbitrary universe. The coefficient group is `ℝ≥0ˣ` with its
usual units topology. All adelic rings, local insertions and quotient maps are
those of `Langlands.Global.Adelic`.

The finite-place norms are the pinned Mathlib normalized completion norms. The
archimedean exponent is `v.mult`, which is one at real places and two at complex
places. Thus the real value of `full F x` is

\[
 \left(\prod_{v\mid\infty}\|x_v\|^{v.\mathrm{mult}}\right)
 \left(\prod_{v\nmid\infty}\|x_v\|\right).
\]

For an idele, the second product has finite multiplicative support. These factors
are not supplied characters or choices of normalization.

`finiteValue` is the multiplicative nonnegative real function given by the
finite-support product of local norms. Support finiteness is Mathlib's
`NumberField.FiniteAdeleRing.hasFiniteMulSupport_norm`, and multiplicativity
uses that support theorem and local norm multiplicativity. `coe_finiteValue`
records its real value; `finiteValue_eq_norm` compares it with Mathlib's
multiplicative finite-adele `Norm` instance. That instance is not treated as a
normed-ring norm.

`allIntegral` is the subgroup of finite ideles whose value and inverse are
integral at every finite place. It is open by the restricted-product open
integral set and the two continuous value maps on units. Both integrality
conditions put each coordinate unit in the local integer-ring unit group.
Mathlib's valuation criterion and normalized-norm comparison show that its norm
is one. Consequently `finiteValue` is one on `allIntegral`. Its unit-valued
homomorphism is constant on an open neighborhood of the identity, so it is
continuous at the identity and hence everywhere. This gives the genuine
continuous homomorphism `finite`. The inverse comes from the inverse idele via
`MonoidHom.toHomUnits`; no separate positivity assumption is used.

`infiniteValue` is the finite archimedean product. Multiplicativity follows
coordinatewise, and continuity is proved on each actual completion coordinate
and its norm power, then by finite products. The inverse idele provides its
inverse value, giving the continuous unit-valued homomorphism `infinite`.
`coe_infiniteValue`, `infiniteValue_eq_norm` and `coe_infinite` record its
product and its comparison with Mathlib's infinite-adele `Norm` instance.
The proof never interprets that product instance as a normed-ring norm.

`full` multiplies these two continuous homomorphisms after the actual
`ideleProductEquiv`. `coe_full` is the displayed product formula for an arbitrary
idele, and `full_eq_norms` gives the product of the two Mathlib adele norms.
`full_pos` derives strict positivity from its value being a nonnegative real
unit. `full_diagonalUnits` proves that every principal idele has value one:
Mathlib identifies the infinite factor with the absolute rational field norm
and the finite factor with its inverse, and that field norm is nonzero on a
nonzero field element. This is the normalized product formula, with no
hypothesis on a supplied character.

`ideleClass` uses `QuotientGroup.lift` to descend `full` through the actual
principal subgroup. Its continuity follows from the quotient topology.
`ideleClass_class` identifies its value on every representative with `full`,
and `ideleClass_unique` proves uniqueness among continuous monoid homomorphisms
with those representative values, by quotient induction.

`full_infiniteIdelesInclusion` and `full_finiteIdelesInclusion` compute its
restriction to the entire infinite and finite factors. The two single-place
formulas `coe_full_finiteIdeleInclusion` and
`coe_full_infiniteIdeleInclusion` give respectively `‖x.val‖` and
`‖x.val‖ ^ v.mult`. The actual insertion has coordinate `Pi.mulSingle`, so
all other norm factors equal one, and the finite-support or finite product
reduces to the single coordinate. The corresponding
`coe_ideleClass_finiteClassInclusion` and
`coe_ideleClass_infiniteClassInclusion` formulas follow from the representative
formula on the quotient.

The provenance is internal: these are products, restrictions and quotient
constructions from pinned Mathlib's actual completion norms and the Library's
actual adelic objects. The Mathlib definitions and comparison theorems used are
in `NumberTheory/NumberField/FiniteAdeleRing.lean`,
`NumberTheory/NumberField/InfiniteAdeleRing.lean`,
`Topology/Algebra/Valued/NormedValued.lean` and
`RingTheory/DedekindDomain/AdicValuation.lean`. This module adds continuity in
the actual idele topology and the continuous principal-quotient descent to the
existing products and principal formulas. It makes no new identification with
original literature.

Identification with a Haar modulus, a determinant character on an adelic
parabolic, any relative idele norm, class field theory, and automorphic
representation existence remain separate obligations.
