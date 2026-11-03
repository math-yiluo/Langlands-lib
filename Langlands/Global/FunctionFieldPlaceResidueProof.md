# Residue finiteness via Krull–Akizuki

`Langlands.Global.functionFieldPlaceResidue` proves
`Langlands.Global.FunctionFieldPlaceResidueStatement` in one arbitrary
universe. For compatible `k`- and `RatFunc k`-algebra structures on the fields
`k` and `F`, and `FunctionField k F`, it proves
`Module.Finite k v.ResidueField` for every actual
`v : AlgebraicCurve.Place k F`. The module action is the existing quotient
action induced by the constant-field inclusion in the valuation ring.

The private lemma `finite_residue_of_parameter_mem` first works with any
`s : F` for which `F` is finite dimensional over `k⟮s⟯` and `s` belongs to the
actual valuation ring `O = v.toValuationSubring`. It forms
`R = Algebra.adjoin k {s}`. The published
`CurveModel.adjoin_le_valuationSubring` puts every element of `R` in `O`,
so the proof regards the same ring `O` as an `R`-subalgebra `B` of `F`.
The existing `Algebra k O` is retained explicitly as `Algebra k B`, and
`IsScalarTower.of_algebraMap_eq` checks the scalar tower by equality of the
constant-field maps. Thus the argument does not change the constant-field
action when it changes the subalgebra presentation.

The valuation ring is a discrete valuation ring; in particular its maximal
ideal is nonzero, by `IsDiscreteValuationRing.not_a_field`. The published
`Subalgebra.isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite`
is the Krull–Akizuki overring theorem applied to `R`, its fraction field
`k⟮s⟯`, the finite extension `F`, and `B`. Its finite-length conclusion,
applied to the nonzero maximal ideal of `B`, gives
`IsFiniteLength R (IsLocalRing.ResidueField B)`. Finite length gives the
Noetherian module property and then `Module.Finite R` of this residue
field.

The one-generated algebra `R` is finite type over `k`, by
`Algebra.FiniteType.adjoin_of_finite`. Module finiteness makes the residue
field a finite type `R`-algebra. Transitivity therefore makes it a finite
type `k`-algebra. Mathlib's
`finite_of_finite_type_of_isJacobsonRing` applies Zariski's lemma to this
field and proves `Module.Finite k` of it. Because `B` has the same carrier,
ring structure, local-ring structure and constant action as `O`, this is the
required finiteness of the actual `v.ResidueField`.

For the final theorem, take `s` to be the image of `RatFunc.X`. The published
`FunctionField.FiniteDimensional.adjoin_algebraMap_X` supplies finite
dimensionality of `F` over `k⟮s⟯`. The valuation-subring property puts either
`s` or `s⁻¹` in `O`. In the second case the proof establishes
`k⟮s⁻¹⟯ = k⟮s⟯` by mutual inclusion: each generator is the inverse of an
element of the other field. It transfers finite dimensionality across this
equality and applies the same private lemma to `s⁻¹`.

This is a derived arithmetic proof using the published Krull–Akizuki
infrastructure and pinned Mathlib results. It requires no finite or perfect
constant field and no separability of the specified rational-function
extension. It assumes neither residue finiteness nor a supplied local-field
package. Compactness of completions, local compactness of adeles, diagonal
discreteness, and geometric point comparisons remain separate results.
