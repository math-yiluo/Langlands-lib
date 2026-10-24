# Equivariant functionals and the localized quotient dual

Author: Worker 127. This module is an intrinsic algebraic universal-property
construction from the published `Whittaker.Algebraic` and
`Jacquet.Localization` modules. It is not an additional theorem attributed to
JPSS or another external source. Both imported pairs remain unchanged.

For every commutative ring `R`, group `G`, subgroup `U`, units-valued character
`θ : U →* Rˣ`, and representation `ρ : Representation R G V`,
`Whittaker.functionalsLocalizationDualEquiv U θ ρ` is the actual linear
equivalence

`Whittaker.functionals U θ ρ ≃ₗ[R] Module.Dual R (Jacquet.Localization.Coinvariants ρ U θ)`.

The ring, group, and module have independent universes `uR`, `uG`, and `uV`.
There is no field, topology, smoothness, admissibility, or dimension hypothesis.
The quotient is precisely the existing module quotient by the span of
`ρ u v - (θ u : R) • v`, and the dual is its full algebraic dual.

The forward map is `Localization.lift` of the given functional. Its covariance
is exactly the required condition for killing the relation span, since scalar
multiplication on `R` is multiplication. The inverse is precomposition with
`Localization.mk`. The quotient relation `mk_apply_subgroup` and linearity
prove that this precomposition has the required covariance. The left inverse
is checked on original vectors; the right inverse and linearity are checked
on quotient representatives using `Localization.hom_ext`. Thus the
construction reuses the proved quotient universal property.

`functionalsLocalizationDualEquiv_mk` proves that evaluating the descended
functional on the quotient class of `v` recovers the original functional at
`v`. `functionalsLocalizationDualEquiv_symm_val` identifies the inverse's
underlying linear map with `f.comp (Localization.mk ρ U θ)`, and
`functionalsLocalizationDualEquiv_symm_apply` gives its pointwise evaluation.
These formulas are definitional for this construction.

Specializing to complex coefficients and the character in the companion
`Whittaker.EntrywiseCharacter` supplies the localized functional-dual
interface requested by the induced Whittaker-type task. The equivalence
makes no induction, tensor-dual, uniqueness, or heredity assertion.
