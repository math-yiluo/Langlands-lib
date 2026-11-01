# Positive Lie rank and equality of the two central actions

This module defines the compatibility condition in Harris–Taylor,
*The Geometry and Cohomology of Some Simple Shimura Varieties* (2001),
III.1, printed p.90 / PDF p.98, immediately before Lemma III.1.2.
The registered source is
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
The source requires that its positive Lie factor have rank `n` and that
the two actions of its totally real field on that factor coincide.

Here the source's imaginary quadratic field `E` is named `L`, its CM field
`F` is named `K`, its totally real field `F⁺` is named `E`, its acting
algebra is named `A`, and its abelian scheme is named `B`. The definitions
and their transport laws only need a field `E` with an algebra map into
`K`; the Harris specialization supplies the totally real number field.
They work for every natural number `n`, including zero. The source's
additional arithmetic, dimension, signature and positivity assumptions
are not inferred from these definitions.

The inputs are an imaginary quadratic CM number field `L`, a number field
`K` containing `L`, an actual structure morphism `s : S ⟶ Spec K`, an
actual abelian scheme `B/S`, and an actual rational algebra action
`i : A →ₐ[ℚ] End0 B` for a `K`-algebra `A`. The positive factor
`lieTensorSheaf L s B i false` is the already constructed actual sheaf
with sections

```text
Γ(B.Lie,U) ⊗_(Γ(S,U) ⊗_ℚ L) Γ(S,U),
```

using the natural imaginary-field embedding on the final factor.

`PositiveLieScalarCondition` requires, for every `a : E`, equality of two
actual sheaf endomorphisms: the action `lieTensorAction` of the central
element `algebraMap K A (algebraMap E K a)` and multiplication by the
global regular function `secHom s ⊤ (algebraMap E K a)`. The latter is
`scalarHom` applied to the identity morphism; on an open it multiplies
sections by the restriction of that function. Thus the equation compares
the differentiated algebra action and the structural scalar action.

`LieCompatibility L E s B i n` conjoins this equation with
`IsLocallyFreeOfRank (lieTensorSheaf L s B i false) n`. This rank predicate
exhibits a cover with actual local bases indexed by types equivalent to
`Fin n`; it is not a numerical rank label supplied independently of the
sheaf.

`PositiveLieEigenScalarCondition` and `EigenLieCompatibility` give the
same tests on the full positive eigensubsheaf. The comparison theorems use
the constructed `lieTensorSheafIso`, its proved action intertwining, and
transport of actual local bases along an isomorphism. A private helper
proves that the structural scalar endomorphisms commute with every
module-sheaf morphism, using global-function linearity of composition.
Cancellation by an isomorphism then transports equality with that scalar.

`positiveLieScalarCondition_iso` and `lieCompatibility_iso` prove
invariance under an actual rational isomorphism of abelian schemes that
intertwines the full `A` actions. The proof uses the constructed
`lieTensorIso` and `lieTensorMap_intertwines`; the rank part uses
`IsLocallyFreeOfRank.ofIso`. The input includes the actual rational inverse.
It does not assume an output Lie isomorphism or a rank comparison.

These definitions follow the source's initial compatibility definition.
The comparison and invariance laws are derived from the existing actual
sheaf constructions. The equivalences with trace conditions in
Lemma III.1.2, arbitrary scheme pullback of these conditions, and
construction of representing PEL schemes remain separate obligations.
