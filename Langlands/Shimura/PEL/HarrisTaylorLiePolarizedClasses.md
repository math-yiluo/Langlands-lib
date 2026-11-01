# Positive Lie compatibility on actual Harris polarized level classes

This module attaches the actual Harris–Taylor positive Lie condition and
prescribed geometric dimension to the existing actual polarized Weil
level quotient. It uses the positive auxiliary left involution
`auxiliaryStarRing D C`, the whole Hodge-positive witness used by the
regular source form, and the original opposite Harris group's
compact-open levels, transported by `hodgeLevelFunctor D C`.

The arithmetic inputs are the actual central simple unitary datum `D`
over a totally real number field `E` and a totally complex quadratic
extension `F/E`, with its actual algebra `A`, together with signature
charts `C`. The positive Lie test also uses an imaginary quadratic CM
number field `L` mapping into `F` and an actual structure map
`p : S ⟶ Spec F`. The charts may have any embedding section for which
they are supplied; no CM-section property, reflex structure or
determinant equality is an additional input here. All types and the
scheme have universe zero.

`PositivePolarizedAction` is the existing actual input. It contains
an actual abelian scheme, a faithful rational algebra action, its
constructed dual scheme and Poincare evaluation data, an actual
geometric polarization, and the equation relating the action to
the positive auxiliary involution. The explicit named assumptions
for tensor pullback, Picard-zero pullback, the Mumford bundle and
universal base change remain parameters, as in that construction.
They are not proved by this module.

`LieObjectCondition` tests local freeness of rank `n` of the actual
positive Lie tensor sheaf and equality of the two `E` actions on it.
`ObjectCondition` is the conjunction of this condition with
`PrescribedRelativeDimension E`, namely dimension `[E : ℚ] * n²`
of the same abelian scheme's actual structure morphism.

For the level constructions, the parameters additionally include the
existing named finite Weil transition and torsion finite-etale
statements, the rational profinite-integer/finite-adele comparison,
an actual point `s` with field-valued source, finiteness of
the fibers of finite-etale covers at `s`, invertibility of all positive
integer indices on `S`, finiteness and etaleness of the corresponding
roots-of-unity schemes, quasi-separatedness of `S`, and ordered-pair
additivity of the actual dual maps. The source problem uses a
geometric point in the usual algebraically closed sense; the reused
construction works for the explicitly supplied field-valued point
and its fiber assumptions. No reducedness, connectedness, flatness
or local noetherianity of `S` is assumed here.

`AmbientClass U` reuses `PolarizedWeilLevel.IsoClass` at the
transported original level. Its representatives are actual positive
polarized actions carrying a fixed compatible Weil-level orbit.
`ambientClassOf` and `forgetAction` reuse the existing quotient
and its map to `RationalAlgebraAction.IsoClass`. The forgetful map
is well defined because every ambient relation includes an actual
equivariant rational isomorphism.

`LieClassCondition` is the invariant positive Lie predicate pulled
back along this actual forgetful map. Its representative formula
holds for every representative of a given polarized class.
`ClassCondition q` requires one actual level representative of `q`
satisfying `ObjectCondition`. The theorem `classCondition_iff`
identifies this image with `LieClassCondition q` and the image
of the actual dimension predicate. The reverse implication
transfers Lie compatibility to the representative witnessing
dimension. Thus one actual polarized abelian scheme satisfies both
conditions; dimension is never silently transported through a
rational isomorphism. Every representative of a satisfying class
has positive Lie compatibility, with no analogous dimension claim.

`IsoClass U` is this image as a subtype of the actual ambient
quotient. The constructor `classOf` is surjective from the satisfying
representatives. Equality of constructed classes is exactly the
existing polarized relation: a rational unit, an actual equivariant
isomorphism in the rational category, the actual dual-pullback
polarization multiplier equation, and equality of the transported
compatible fixed orbit with the target orbit. The rational
isomorphism includes its inverse and both inverse identities; it
is not merely an arbitrary rational arrow. The inclusion is
injective.

`forgetDimensionLieAction` sends a class to the previously
constructed joint action-class image. Its witness is the very
same actual representative carrying the polarization, dimension
and Lie condition. Its value and constructor formulas are
proved, and every representative of its forgotten action class
satisfies positive Lie compatibility.

The proofs use the existing quotient and its exact relation, the
proved invariance of actual Lie compatibility, quotient
representative formulas and subtype extensionality. This is a
derived fixed-base prerequisite, not a claim of representability
or of a scheme-valued moduli functor. It does not identify
positive Lie compatibility with central trace or the normalized
determinant condition, prove dimension invariance under rational
isomorphism, identify every rational isomorphism with a geometric
isogeny on arbitrary schemes, or provide scheme pullback,
geometric-point independence or existence of representing schemes.

The original source is Harris and Taylor, *The Geometry and
Cohomology of Some Simple Shimura Varieties* (2001), III.1, printed
pp.89–91 / PDF pp.97–99, registered as
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
Printed p.89 prescribes dimension `d n²`; p.90 defines positive Lie
compatibility; p.91 specifies the polarized quadruples with fixed
compatible level orbits and their isogeny relation. The source's
imaginary quadratic field `E`, CM field `F`, totally real field
`F⁺`, algebra `B` and abelian scheme `A` are respectively this
module's `L`, `F`, `E`, `A` and underlying abelian scheme.
The existing constructions implement the relation using actual
equivariant rational isomorphisms. Their broader fixed-base
hypotheses and the retained comparison obligations are explicit
above.
