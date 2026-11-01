# The actual Harris positive Lie and dimension level tower

This module constructs the fixed-base level tower on the actual positive
polarized dimension-and-Lie classes of `HarrisTaylorLiePolarizedClasses`.
The index is `HarrisLevel D`, the compact-open transporter category of
the opposite original Harris finite-adelic group. `hodgeLevelFunctor D C`
transports it using the same whole Hodge-positive unit that defines the
regular source form. The positive auxiliary involution is the left
involution `auxiliaryStarRing D C` used by that actual geometry.

The arithmetic inputs are a totally real number field `E`, a totally
complex quadratic number field extension `F/E`, the actual central simple
unitary datum `D` with algebra `A`, and signature charts `C`. The positive
Lie condition additionally uses an imaginary quadratic CM number field
`L` with an algebra map to `F`, and an actual structure morphism
`p : S ⟶ Spec F`. The source's imaginary quadratic field `E`, CM field
`F`, totally real field `F⁺`, algebra `B` and abelian scheme `A`
correspond respectively to the Lean parameters `L`, `F`, `E`, `A` and
the underlying abelian scheme. No CM-section condition on the signature
charts or reflex-field morphism is needed for this tower.

All input types and the base scheme have universe zero. The resulting
class tower takes values in `Type 1`. Its other parameters remain those
of the reused actual polarized and compatible-level constructions:
the named tensor-pullback, coherence, Picard-zero, Mumford-bundle and
universal-base-change statements; the finite Weil transition and torsion
finite-etale statements; the rational profinite-integer/finite-adele
comparison; an actual field-valued point `s` and finite fibers there;
invertibility of every positive integer index on `S`; finite etale
roots-of-unity schemes; quasi-separatedness of `S`; and ordered-pair
additivity of the constructed dual maps. These named statements are
explicit assumptions here. The point's field is not assumed algebraically
closed. Connectedness, reducedness, flatness, local noetherianity and
level-smallness are not additional hypotheses.

`ambientTower` is the existing raw `PolarizedWeilLevel.isoClassTower`
composed with the actual original-Harris level functor. Its objects
are the existing `AmbientClass U`, with no determinant restriction.
`mapRepresentative` applies the raw actual transporter map to an
actual positive polarized object equipped with a compatible fixed
level orbit. Its first component is definitionally the identical
positive polarized object. In particular, the underlying abelian
scheme, action, geometric polarization, dimension and positive Lie
sheaf are unchanged; only the orbit is transported. The representative
formula for the ambient tower is proved.

The raw quotient map retains the same rational action class.
Consequently `LieClassCondition` is preserved and reflected by every
level arrow. To preserve `ClassCondition`, the proof takes its one
actual satisfying representative and maps its level orbit. The same
object and the same dimension-and-Lie proof remain a witness at the
target level. This argument does not require dimension invariance under
rational isomorphisms or a new representative chosen independently of
the dimension witness.

`classMap` is the resulting subtype map. Its value and constructor
formulas are proved, and `isoClassTower` packages it as a functor.
Identity and composition follow from the actual ambient functor by
subtype extensionality. `inclusionNatTrans` is the natural inclusion
into `ambientTower`. `forgetDimensionLieAction_classMap` proves that
the actual joint dimension-and-Lie action class is constant along every
level map; the proof uses the existing surjectivity from satisfying
representatives and the identical underlying object. The resulting
`forgetDimensionLieActionNatTrans` has codomain the constant functor
with value `HarrisTaylor.DimensionLieActionClass L E p n`.

`forgetLevel` uses the original subgroup-inclusion arrow. Its
representative formula and unchanged joint action class are proved.
For original compact-open levels `U`, `V` and an element `g` of the
opposite original Harris group, `heckeLeft` and `heckeRight` have common
source at the actual compact-open subgroup `U ∩ g V g⁻¹`. The left leg
is the inclusion into `U`; the right leg is the original transporter
with element `g` into `V`. Their maps on classes use those actual
arrows, transported by `hodgeLevelFunctor`. The required finite
dimensionality of `A` over `ℚ`, used to obtain the topological group
structure for this intersection, is derived from
`hodgeRationalPELConditions D C`. Both constructor formulas and the
unchanged joint action class along each leg are proved.

This is a derived prerequisite using the actual polarized rational
quotient and its proved compatibility with actual level transport.
It does not assert finite etaleness or representability of the tower
by schemes, geometric-point independence, an arbitrary-scheme pullback
of the positive Lie condition, equivalence with a central trace or
determinant condition, or a canonical-model theorem. The same-
representative image from the imported class module is preserved
without imposing any determinant condition. Its explicit geometric
and finite-Weil hypotheses remain obligations of the larger task.

The original source is Harris and Taylor, *The Geometry and Cohomology
of Some Simple Shimura Varieties* (2001), III.1, printed pp.89–91 /
PDF pp.97–99, registered as
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
Printed p.89 prescribes dimension `d n²`; p.90 defines positive Lie
rank and equality of the two totally real field actions. Printed p.91
defines the polarized fixed-orbit classes and gives subgroup forgetting
and right translation by precomposition of the level isomorphism with
`g` when `g⁻¹ V g ⊆ U`. The implementation realizes these fixed-base
class maps and their actual original-group indexing. The Hecke span
is the derived pair of those arrows from their common compact-open
intersection. The stronger source hypotheses and the source's scheme
and finite-etale conclusions are not asserted by this class tower.
