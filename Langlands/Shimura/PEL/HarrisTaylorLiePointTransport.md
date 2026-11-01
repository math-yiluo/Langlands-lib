# Point independence of the actual Harris positive Lie and dimension level tower

This module constructs the canonical comparison between the actual Harris
positive polarized dimension-and-Lie class towers at two geometric points.
It specializes `PolarizedWeilLevelPointTransport` to the arithmetic datum,
positive auxiliary involution, same-representative condition and original
Harris level category of `HarrisTaylorLieWeilTower`. Its namespace is
`Langlands.Shimura.PEL.HarrisTaylorLieWeilLevel`.

The source is Harris and Taylor, *The Geometry and Cohomology of Some Simple
Shimura Varieties* (2001), III.1, printed pp.89–91 / PDF pp.97–99,
registered as `harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
Printed p.91 asserts canonical independence of the geometric point for the
polarized compatible-level quadruples defined there. The present construction
implements that comparison for the existing actual rational-isomorphism
quotient, including its prescribed dimension and positive Lie image and its
original level indexing. The source's use of geometric isogenies and its
scheme representability and finite-etale conclusions are separate obligations.

## Inputs and retained geometry

All arithmetic types and the base scheme have universe zero. The inputs are a
totally real number field `E`, a totally complex quadratic number field
extension `F/E`, the central simple unitary datum `D` with algebra `A`, signature
charts `C`, an imaginary quadratic CM number field `L` mapping into `F`, and
an actual structure map `p : S ⟶ Spec F`. The source's imaginary quadratic
field, CM field, totally real field and algebra correspond to `L`, `F`, `E`
and `A`. The charts need no additional CM-section property here.

The positive auxiliary left involution is `auxiliaryStarRing D C`.
The actual regular source form and `hodgeLevelFunctor D C` use the same whole
Hodge-positive witness. The level category is `HarrisLevel D`, the existing
compact-open transporter category for the opposite original Harris
finite-adelic group. No replacement arithmetic group or determinant condition
is introduced.

The named tensor comparison, composition, unit coherence, associativity,
unitor comparison and symmetry statements, Picard-zero pullback stability,
Mumford-bundle Picard-zero statement and universal base-change statement remain
explicit inputs. The finite Weil transition compatibility statement, rational
profinite-integer/finite-adele comparison, torsion finite-etale statement,
invertibility of every positive torsion order on `S`, finite-etaleness of
the corresponding roots-of-unity schemes, quasi-separatedness of `S`, and
ordered-pair additivity of the constructed dual maps remain explicit too.
This module proves none of these inputs.

The first constructions use field-valued points `s`, `t`, `r`, finiteness
of the fibres of every finite-etale cover at each endpoint, and an actual
isomorphism of fibre functors. Algebraic closedness, connectedness and local
Noetherianness are required only for the final canonical geometric comparison.
No reducedness, flatness or level-smallness hypothesis is added.

The objects and quotient relation are exactly the existing ones. A
representative contains an actual positive polarized abelian scheme, its
faithful rational algebra action and a compatible monodromy-fixed level orbit.
The ambient relation retains the actual equivariant rational isomorphism with
both inverse identities, the rational multiplier, the dual-pullback
polarization equation and the compatible-orbit equation. `ClassCondition`
requires one actual representative satisfying both dimension
`[E : ℚ] * n²` and the positive Lie condition. The latter tests rank `n`
local freeness of the actual positive Lie tensor sheaf and equality of its two
`E` actions.

## Construction and proved laws

`pointMapRepresentative` uses the constructed generic actual polarized point
transport at the image of an original Harris level. It changes only the fixed
compatible level orbit. Its first projection is definitionally the identical
polarized object, and `objectCondition_pointMapRepresentative_iff` is therefore
definitional as well.

`ambientPointTowerIso` precomposes the existing actual polarized tower
isomorphism with `hodgeLevelFunctor D C`. Its representative formula is
proved. To establish `classCondition_pointMap`, the proof transports the one
actual representative witnessing `ClassCondition`; its object, dimension proof
and positive Lie proof are unchanged. Thus the target class has one witness
for both conditions. No dimension invariance under arbitrary rational
isomorphisms is used.

`classPointMap` restricts this actual ambient map to the existing joint image.
Its underlying-value and satisfying-representative formulas are proved.
`classPointEquiv` uses the reverse path as inverse; subtype extensionality and
the generic actual quotient inverse laws prove its inverse identities.
`classPointTowerIso` packages these equivalences into an isomorphism of the
original Harris class towers. Naturality follows from the ambient point
comparison and covers every original transporter arrow, including the existing
subgroup-forgetting maps and both Hecke legs. The forward and inverse
component formulas, path independence, identity, composition and reversal
laws are proved.

`inclusionNatTrans_classPointTowerIso` is the commuting square with inclusion
into the actual ambient polarized tower. The underlying joint
dimension-and-Lie action class is also unchanged:
`forgetDimensionLieAction_classPointMap` proves this using surjectivity of the
satisfying-representative constructor and the unchanged actual object.
`forgetDimensionLieActionNatTrans_classPointTowerIso` packages the equality
for the entire tower.

For connected, locally Noetherian `S` and algebraically closed endpoint
fields, `classGeometricPointTowerIso` chooses a path using the proved
`geometricPathExists`. Its equality with the comparison from every supplied
path follows from path independence. Its identity, composition and reversal
laws consequently have no chosen path in their statements. The canonical
comparison is between functors with values in `Type 1`.

## Provenance and scope

The provenance is derived: precompose the constructed actual polarized
comparison with the actual Harris level functor, restrict it using the
identical satisfying representative, and inherit the laws by subtype
extensionality. Path independence ultimately uses monodromy-fixed orbits;
it is not a claim that arbitrary frames have path-independent transport.
The final comparison uses proved path existence rather than an assumed
comparison or an arbitrary supplied class equivalence.

This is a fixed-base comparison. It does not yet construct an unpointed
varying-base polarized moduli presheaf, prove a square with arbitrary
base-scheme pullback, identify positive Lie compatibility with a determinant
or central trace condition, construct representing scheme levels, or descend
coefficient systems. These remain obligations of the larger geometry task.
