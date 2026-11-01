# Pointed pullback of actual Harris positive Lie and dimension classes

This module constructs pointed base pullback of the actual positive polarized
Harris level classes restricted by the prescribed geometric dimension and the
original positive Lie condition. It uses the existing actual polarized
representative pullback and its proved rational-isogeny relation preservation;
it does not replace that quotient by the action quotient or a numerical trace
condition.

The arithmetic inputs are the central simple unitary datum `D` over the totally
real number field `E`, a totally complex quadratic extension `F/E`, its algebra
`A`, and the signature charts `C`. The positive auxiliary left involution and
Hodge form are those of the existing construction. The imaginary quadratic CM
number field `L` maps into `F`. The base consists of actual schemes `S`, `T`, an
arbitrary morphism `b : T ⟶ S`, and a structural map `p : S ⟶ Spec F`; the target
structure is `b ≫ p`. Schemes and these arithmetic types have universe zero.
No CM-section property, determinant equality or trace identity is an input.

The explicit tensor/Picard construction assumptions remain: tensor-pullback
invertibility, composition, unit, associativity, left-unitor and symmetry
coherence, Picard-zero pullback, the Mumford-bundle statement and Picard-zero
universal base change. For the pointed level construction one also supplies the
finite Weil transition and torsion finite-etale statements, the rational
profinite-integer/finite-adele comparison, quasi-separatedness of both bases,
a field-valued point `t` on `T`, finite fibers of finite-etale covers at `t`
and `t ≫ b`, invertibility of every positive torsion index and finite etale
roots of unity on both bases. Ordered-pair dual additivity is supplied on both
bases. These are inherited construction inputs, not conclusions of this file.
The source uses an algebraically closed geometric point; the imported
construction works with the stated field-valued point and fiber hypotheses.

`PositivePullbackDualData` reuses the existing
`HarrisPolarizedWeilLevel.PositivePullbackDualData` definition, retaining the
same actual pullback and parameter order.

The family `dualData` specifies actual dual-scheme, geometric, inverse-Poincare,
evaluation and dual-endomorphism-additivity data for each source object's own
actual abelian-scheme pullback. It cannot specify a different output abelian
scheme, polarized action, level orbit or quotient map. This file does not prove
existence or choice-independence of that family. In contrast, integral dual
naturality and full polarization stability are supplied internally by the
published theorems `dualAbelianBaseChangeNaturality` and
`polarizationBaseChange`. Lie naturality is also supplied internally by the
positive Lie pullback theorem. None of those three propositions remains an
extra hypothesis of the new constructions.

`levelDataBaseChange_objectCondition` applies the proved actual dimension and
positive Lie pullback theorem to the underlying rational action of the very
same polarized representative. The existing `levelDataBaseChange` constructs
its actual pulled-back positive polarized action and fixed compatible Weil
orbit. Its faithfulness comes from the source level's nonempty frame type; no
monodromy-fixed frame representative is assumed. Its integral polarization is
transported through the canonical comparison with the dual. The positive Lie
test concerns the original-order positive tensor sheaf: actual local rank `n`
and equality of its two `E` actions. The dimension is `[E : ℚ] * n²` for this
same abelian scheme's actual structure map.

`ambientClassBaseChange_condition` uses the pulled-back source witness to prove
preservation of the joint representative image. The ambient map is the existing
quotient map whose relation contains an actual equivariant rational isomorphism
with inverse, the geometric polarization multiplier equation for a rational
unit, and the compatible-orbit equality. Its proved pullback uses the same unit
and the image of that actual rational isomorphism. Thus the restriction assumes
neither dimension invariance under arbitrary rational isomorphism nor a
separately supplied relation-preservation theorem.

`classBaseChange` is the restriction to the joint image. Its value is the
constructed ambient quotient pullback, and `classBaseChange_classOf` proves
that it sends a satisfying representative to exactly its own constructed
polarized level pullback with both conditions. No new representative is
chosen when making this restriction.

`classTowerBaseChange` is a natural transformation between the existing joint
class towers over the original opposite Harris group's compact-open
transporter category. Subtype extensionality reduces naturality to the
existing actual ambient tower pullback. This includes subgroup inclusions and
the original Hecke transporter arrows. `classTowerBaseChange_inclusion` proves
commutation with the injective inclusions into the ambient polarized towers.

`forgetDimensionLieAction_baseChange_val` proves that forgetting actual
polarization and level gives the actual rational action quotient pullback.
The subtype-valued theorem `forgetDimensionLieAction_baseChange` identifies it
with the map of the already constructed `dimensionLieActionPresheaf` for the
actual arrow `Over.mk (b ≫ p) ⟶ Over.mk p`. The induced constant-level-tower
map and `classTowerBaseChange_forgetDimensionLieAction` give the resulting
natural square. Quotient representative surjectivity and the explicit
constructor formulas prove these equalities; the dimension and Lie witnesses
continue to refer to the same underlying object.

The provenance is a derived construction from the actual imported pullbacks,
their proved relation and level naturality, the positive Lie pullback, and the
same-representative dimension image. The motivating original source is Harris
and Taylor, *The Geometry and Cohomology of Some Simple Shimura Varieties*
(2001), III.1, printed pp.89–91 / PDF pp.97–99, registered as
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
Those pages prescribe dimension, define the positive Lie condition, then define
polarized compatible level quadruples and their isogeny relation. The source's
imaginary quadratic field `E`, CM field `F`, real field `F⁺`, algebra `B` and
abelian scheme `A` are this file's `L`, `F`, `E`, `A` and underlying abelian
scheme. The rational-isomorphism quotient and broader base hypotheses retain
the existing construction's explicit comparison boundaries.

No flatness, reducedness, connectedness or local noetherianity of the bases is
required here. This is pointed pullback with the supplied dual family. It does
not establish identity/composition coherence for successive choices of that
family, independence of geometric point, an unpointed polarized moduli
presheaf, the source trace equivalence, equivalence with geometric-isogeny
relations on arbitrary schemes, scheme representability, canonical models,
scheme-valued level morphisms or coefficient descent. Those remain separate
obligations of the broader geometric task.
