# Polarized determinant classes indexed by the original Harris group

This derived construction reindexes the actual positive-auxiliary polarized
Weil-level determinant classes by compact open subgroups of the opposite
original Harris similitude group. It constructs a genuine transporter functor,
its exact representative relation, natural forgetful maps, subgroup forgetting
and both Hecke legs. Its namespace is
`Langlands.Shimura.PEL.HarrisPolarizedWeilLevel`.

## Source and derivation

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura Varieties*
(2001), printed p.18 / PDF p.26, defines an isogeny as an invertible rational
homomorphism and a polarization by its geometric fibres. Section III.1,
printed p.91 / PDF p.99, describes the pointed PEL quadruples, the
monodromy-invariant orbit of compatible frames, their rational-isogeny
relation, subgroup forgetting and the right action `η ↦ η ∘ g` under the
condition `g⁻¹ U g ≤ V`. Printed p.92 / PDF p.100 describes the corresponding
complex quotient action. The registered source is
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

The new functor is the composite of the published
`harrisWeilFiniteAdelicLevelFunctor` in `AbelianScheme.Tate.HarrisWeilLevels`
with `positiveIsoClassTower` in `Shimura.PEL.HarrisPolarizedWeilClasses`.
The first is the actual regular-source continuous group transport; the second
is a quotient of actual geometric data restricted by the actual determinant
condition. Reindexing preserves these constructions and their proved laws.
It does not identify the resulting fixed-base class tower with the full
Harris–Taylor moduli functor or with a representing scheme.

## The identical Hodge-positive witness

Fix totally real `E`, totally complex quadratic `F/E`,
`D : CentralSimpleUnitaryData E F A n`, the displayed algebra structures and
rational scalar towers, and Harris signature charts `C`. All arithmetic types
have universe zero. Put `β = D.harrisHodgePELUnit C`. This is the same whole
Hodge-positive witness used to construct `D.harrisHodgePELAlgebra C` and
`D.harrisHodgePELForm C`. The index transport does not choose a second
positive skew unit.

The scalar-extension form is definitionally
`(D.skewTwist β (D.harrisHodgePELUnit_skew C)).tracePairing β⁻¹`.
The constructed positive auxiliary involution is its left adjoint; the original
Harris involution is its right adjoint. The actual regular left `A`-module is
`A`. The imported continuous group equivalence `e` sends an element of the
opposite original finite-adelic Harris group to the regular operator
`x ↦ x * g.unop.val.1`, with the original multiplier. The opposite group
accounts for the order of composing these operators.

`HarrisLevel D` is the actual compact-open transporter category of this
opposite original group. An arrow `f : U ⟶ V` has an element satisfying
`f.element⁻¹ U f.element ≤ V`. `hodgeLevelFunctor D C` transports it to the
compact-open category of the scalar-extension similitude group of the same
form. The `_obj_mem` and `_map_element` theorems compute subgroup membership
and the transported element. `_inclusion` identifies an inclusion arrow with
the actual transported inclusion. These are specializations of the published
transport laws, rather than assumptions about arbitrary index maps.

`hodgeRationalPELConditions` proves the finite, faithful, alternating,
nondegenerate and left-adjoint rational PEL source conditions for precisely
this form and auxiliary involution. The proof specializes the generic
published theorem to `β`. In particular its `finite_module` field derives
`Module.Finite ℚ A`; no independent finite-dimensionality hypothesis is
needed to form the Hecke intersections. `hodgeLevelFunctor_heckeLevel` proves
that transport preserves the actual intermediate subgroup
`U ∩ g V g⁻¹`, computed in the opposite group.

## Actual representatives and classes

Fix an actual scheme `S`, its actual morphism `b` to the constructed
cocharacter-reflex field, and a CM-section proof `hΦ`. Retain the displayed
pullback-tensor comparison, composition, unit, associativity, unitor and symmetry
statements; Picard-zero stability, Mumford-bundle Picard-zero and universal
base-change statements; finite Weil transition; the rational
profinite-integer/finite-adele scalar comparison; and torsion finite étaleness.
Fix a field-valued point `s : Spec Ω → S`, with finite fibres for every finite
étale cover at `s`. The API assumes only `[Field Ω]`. Invertibility of every
positive full-tower torsion order, finite étale roots of unity, and
quasi-separatedness of `S` remain explicit. The actual dual-map
`PositivePairAdditivity` statement also remains an input.

At an original level `U`, `HarrisLevelData U` is the existing
`PositiveLevelData` at `hodgeLevelFunctor.obj U`. Its actual abelian scheme,
faithful rational `A`-action, constructed dual and Poincaré geometry,
polarization and involution compatibility are unchanged. Its level is a
monodromy-fixed orbit of actual tensor-linear Weil-compatible frames. The
existential trivialization of the actual Tate twist is the existing one;
no representative of an orbit or trivialization is chosen by reindexing.
The polarization includes an actual isogeny and ample Mumford presentations
on geometric fibres as in the imported construction.

`HarrisIsoClass U` is the existing positive polarized isogeny-class subtype
at that transported level. Its determinant condition is the published
`HarrisRationalLieDeterminantCondition` on the actual Lie action, with reflex
coefficients mapped through `b`. It is the order-family determinant test;
this module does not replace it by the separate central trace condition.

`harrisClassOf x hx` forms the class of an actual representative and its
determinant proof. `harrisClassOf_surjective` gives such a representative for
every existing class, without asserting nonemptiness.
`harrisClassOf_eq_iff` retains exactly the existing relation: a rational unit
`q`, an actual equivariant rational isomorphism `e`, the equation
`eᵛ ∘ λ_y ∘ e = (q : ℚ) • λ_x`, and equality of the transported compatible
level orbit with the target orbit. The rational inverse is part of `e`.
No sign condition is asserted for `q`. The proof is the existing exact
quotient criterion at the transported subgroup.

## Functor, forgetting and Hecke maps

`harrisIsoClassTower` is the composite transporter functor into `Type 1`.
Its identity and composition laws are those of actual functor composition.
Its object formula is definitional.
`harrisIsoClassTower_map_classOf` proves that every original arrow uses the
actual polarized representative map at `hodgeLevelFunctor.map f`. This keeps
the underlying object and determinant proof, and acts on its compatible
orbit by the actual transported regular operator. Thus the original right
level action has the precise opposite-group convention stated above.

`harrisForgetDeterminantActionNatTrans` naturally forgets polarization and
level into the actual determinant action class. `harrisInclusionNatTrans`
is natural inclusion into the transported ambient polarized class tower.
Both are obtained by left whiskering the existing natural transformations
with the actual index functor, so their naturality fields are proved.

`harrisForgetLevel` is the map of an original subgroup inclusion. The theorem
`harrisForgetLevel_eq` identifies it with `positiveForgetLevel` for the
actual transported subgroups, by the index inclusion formula and function
extensionality.

`harrisHeckeLeft U V g` and `harrisHeckeRight U V g` are the two maps from
classes at `U ∩ g V g⁻¹` to classes at `U` and `V`. Their source finiteness
instance is derived from `hodgeRationalPELConditions` as above. The two
`_classOf` formulas identify them with the actual representative maps for
the transported left and right arrows. The first arrow has element one;
the second has element `g`, transported to `e(g)`, with its multiplier.
Together with `hodgeLevelFunctor_heckeLevel` these are the actual compact-open
Hecke span for this fixed-base class tower. These representative formulas
are definitional consequences of the composite functor.

## Retained obligations

This is a fixed-base, fixed-point full finite-adelic tower. It adds no
base-scheme pullback, point-independence comparison, or away tower. It does
not impose the source's prescribed relative dimension or prove that the
order-family determinant condition is equivalent to the full Harris–Taylor
Lie compatibility condition. The source's connectedness, local noetherianity
and sufficiently-small-level hypotheses are not asserted for its general
parameters. Extension over disconnected schemes, the full Harris PEL
functor, precise representability, actual scheme levels, their comparison
with the complex tower, and coefficient descent remain obligations of the
broader construction. This focused reindexing result asserts none of those
existence or comparison theorems.
