# Numerical representative images in the original Harris polarized tower

This derived construction restricts the original Harris polarized determinant
class tower to classes admitting one actual representative that also satisfies
the prescribed geometric dimension and central Lie trace formula. It constructs
the resulting transporter functor, its representative relation, natural maps,
subgroup forgetting and both Hecke legs. Its namespace is
`Langlands.Shimura.PEL.HarrisNumericalWeilLevel`.

## Source and scope

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura Varieties*
(2001), III.1, printed pages 89–91 / PDF pages 97–99, prescribes the dimension
`d n²`, states the central trace formula in Lemma III.1.2(3), and defines pointed
polarized PEL quadruples up to rational isogeny. Page 91 gives the
monodromy-invariant compatible level orbit, subgroup forgetting and right level
action. The registered original is
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

This module combines the existing actual constructions in
`HarrisPolarizedWeilTower` and `HarrisTaylorNumericalClasses`. It uses an
existential representative image for the dimension condition. Its level maps
preserve the same underlying object, so their restriction needs no theorem
asserting dimension invariance under rational isomorphism. This is a fixed-base,
fixed-point prerequisite of the PEL functor, rather than the source's complete
moduli functor or a representing scheme.

## Parameters and actual geometry

Fix totally real `E`, a CM number field `F` quadratic over `E`, the displayed
algebra and rational scalar towers, `D : CentralSimpleUnitaryData E F A n`,
Harris signature charts `C`, and their CM-section proof `hΦ`. The arithmetic
types and base scheme have universe zero. The original index category is
`HarrisLevel D`, the compact-open transporter category of the opposite original
finite-adelic Harris group.

The ambient tower uses the same whole Hodge-positive unit
`D.harrisHodgePELUnit C` for its positive auxiliary involution, rational regular
source, Weil form and continuous index transport. The auxiliary involution is
the left adjoint of that form and the original Harris involution is its right
adjoint. Every local star instance in this module is that constructed auxiliary
involution. It does not introduce another involution or positive witness.

Retain the ambient tower's explicit pullback-tensor comparison, composition,
unit, associativity, unitor and symmetry statements; Picard-zero pullback,
Mumford-bundle and universal-base-change statements; finite Weil transition
statement; rational profinite-integer/finite-adele comparison; and torsion
finite-étaleness statement. These are the named propositions of the imported
constructions, not supplied output schemes. The base `S` is quasi-separated.
The point `s : Spec Ω → S` requires only a field `Ω` and finiteness of the fibres
of all finite étale covers at `s`. Invertibility of every positive full-tower
torsion order and finite étaleness of the corresponding roots of unity remain
explicit. The actual dual-map `PositivePairAdditivity` proposition remains an
input.

There are two independently supplied base maps:

- `b : S → Spec (D.kottwitzCocharacterReflexField C)` maps the determinant
  coefficients to actual sections.
- `p : S → Spec F` maps the central trace coefficients to actual sections.

The module proves no identification or compatibility between these maps.
Also fix a CM number field `L` and an `L`-algebra structure on `F`.
For the numerical formula the source notation `E, F⁺, F, B` corresponds to
Lean `L, E, F, A`. The more general field parameters in the numerical API
do not assert the source's entire compositum setup.

`Data U` abbreviates the actual `HarrisLevelData` at `U`. It retains an actual
abelian scheme, faithful rational `A`-action, constructed dual and Poincaré
geometry, an actual polarization, involution compatibility, and a
monodromy-fixed orbit of actual tensor-linear Weil-compatible frames.
The polarization includes an isogeny and geometric-fibre ample Mumford
presentations. No representative frame or Tate-twist trivialization is chosen.
`Good` is the existing positive-object determinant predicate using `b`.

## Numerical image and equality

`NumericalObjectCondition X` is exactly
`HarrisTaylor.NumericalCondition L p E X.actionObj.abelianScheme
X.actionObj.action n`. Its first conjunct is the actual
`SmoothOfRelativeDimension ([E:ℚ] * n²)` predicate for the abelian scheme's
structure morphism. Its second conjunct is the central trace formula, on every
actual finite free Lie chart, central element and smaller open, using the
actual rational differential and the section map induced by `p`.

`ClassCondition q` states that there are actual data `x`, a determinant proof
`hx : Good x.1`, an equality `harrisClassOf x hx = q`, and a proof of
`NumericalObjectCondition x.1`. Thus one and the same representative satisfies
both restrictions. `IsoClass U` is the subtype of the actual ambient polarized
determinant classes defined by this image predicate.

`classOf` uses a supplied satisfying representative as its witness.
`classOf_surjective` extracts such a witness for every existing image class;
it asserts no nonemptiness. `classOf_eq_iff` reduces subtype equality to the
ambient quotient criterion. Its right side retains a rational unit multiplier,
an actual equivariant rational isomorphism with its inverse, the polarization
equation, and equality of the transported compatible orbit. It asserts no sign
condition on the rational unit. `val_injective` proves that forgetting the
numerical restriction embeds the image in the ambient class set.

The image definition does not assert that every ambient representative has the
prescribed geometric dimension. The central trace condition is invariant under
actual equivariant rational isomorphism by the imported theorem, but geometric
dimension invariance is a separate obligation.

## Transporter functor and natural maps

`mapRepresentative f` is the actual ambient representative map at
`hodgeLevelFunctor.map f`. It changes the compatible level orbit and retains
the underlying abelian scheme, action and polarization. Consequently
`classCondition_map` takes the satisfying witness at the source to a satisfying
witness at the target, retaining its determinant and numerical proofs.
`classMap` restricts the actual ambient class map. The `_val` and `_classOf`
formulas compute its underlying map and representative action.

`isoClassTower` is the resulting functor into `Type 1`. Its identity and
composition fields follow from the ambient functor laws by subtype
extensionality. `inclusionNatTrans` has component `Subtype.val`; its naturality
is definitional.

`forgetNumericalAction` forgets polarization and level into the actual
`HarrisTaylor.NumericalActionClass`. It uses the ambient determinant-action
forgetful map and extracts the same numerical representative to prove image
membership. Its `_classOf` formula computes the result on a representative.
`forgetNumericalAction_classMap` proves that all original level arrows leave
this numerical action class unchanged, by taking a satisfying representative.
This supplies the naturality field of `forgetNumericalActionNatTrans`, whose
target is the constant functor on numerical action classes.

## Subgroup forgetting and Hecke legs

`forgetLevel hU` is the class map of the actual original subgroup inclusion.
`heckeLeft U V g` and `heckeRight U V g` have common source the numerical
classes at `U ∩ g V g⁻¹`, computed in the opposite original Harris group, and
targets the classes at `U` and `V`. They apply the class map to the existing
left and right transporter arrows. The first has element one and the second
has element `g`; the index functor transports the latter to its actual regular
operator with the original multiplier. The finite rational module instance
needed for this compact-open intersection is derived from
`hodgeRationalPELConditions`; it is not an additional hypothesis.

The two `_classOf` formulas prove that these maps use precisely the actual
representative transports and retain both supplied conditions. Their
compatibility with the ambient tower and numerical action forgetting is covered
by the general class-map and naturality theorems above.

## Remaining comparisons

This construction supplies no base-scheme pullback, point-independence theorem,
away tower, or comparison between `p` and `b`. It does not prove equivalence
between the order-family determinant test, the central trace formula and the
full source Lie-plus condition. Source connectedness, local noetherianity and
sufficiently small levels are not imposed on these general parameters.
The complete Harris PEL functor, its extension to disconnected schemes,
representability, actual scheme levels, their complex comparison and
coefficient descent remain obligations of the broader construction.
