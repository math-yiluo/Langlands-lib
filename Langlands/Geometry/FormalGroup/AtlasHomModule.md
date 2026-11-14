# The integral module of formal atlas homomorphisms

This is internal infrastructure for formal modules on principal affine covers.
It extends the actual same-cover formal morphisms of
[AtlasMorphism](AtlasMorphism.md), using the coordinate-level Hom module and
bilinear composition of [ModuleMorphism](ModuleMorphism.md). It introduces no
new external source assertion.

The parameters are commutative rings O and R, an O-algebra structure on R, and
finite coordinate types σ, τ and υ. For atlases X, Y and Z, the respective cover
equalities h : X.opens = Y.opens and k : Y.opens = Z.opens are supplied.
The coefficient test algebras have the same universe as R, as in `BasicAtlas`.
All declarations lie in `Langlands.FormalGroup.ModuleLaw.BasicAtlas.Hom`, except
the private coefficient helper.

## Formal operations and their compatibility

The `Zero`, `Add`, `SMul O` and `Neg` instances act on the actual formal chart
maps for every coefficient algebra A, target chart b and unit witness hb.
The chart formulas are:

- `zero_hom`: the zero atlas map is the zero formal homomorphism.
- `add_hom`: the sum has chart map f.hom + g.hom, formed using the target's
  formal group addition law.
- `smul_hom`: multiplication by a in O has chart map a • f.hom, formed by
  postcomposing with the target's formal scalar action.
- `neg_hom`: negation has chart map -(f.hom). The atlas construction uses the
  scalar -1, and coordinate-level `neg_one_smul` proves this formula.

These operations retain both defining formal conditions of `BasicAtlas.Hom`.
For coefficient naturality, the private `map_coefficientLift` transports an
arbitrary coordinate map from a principal localization along the actual
coefficient triangle. Its proof uses composition of coefficient maps and
uniqueness of the localization lift. This applies to the target addition law
and to every scalar action. Coefficient extension preserves formal composition
and pairing, so the original naturality equations for f and g prove naturality
of their sum and scalar multiples. Zero uses the coefficient-zero law.
For formal transition squares, coordinate-level composition is O-bilinear;
the original transition equations therefore prove the new equations. Thus the
construction supplies full formal atlas maps over every test algebra.

Chartwise extensionality proves the `AddCommGroup` and `Module O` instances by
the corresponding coordinate Hom laws. `chartLinear A b hb` is the O-linear
map sending an atlas homomorphism to its actual formal homomorphism on that
test chart.

## Families, composition and endomorphisms

`onPoints_zero`, `onPoints_add`, `onPoints_neg` and `onPoints_smul` show that the
operations have their expected values on complete compatible families of
nilpotent chart tuples. The proofs compare every component of the family and
use coordinate-level evaluation. Consequently `onPointsLinear A` is O-linear
from formal atlas Hom to the O-linear maps X.Point A → Y.Point A. Its values are
the existing family maps, whose coefficient naturality was proved in
`AtlasMorphism`; no arbitrary family map is used to define a formal map.

`comp_add`, `add_comp`, `comp_smul`, `smul_comp`, `comp_zero` and `zero_comp`
are equations of formal atlas homomorphisms. Each follows by chartwise
extensionality from coordinate-level bilinearity. They construct
`compLinear : Hom Y Z k →ₗ[O] Hom X Y h →ₗ[O] Hom X Z (h.trans k)`, with the
right map applied first. The existing identity and associativity laws then
give `Ring (Hom X X rfl)`, whose product is formal composition and whose unit
is the actual identity atlas map.

## Scope

The maps require equal principal-open covers and finite coordinate types.
This unit supplies integral O-linear maps. Rational maps, full-order
commutation, refinement and gluing of rational maps, quasi-isogenies and
framing triples require further constructions. No representing or universal
object, classification, height, polarization or group action is assumed or
constructed here.
