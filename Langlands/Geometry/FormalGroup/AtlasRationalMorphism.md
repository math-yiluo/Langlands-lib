# Rational formal atlas maps and quasi-isogenies

This is an internal construction from the integral atlas Hom module and the
existing coordinate rational Hom and quasi-isogeny APIs. It extends actual
formal maps by tensor products and carries their formal compatibility equations
to rational chart maps. No new original-literature assertion is used here.

## Parameters and rational Hom

Let O and R be commutative rings, with an O-algebra structure on R. Let F be a
field with an O-algebra structure. The coordinate types are finite. The atlases
X and Y are the existing `BasicAtlas` objects, with a supplied equality
`h : X.opens = Y.opens` of their sets of principal-open generators. Coefficient
test algebras are `CommAlgCat.{v} R`, in the universe of R.

`BasicAtlas.RationalHom F X Y h` is `F tensor[O] BasicAtlas.Hom X Y h`.
`sourceTensorEquiv` exchanges the factors to give the order Hom tensor F.
`ofHom` is the O-linear map sending f to `1 tensor f`; no injectivity is asserted.
Every rational map is a finite sum of simple tensors of actual integral formal
atlas maps. The integral maps already satisfy coefficient naturality and the
formal transition squares.

## Formal composition and chart evaluation

`compLinearO` extends integral formal composition using the O-bilinear
multiplication of F. Thus, with f applied first,

`comp (a tensor g) (b tensor f) = (a*b) tensor (g.comp f)`.

Tensor induction proves both identity laws and associativity. It also proves
linearity in each argument over F; `compLinear` packages this bilinearity.
`ofHom` preserves identities and composition. On rational endomorphisms of one
atlas, multiplication is this composition and the unit is the rational integral
identity. Natural and integer casts are their casts in F tensored with that
integral identity, yielding a ring compatible with the tensor additive group.

For a test algebra A and a target chart b whose generator becomes a unit in A,
`onChart A b hb` is the F-linear scalar extension of the integral chart-evaluation
map. Its source chart is `sourceChart h b`. Its value lies in the actual
coordinate `ModuleLaw.RationalHom` between the two coefficient-extended formal
module laws. On a simple tensor its formula is

`onChart A b hb (a tensor f) = a tensor (f.hom A b hb)`.

The formulas `onChart_ofHom`, `onChart_id` and `onChart_comp` identify evaluation
of integral maps, identities and composition. For composition the first map is
evaluated at b and the second at the corresponding intermediate source chart.
The coefficient lifts and chart transports are those of the existing atlas.

`onChart_transition` proves the formal square between any two usable charts in
A. Its two transition maps are the actual integral atlas transitions included
in coordinate rational Hom. `onChart_natural` proves coefficient naturality for
an R-algebra morphism from A to B. The comparison maps in this equation are the
actual identity-coordinate isomorphisms `coefficientTriangleIso`; the map from
the A chart is extended by the actual coefficient O-algebra map into B.
Both equations are equalities of rational formal coordinate maps. Their proofs
use tensor induction, reduce simple tensors to the inherited formal equations,
and use the identity-coordinate formulas for the coefficient comparisons.

## Quasi-isogenies

Here O is additionally a domain and F its fraction field.
`BasicAtlas.QuasiIsogeny F X Y h` consists of a rational map from X to Y and a
rational map back with both composition equations equal to the respective
rational identities. The equality of covers for the inverse is `h.symm`.

`refl`, `symm` and `trans` supply the identity, inverse and composition, using
the actual rational formal composition above. `ofIso` includes every actual
integral atlas isomorphism. Associativity and the identity equations show that
any rational left inverse is the stored inverse (`inv_unique`), so equality of
the forward maps implies equality of the quasi-isogenies (`ext_hom`).
`QuasiIsogeny.onChart` evaluates both maps and uses preservation of composition
and identity to construct a coordinate `ModuleLaw.QuasiIsogeny`.

## Scope

This is global tensor Hom on one common cover. No equality with arbitrary
locally rational maps or a rational Hom sheaf is asserted. Rational maps are
not evaluated directly on the integral nilpotent tuple groups; chart evaluation
lands in formal coordinate tensor Hom. General-refinement transport, local
rational gluing, full-order equivariance, height and framing remain separate.
No classification, representing object, universal object or representability
conclusion is assumed or constructed.
