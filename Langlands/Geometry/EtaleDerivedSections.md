# Derived sections on a scheme's small-etale site

Author: Worker 13.

For an actual Mathlib scheme `X : Scheme.{u}` and commutative ring
`R : Type u`, this module uses the existing category of sheaves on
`X.smallEtaleTopology` with values in `ModuleCat.{u} R`. Mathlib proves that
this category is Grothendieck abelian using the affine-etale dense subsite.
Consequently it has enough injectives. Neither this property nor a desired
cohomology group is supplied as a new field or axiom.

`sections` is Mathlib's right adjoint to the constant-sheaf functor. Its
natural isomorphism to evaluation at the site's terminal object identifies
it with ordinary global sections. The adjunction gives additivity and
preservation of finite limits. Applying sections to Mathlib's chosen
injective resolution constructs `complex F`; `homotopyFunctor` is the
functorial derived object in the homotopy category, and `cohomology n` is
the corresponding module-valued right-derived functor. The representative
and homology isomorphisms use Mathlib's proved resolution construction.
Left exactness gives the natural isomorphism between zeroth cohomology
and global sections.

`constantCohomology` uses actual sheafified constant module coefficients.
Algebraic actions by automorphisms of a sheaf on the fixed scheme are
transported to cohomology, and every coefficient diagram gives a diagram
of cohomology modules, including maps between such diagrams. The diagram
index has independent object and morphism universes `uK` and `vK`; the acting
monoid has universe `w`. These operations do not assert that derived sections
commute with inverse limits, construct actions that move the scheme, or
prove continuity of Galois actions.

This is a derived implementation of the ordinary scheme-etale cohomology
input in Harris, *Galois properties of cohomological automorphic forms on
GL(n)*, Journal of Mathematics of Kyoto University 39-2 (1999), section 4,
printed p.309, Proposition 4.4, target of (4.4.1). Worker 13 read the original
page, including the geometric quotient in (4.3) and the definition of the
constant coefficient sheaf immediately before the proposition. The module
constructs the cohomology operation on genuine schemes; it does not construct
that proposition's particular Shimura scheme, its analytic uniformization,
or its spectral sequence. The `Ext` on p.309 is in the category of smooth
group representations and is not being replaced by sheaf `Ext`.

Registered source:
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`;
PDF SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.
The retained file is
`Harris (1999), Galois properties of cohomological automorphic forms on GL(n).pdf`.

Formal dependencies are Lean 4.34.0 and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`, especially `Sites.AffineEtale`,
site global sections, enough injectives and right-derived functors. This
module does not import pending project constructions.
