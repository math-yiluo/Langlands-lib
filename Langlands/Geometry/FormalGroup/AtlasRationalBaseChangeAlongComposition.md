# Natural rational comparison of successive supplied coefficient maps

This is an internal construction from `AtlasRationalBaseChangeComposition`,
`AtlasRationalBaseChangeAlong` and `AtlasBaseChangeAlongComposition`. The
last module already constructs the actual successive-to-direct isomorphism
over supplied scalar structures. This module proves its naturality and
rationalizes that same isomorphism. It makes no additional original-literature
assertion.

Let `O` be a commutative ring, `R`, `S`, `T` commutative `O`-algebras in the same
universe, and `f : R →ₐ[O] S`, `g : S →ₐ[O] T` supplied algebra maps. The
original atlases may have different finite coordinate types and have equal
principal covers. Let `F` be a field with an `O`-algebra structure. Rational
Hom is the global tensor `F ⊗[O] BasicAtlas.Hom` of actual integral formal
atlas maps. It is not defined by separately gluing rational maps on charts.

The auxiliary `baseCompReAlgebraMapOpens_eq` records equality of successive
covers after intermediate and final scalar transport. The corresponding
`Hom.baseCompReAlgebra_natural` and `baseCompReAlgebra_inv_natural` equations
use a test algebra `S` over `R` and a test algebra `T` over `S`, an equality
`e` from the composite intermediate `O`-algebra structure to a supplied
structure `β`, and an equality `d` from the resulting final composite
structure to a supplied structure `γ`. The direct transport uses
`coefficientAlgebra_comp_transport` followed by `d`. Eliminating `e` and `d`
reduces both equations to the existing raw integral naturality laws. Thus the
maps are exactly those of `baseCompReAlgebraIso`, with the original preimage
choices retained.

`RationalHom.baseCompReAlgebra_natural` and
`baseCompReAlgebra_inv_natural` perform the same two transports on the raw
global rational equations. Eliminating the two scalar equalities proves
these equations for every global tensor. No new chart-evaluation
injectivity or local gluing result is used.

`baseAlongCompMapOpens_eq` specializes the cover equality to `f` and `g`.
`Hom.baseAlongComp_natural` says that extending an actual formal map twice
and then applying the target's actual `baseAlongCompIso.hom` equals applying
the source's comparison and then extending directly along `g.comp f`.
`baseAlongComp_inv_natural` gives the reverse square using the actual inverse.
These are specializations of the transported integral equations to
`coefficientTest f`, `coefficientTest g` and their structural equalities
`coefficientAlgebraAlong_eq`.

`RationalHom.baseAlongComp_natural` and `baseAlongComp_inv_natural` give
the same two squares for every rational formal map. They specialize the
transported rational equations, retaining the independently supplied
`O`-algebra structures of both `S` and `T`. The comparison maps are the
rationalizations of the actual transported integral maps.

For quasi-isogenies assume additionally that `O` is a domain and `F` is its
fraction field. `BasicAtlas.baseAlongCompQuasiIsogeny X f g` applies
`QuasiIsogeny.ofIso` to `X.baseAlongCompIso f g`, retaining both rationalized
maps and both inverse equations. The `_hom` and `_inv` lemmas expose these
maps. `QuasiIsogeny.baseAlongComp_natural` and
`baseAlongComp_inv_natural` give the forward and reverse whole-quasi-isogeny
squares. Forward-map extensionality and the corresponding rational equations
prove them; uniqueness of a two-sided inverse also identifies their inverses.

These are naturality laws for the specified actual two-map comparison. They
do not assert strict equality of atlases, independence of arbitrary
comparison witnesses, three-map or identity-unit coherence, full-order
equivariance, local rational gluing, heights, framing, polarization, descent,
levels or representability.
