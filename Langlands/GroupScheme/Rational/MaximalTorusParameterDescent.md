# Descending parameter points of conjugate tori

Author: Worker 1420.

This internal, derived module turns a conjugate of the maximal torus that is
defined over a purely transcendental function field into an actual
parametrization of the parameter scheme `Q`. The field `k : Type u` is
arbitrary; there is no infinitude, perfection or characteristic assumption.
Apart from the parameter map `q`, every hypothesis concerns only `G` and `j₀`.

`TorusConjugateDescends j₀ π g` is defined for morphisms `π : X → Y` and
`g : X → G.X` of schemes over `Spec k`. It says the following. For every
scheme `U` over `k` and every two points `a₁, a₂ : U → X` with
`a₁ ≫ π = a₂ ≫ π`, the point `(a₁ ≫ g)⁻¹ * (a₂ ≫ g)` of `G` over `U` lies in
the all-test torus normalizer `torusNormalizer j₀`. Informally, the conjugates
of the torus by the two pullbacks of `g` to the kernel pair of `π` agree. This
is a compatibility condition only. The definition puts no hypothesis on `π`, and
the module never claims or uses that the conjugate torus is the base change of
a torus over `Y`. For example, the condition holds automatically whenever `π` is
a monomorphism, and a conjugate torus over a dense open of `Y` need not extend
to a torus over `Y`. The condition quantifies over all test schemes and all such
pairs. It is not restricted to field-valued points. What descends in this module
is the parameter point `g ≫ q`, by the next lemma, and only along effective
epimorphisms.

`rationalFunctionFieldOver k n` is `Spec` of Mathlib's function field of
`𝔸(n; Spec k)` (the stalk at the generic point). It is a scheme over `Spec k`
through the canonical map to affine space followed by the structure map.

`IsMaximalTorusParameter.exists_desc` assumes an actual parameter map `q`
for `j₀`, a morphism `π` over `k` whose underlying scheme morphism is an
effective epimorphism, and `TorusConjugateDescends j₀ π g`. It constructs
`e : Y → Q` over `k` with `π ≫ e = g ≫ q`. If two scheme points
`z₁, z₂ : Z → X` agree after `π`, the proof regards `Z` as a scheme over `k`
through `z₁`. It obtains two points of `X` over `k` with equal images in `Y`.
The descent hypothesis puts their quotient in the normalizer, and the all-test
fiber relation `fiber_iff` gives `z₁ ≫ g ≫ q = z₂ ≫ g ≫ q`. Mathlib's
`EffectiveEpi.desc` then produces `e.left`. It is a morphism over `k`
because `π.left` is an epimorphism and `π ≫ e ≫ Q.hom = π ≫ Y.hom`.

`IsMaximalTorusParameter.hasDenseRationalFunctionFieldPoint` takes `Y` to be
`rationalFunctionFieldOver k n` for a finite coordinate type `n`. It requires
`π.left` to be flat, surjective and quasi-compact, so Mathlib's fpqc instance
(`Mathlib.AlgebraicGeometry.Sites.Fpqc`) makes it an effective epimorphism. For
example, `π` may be the spectrum of a field extension `L` of the function
field. If moreover `g ≫ q` has dense range, the descended `e` gives
`HasDenseRationalFunctionFieldPoint k Q`. Its range contains the range of
`π ≫ e = g ≫ q`.

`IsMaximalTorusParameter.isUnirational_of_torusConjugateDescends` assumes
instead that `g` itself has dense range in `G`. Then `g ≫ q` has dense range
because `q` is surjective and continuous, and `Q` is locally of finite type
over `k` by the parameter predicate. So `HasDenseRationalFunctionFieldPoint.isUnirational`
from `UnirationalSpreading` gives `IsUnirational k Q` for the same supplied
`Q`.

Provenance: derived from the published `IsMaximalTorusParameter` predicate
(its surjectivity, finite type and all-test fiber fields), the published
`torusNormalizer`, the helper module `UnirationalSpreading`, and pinned
Mathlib's effective epimorphisms of schemes (`EffectiveEpi.desc` and the fpqc
instance in `AlgebraicGeometry/Sites/Fpqc`). It is the step in SGA 3,
Exposé XIV, Théorème 6.1, where the generic Cartan subgroup over the function
field of a rational variety gives a generic point of the scheme of maximal
tori. This module does not construct such a conjugating point `g`. That
construction is the remaining substance of the unirationality target.
