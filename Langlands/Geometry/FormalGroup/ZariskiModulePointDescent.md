# Principal-open descent of actual formal O-module points

This derived unit equips the matching tuples of `ZariskiPointDescent` with
the actual formal O-module operations and constructs the O-linear gluing
equivalence `ModuleLaw.basicPointEquiv`.

## Provenance and scope

The provenance is Drinfeld's convention of gluing formal groups over
localizations, *Coverings of p-adic symmetric regions* (1976), printed p.109,
paragraph before section 2 (PDF page 3); registered source
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The linear equivalence is derived infrastructure and is not asserted as a
separate theorem in that source.

O and R are commutative rings with an O-algebra structure on R, σ is a finite
coordinate type in `Type`, κ is any type in `Type`, and the possibly infinite
set of principal-open generators spans the unit ideal. The formal-module law
is global and fixed. This unit does not assert gluing of varying chart laws,
atlas refinement, arbitrary site descent, moduli, representability or levels.
No reducedness, Noetherian hypothesis, flatness assumption or uniform bound
on local nilpotence exponents is used. The matching family carrier has
universe v, the universe of R; taking κ to be `Empty` gives the actual
nilpotent tuple carriers of the point functor.

## Actual coefficient maps and module operations

`mapPointsAlong` takes two O-algebra maps φ : R → S and ψ : R → T, a
ring homomorphism f : S → T and the coefficient-triangle equality
f ∘ φ = ψ. It constructs a linear map from the series-valued points of
`M.map φ` to those of `M.map ψ`. Its underlying function applies f to
each power-series coefficient. S and T may have arbitrary carrier
universes and arbitrary specified O-algebra structures; the supplied
triangle is the exact condition used by the proof.

For addition, `SeriesPoint.map_eval` moves coefficient change through
evaluation of the actual formal addition map, and `map_pair` moves it
through the two input tuples. `CoordinateMap.map_ringHom_comp` and the
coefficient triangle then identify that formal addition with the target
law's addition. The same evaluation and coefficient-composition
identities prove compatibility with the formal scalar action for every
c ∈ O. Thus linearity is proved using the formal-module laws, rather
than using the coordinatewise additive structure on power series.
`mapPointsAlong_apply` records the actual coefficient-map formula.

`basicOverlapLeft a b` and `basicOverlapRight a b` specialize this map to
R[1/a] → R[1/(ab)] and R[1/b] → R[1/(ab)]. Their coefficient triangles
are proved using Mathlib's `awayToAwayRight_eq` and `awayToAwayLeft_eq`.
Both maps take values in points of the same actual base-changed law.

## The matching submodule and gluing equivalence

`BasicPointFamily s` is the product of the actual O-modules
`(M.map (basicCoefficientMap a)).Point κ` for a ∈ s.
`basicPointSubmodule s` uses the raw condition
`SeriesPoint.BasicCompatible s` as its carrier predicate. The preceding
linear overlap maps prove closure under zero, addition and O-scalars:
each matching equation is an equality of linear images in the joint
localization. `MatchingBasicPoint s` is that solution submodule.

`toBasicPoints s` restricts each global point using
`M.mapPoints (basicCoefficientMap a)`. Its image satisfies the matching
equations by `SeriesPoint.basicCompatible_map`; its linearity follows
component by component from those actual formal-module restriction maps.

`basicPointEquiv s hs` uses this linear restriction as its forward map.
The inverse is the explicit coefficient gluing
`SeriesPoint.glueBasic s hs` from the preceding tuple-descent unit.
That construction proves substitutability through local detection of
nilpotence for the glued constant coefficients. The left inverse uses
`SeriesPoint.ext_basic` and the gluing restriction formula; the right
inverse uses that formula at each local tuple. These proofs do not assume
a gluing operator or a comparison isomorphism as input.

`basicPointEquiv_apply` exposes each localized tuple of a global point.
`basicPointEquiv_symm_map` states that the inverse has exactly the
prescribed localized tuples. The resulting linear equivalence includes
linearity of the gluing inverse. It therefore gives both existence and
uniqueness of gluing with the actual formal-module operations, for
arbitrary κ as well as the nilpotent-point specialization.
