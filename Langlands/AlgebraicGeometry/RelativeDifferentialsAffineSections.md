# Actual affine sections of relative differentials

Let `f : X ⟶ S` be a scheme morphism, let `U` be an affine open in `S`,
and let `V` be an affine open in `X` contained in `f⁻¹(U)`. Equip
`Γ(X,V)` with the `Γ(S,U)`-algebra structure of the actual map
`f.appLE U V h`.

`relativeDifferentialsSectionsIso f hU hV h` is an isomorphism of
`Γ(X,V)`-modules between actual sections of
`Langlands.Scheme.relativeDifferentials f` over `V` and
`KaehlerDifferential Γ(S,U) Γ(X,V)`.
No smoothness, noetherian or affineness hypothesis on the whole morphism
is needed; affineness is required of the two specified opens.

The construction is an internal composition of existing canonical
comparisons. First, pull sections to the spectrum of the actual ring
`Γ(X,V)` using `fromSpecSectionsLinear`, whose bijectivity follows from
the affine chart. Next, apply the invertible affine-chart differential
square map. Finally, invert the algebraic-to-Spec differential comparison
and the tilde global-sections isomorphism.

`relativeDifferentialsSectionsIso_fac` verifies the factorization through
these two canonical maps to the Spec differential module. Thus the
comparison is tied to the actual chart and differential maps, rather
than merely chosen from existence of a module isomorphism.
The proof expands the composition and cancels the specified inverse
isomorphisms.

The provenance is the Library's affine-chart and spectrum differential
comparisons and affine pullback section maps. No external source claim
or compatibility across different chart choices is added here.
