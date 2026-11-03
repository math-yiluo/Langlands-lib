# Finite presentations of affine sheaves across nilpotent base reduction

This is an internal construction from published algebraic and sheaf results. Let
`A → B` be an algebra, `I` a nilpotent ideal of `A`, and `M` an existing
quasi-coherent ordinary module sheaf on `Spec B`. The affine section module
`N = moduleSpecΓFunctor.obj M` has a compatible `A`-module structure and is
assumed flat over `A`. Put `J = IB`, the image ideal in `B`.

The input is a finite global sheaf presentation of the actual ordinary
pullback of `M` along `Spec(B/J) → Spec B`, whose ring map is the quotient map.
`finitePresentation_moduleSpecΓFunctor_of_base_nilpotent` proves that `N` is
finitely presented over `B`. `exists_presentation_of_base_nilpotent` gives a
finite global presentation of `M`, and
`isFinitePresentation_of_base_nilpotent` deduces local finite presentation in
the existing `SheafOfModules.IsFinitePresentation` sense.
The noncomputable constructor `finitePresentationOfBaseNilpotent` chooses such
a presentation and returns it in the subtype `{Q : M.Presentation // Q.IsFinite}`.

The proof first applies
`finitePresentation_moduleSpecΓFunctor_of_presentation` to the reduced
sheaf presentation. The canonical `affineScalarSectionsIso`, induced by the
actual pullback adjunction unit, identifies its section module with
`(B/J) ⊗[B] N`. Quasi-coherence supplies this identification without a
flatness hypothesis on `B`. The algebraic
`Langlands.Algebra.finitePresentation_of_base_nilpotent` then lifts finite
presentation of `N`, using its assumed flatness over `A` and nilpotence of
`I`. Finally, `exists_presentation_tilde` presents the associated sheaf
of `N`, and the actual quasi-coherent comparison `M.fromTildeΓ` transports
that presentation to `M`. A finite global presentation implies local finite
presentation by the existing assembly lemma. The constructor uses classical
choice on this existence proof, retaining the proof of finiteness.

The rings and section modules need not be noetherian, `I` need not be
finitely generated, and `B` need not be flat over `A`. The universe of `A`
is independent of the scheme universe. This result retains the stronger
input of a global finite presentation of the reduced sheaf and flatness
of affine sections; it does not derive these from local finite presentation
or relative stalk flatness. It constructs a presentation of an existing
sheaf, rather than a new deformation, and supplies no coherent-family atlas.
