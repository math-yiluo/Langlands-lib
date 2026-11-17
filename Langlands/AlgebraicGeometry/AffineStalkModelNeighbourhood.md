# Affine neighbourhoods from affine stalk models

This internal construction completes the geometric reduction of
Bosch–Lütkebohmert–Raynaud, *Néron Models*, §6.4 Lemma 4, once an affine
stalk model is supplied. It does not assert that the normal
codimension-one hypotheses already produce such a model.

For an integral scheme `X` over `Spec R` and a set `E` of points,
`AffineStalkModel p E` consists of a commutative domain `A` with its
`R`-algebra structure, an `R`-morphism `Spec A ⟶ X`, a dominant map
`Spec X.functionField ⟶ Spec A` whose composite is the canonical generic
map into `X`, and compatible maps
`Spec (X.presheaf.stalk x) ⟶ Spec A` for all `x ∈ E`. The latter maps are
over `Spec R` and restrict to the specified generic map. The affine model
need not be of finite type or noetherian.

For separated integral `X` locally of finite presentation over `Spec R`
and finite `E`, `affineNeighbourhoodOfAffineStalkModel` returns an actual
affine open of `X` containing `E`. It works in every universe and allows
empty `E`.

The constructor factors the affine-model morphism through a finitely
generated `R`-subalgebra `T` of `A`. This gives a locally finite type
affine stage `Spec T`, with a map to `X`. The map `Spec A ⟶ Spec T` is
dominant because the subalgebra inclusion is injective. The given generic
map and the stalk maps therefore descend to a dominant generic inverse
and compatible local extensions at `E`. The support constructor
`affineNeighbourhoodOfGenericRetraction` then supplies the affine open.

The supporting theorem `isDominant_specMap_of_injective` proves dominance
of an affine morphism induced by an injective ring homomorphism using the
kernel criterion for density of the spectrum map.
