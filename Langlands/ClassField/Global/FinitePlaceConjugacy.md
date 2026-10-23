# Finite-place conjugacy

For number fields `F` and `E` in an arbitrary common universe, with an
`F`-algebra structure on `E`, fix a finite place `v` of `F`, a finite place
`w` of `E` above it, and `g : E ≃ₐ[F] E`. Put
`w' = finitePlaceEquiv g.toRingEquiv w`. This is the pullback convention:
the completion equivalence extends `g` from `E_w'` to `E_w`.

`finiteCompletionEquiv_algebraMap` proves that this completion equivalence
fixes `F_v`. Both maps are continuous, so equality on the dense image of
`F` proves equality on the completed base. Consequently,
`finiteCompletionAlgEquiv v w g : E_w' ≃ₐ[F_v] E_w` is the actual
completion equivalence equipped with this algebra compatibility.
Its value on an element of `E` is the completed image of `g` of that
element. `finiteCompletionCompatible` packages the commuting square with
the identity of `F_v` required by the existing `relativeConjugacy`.
The place `w'` lies over `v` by `liesOver_finitePlaceEquiv`.

The remaining declarations assume `Normal F E`. Write `d_w` for
`decompositionHom v w`, `e` for the constructed algebra equivalence, and
`C_e` for `galoisConjugacy` along it. The two decomposition comparison
lemmas prove

`d_w(C_e(σ)) = g * d_w'(σ) * g⁻¹`

and

`d_w'(C_e⁻¹(τ)) = g⁻¹ * d_w(τ) * g`.

The forward formula follows by applying the injective embedding of `E`
in `E_w`, using the defining decomposition identity and the value of
`e` on `E`. The inverse formula follows by substituting `C_e⁻¹(τ)`
and cancelling the conjugating elements.

Let `loc_w` denote the actual map from ordinary idele cohomology to
relative cohomology of `E_w/F_v`, and let `T_e` denote the homomorphism
of the actual `relativeConjugacy` isomorphism. In every natural degree,
`innerConjugationMap_comp_ideleLocalMap` proves the square

`loc_w ∘ innerConjugationMap(g⁻¹) = T_e ∘ loc_w'`.

The proof applies ordinary group-cohomology functoriality.
The inverse decomposition formula identifies the group homomorphisms.
The coordinate formula for the actual idele action identifies the
coefficient maps: the `w`-coordinate of `g` acting on an idele is `e`
applied to its `w'`-coordinate. The inverse coefficient action in
`innerConjugationMap(g⁻¹)` is precisely the action of `g`.

`ideleLocalMap_finiteCompletionConjugacy` specializes this square to
degree two and applies `innerConjugationMap_two`, giving
`T_e ∘ loc_w' = loc_w`. The `_apply` form evaluates this equality on
any actual idele-cohomology class.

This is an internal derivation from the existing completion and
decomposition maps, the actual idele coordinate action, ordinary
cohomology functoriality, and the explicit boundary proof in
`OrdinaryInnerConjugation`. No external source theorem is asserted.
The unit proves the transport identity for conjugate finite places.
It neither assumes nor proves naturality of a supplied local invariant
family. Invariant-value independence, archimedean choice independence,
and `GlobalInvariantStatement` require further results.
