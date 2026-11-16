# Properness and smoothness of scheme coproduct morphisms

This internal geometry unit supplies the finite coproduct step used to assemble
smooth proper local parameter schemes for actual parabolic families. It is a
consequence of the imported scheme coproduct and morphism-property APIs; it does
not assume or prove parabolic representability.

Let `I : Type v` be small relative to universe `u`, let `X i` be schemes in
universe `u`, and let `f i : X i ⟶ Y` be morphisms to one scheme. The module proves:

- `universallyClosed_sigmaDesc`: if `I` is finite and every `f i` is universally
  closed, then the induced morphism `Sigma.desc f` from the scheme coproduct is
  universally closed.
- `isProper_sigmaDesc`: if `I` is finite and every `f i` is proper, then
  `Sigma.desc f` is proper.
- `smooth_sigmaDesc`: if every `f i` is smooth, then `Sigma.desc f` is smooth.
  This last assertion needs only the stated smallness, with no finiteness premise.

These results include the empty indexing type and impose no affine, Noetherian,
reductive-group, or nonemptiness hypotheses.

The definition `smoothProperCoproduct` applies these results to construct an
element of `{V : Over Y // Smooth V.hom ∧ IsProper V.hom}` from a finite family
of smooth proper morphisms. Its underlying object is `Over.mk (Sigma.desc f)`,
so its source is the actual scheme coproduct of the `X i`. The theorem
`smoothProperCoproduct_hom` records the structure morphism by definitional
equality. This construction retains both geometric properties with the scheme
over `Y`; it does not assert a moduli property.

The preliminary `isClosedMap_of_finite_openCover` treats an arbitrary morphism
`f : X ⟶ Y` and a finite open cover of its source. If all composites from cover
components to `Y` are closed maps, so is `f`. For a closed subset `Z` of `X`,
covering expresses its image as the union, over the cover indices, of the images
of the inverse images of `Z` on the components. The inverse images are closed by
continuity; the component hypotheses and the finite closed-union theorem show
that the union is closed.

For universal closedness, the implemented proof starts with an arbitrary
pullback square for `Sigma.desc f` and pulls back the coproduct component open
cover to the new source. Pasting the component pullback squares with the supplied
square identifies each cover composite as a base change of the corresponding
`f i`. Stability of universal closedness under base change makes that composite
closed. The preceding finite-cover criterion proves closedness of the arbitrary
base change, as required.

Properness combines this universal closedness result with local finite type,
which is Zariski local on the source, and the published theorem
`AlgebraicGeometry.isSeparated_sigmaDesc_of_forall_isSeparated`. The latter is
imported from the existing Anthropic FLT port; this module adds no new proof of
coproduct separatedness. Finally, smoothness follows directly from the published
Zariski source-locality API for smooth morphisms.
