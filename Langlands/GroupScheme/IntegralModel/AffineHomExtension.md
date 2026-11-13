# Affine extension from containment of generic coordinates

The theorem `Langlands.GroupScheme.IntegralModel.nonempty_hom_of_genericCoordinates`
is an internal supporting result for `SmoothHomExtensionStatement`. Let `R` be a
domain, `K` a fraction field, `M` and `N` the supplied integral models of `G` and
`H`, and `f : G ⟶ H` a homomorphism. If, for every actual global section `b` on
`N`, the pullback of `N.genericCoordinate b` along `f` belongs to the range of
`M.genericCoordinate`, then `Nonempty (M.Hom N f)`.

The theorem uses the affine and flat hypotheses already carried by each
`IntegralModel`. It requires no discrete valuation, Henselian, residue-field, or
smoothness hypotheses. The finite-type structure carried by the models is not
used in the argument. This is a derived helper: it implements the coordinate-ring
construction needed in the proof of Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach* (2023), Remark 2.10.3, together with generic reflection of the group law
as described in Remark 2.10.19. It is not a proof of the integral-point criterion
on its own; the coordinate-containment premise remains explicit.

The implementation first proves that an algebra homomorphism between the global
coordinate rings of affine schemes over `Spec R` is the pullback of an actual
morphism over `Spec R`. It constructs the morphism using the canonical
isomorphisms with spectra of global sections. Naturality of these isomorphisms
and full faithfulness of `Spec` establish the prescribed global-section map;
compatibility with the structure morphisms follows from the algebra-map law.

For the given models, the generic group is regarded as a scheme over `Spec R`
by composing its structure morphism with `Spec K ⟶ Spec R`. Its actual restriction
to the model is the inverse specified generic identification followed by the
first pullback projection. Global-section pullback along these morphisms gives
algebra homomorphisms over `R`. The coordinate-containment premise chooses a
preimage in the coordinate ring of `M` for every pulled-back coordinate of `N`.
The published injectivity theorem `IntegralModel.genericCoordinate_injective`
then proves that these preimages preserve zero, one, addition, multiplication,
and scalars. Thus they form an `R`-algebra homomorphism.

The affine construction gives a scheme morphism from `M` to `N`. Equality of
its coordinate pullback with the chosen algebra map identifies its composite
with the actual generic restriction. The universal property of the generic
pullback then proves that the base-changed scheme morphism is
`M.genericIso.hom ≫ f ≫ N.genericIso.inv` on underlying schemes.

Finally, `Langlands.AbelianScheme.isMonHom_of_map` reflects preservation of the
unit and multiplication through generic base change. Its injectivity premises
are supplied by `genericFibre_map_injective`: the unit scheme and the square of
`M` are flat over the domain, and `N` is separated because it is affine. The
reflected monoid morphism gives a group-scheme homomorphism by `Grp.homMk`.
Cancelling the specified generic isomorphisms yields the exact compatibility
square required by `M.Hom N f`.
