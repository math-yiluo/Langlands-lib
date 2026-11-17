# Recovering a sheaf from an effective local scheme descent

`LocalRepresenter.representableByDescent` constructs a representation of an
étale sheaf from a supplied invariant cartesian scheme descent of its local
representing chart. It keeps independent scheme universe `u` and presheaf
value universe `v`. Geometric effectivity is a separate obligation.

The inputs are schemes `S,U`, a surjective étale map `p : U ⟶ S`, a presheaf
`F : (Over S)ᵒᵖ ⥤ Type v` satisfying the sheaf condition for the full big
étale slice topology, and a local representing equivalence
`e : ((Over.map p).op ⋙ F).RepresentableBy M`.
Write `W` for `M` viewed over `S`, and `R` for its local relation constructed
in `LocalRepresenterOverlap` and `LocalRepresenterRelation`.
The remaining inputs are `N : Over S`, a scheme map `q : M.left ⟶ N.left`,
a cartesian square `IsPullback q M.hom N.hom p`, and invariance
`first p ≫ q = second p e ≫ q`. The output is the actual datum
`F.RepresentableBy N`. No affineness, line bundle, smoothness or properness
is needed for this comparison.

The implementation uses the following internal constructions.

- `cartesian` identifies the relation's second covering-base coordinate with
  the second projection of its defining pullback.
- `liftedChartMap` is the natural map associated with the chart's universal
  family. Its source is the lifted Yoneda presheaf of `W`, and its target is
  `F ⋙ uliftFunctor.{u+1}`. For surjective étale `p` it is locally surjective:
  base change of a test scheme supplies a single covering morphism, and the
  local representing bijection supplies the lifted section.
- `liftedYonedaMap_locallySurjective` proves the corresponding assertion for
  any surjective étale map in the slice, by pulling back its covering sieve.
- `same_kernel` proves that chart maps `a,b : T ⟶ W` classify the same
  family exactly when `a ≫ qOver = b ≫ qOver`. In the forward direction the
  matching-pair lift to `R` and invariance give the equality. Conversely,
  the cartesian relation square lifts `a` together with the covering-base
  coordinate of `b`. Invariance gives equality of its second chart
  projection and `b` after composition with `q`; their covering-base
  coordinates also agree. The supplied cartesian square for `q` then
  identifies these chart maps, and `kernel_w` identifies their families.
- `liftedYoneda_isSheaf` restricts the represented fppf sheaf to the étale
  topology, using subcanonicity of the fppf slice topology.

For the final construction the square for `q` implies that `q` is a
surjective étale base change of `p`. Both the sheaf `F` and the represented
sheaf of `N` therefore have locally surjective maps from the represented
sheaf of `W`, with the same sectionwise kernel. The Library theorem
`Langlands.CategoryTheory.Sites.exists_iso_of_isLocallySurjective_of_same_kernel`
constructs their compatible isomorphism in the sheaf category, using
effective epimorphisms. The implementation chooses this isomorphism,
forgets to presheaves, and inverts it to obtain a representation of the
lifted `F` by `N`. `Functor.representableByUliftFunctorEquiv` removes the
temporary lift.

All three sheaves in this argument take values in `Type (max (u+1) v)`,
large enough for sheafification of the slice category. This intermediate
choice imposes no equality or bound on the original `u,v`; the final
representation has values in the original `Type v`.

The provenance is internal categorical reasoning from the local representing
bijection, scheme pullbacks, and the cited Library common-kernel theorem.
This construction assumes a descended invariant scheme; it supplies neither
its existence nor the geometric conclusions of polarized descent.
