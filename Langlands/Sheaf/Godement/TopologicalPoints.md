# Godement degree zero from the points of a topological space

Author: Worker 61. Builds on the published Godement construction
`Langlands.Sheaf.Godement` and on the standard points
`Langlands.Cohomology.Flasque.spacePoints` of a topological space, which are
Mathlib's `Opens.pointGrothendieckTopology x`.

Let `X` be a topological space in `TopCat.{v}` and let `C` be a category with
morphisms in universe `v` and all colimits of size `v`. For `x : X`, write
`pt x` for the point `Opens.pointGrothendieckTopology x` of the site of open
subsets. Its fiber functor sends a presheaf `P` to a colimit of the sections
`P(U)` over the opens `U` containing `x`, indexed by the category of elements
of the point's fiber functor. Mathlib's ordinary stalk `P.stalk x` is the
colimit over `OpenNhds x`. The two index categories have the same objects and
morphisms up to the evident identification. Mathlib lists this comparison as a
TODO in `Mathlib/Topology/Sheaves/Points.lean`.

- `stalkToFiber x P` and `fiberToStalk x P` are the maps induced by the two
  colimit cocones. The first sends the germ of a section to its image
  `(pt x).toPresheafFiber U _ P` (`germ_stalkToFiber`). The second sends that
  image back to the germ (`toPresheafFiber_fiberToStalk`).
- `stalkFiberIso C x : Presheaf.stalkFunctor C x ≅ (pt x).presheafFiber` is the
  natural isomorphism with these components (`stalkFiberIso_hom_app`).

Assume in addition that `C` has all limits of size `v`.

- `sheafStalkFiberIso C x` restricts it to sheaves. It identifies the ordinary
  stalk functor on sheaves, `Sheaf.forget C X ⋙ Presheaf.stalkFunctor C x`, with
  the sheaf fiber functor `(pt x).sheafFiber`.
- `skyscraperIso C x` identifies Mathlib's ordinary skyscraper sheaf functor
  `skyscraperSheafFunctor x` with the point's skyscraper sheaf functor
  `(pt x).skyscraperSheafFunctor`. The ordinary skyscraper is right adjoint to
  the ordinary stalk (`stalkSkyscraperSheafAdjunction`), hence, after transport
  along `sheafStalkFiberIso`, right adjoint to `(pt x).sheafFiber`. The point's
  skyscraper is right adjoint to the same functor
  (`(pt x).skyscraperSheafAdjunction`). The isomorphism is Mathlib's
  `Adjunction.rightAdjointUniq` for these two adjunctions. Decidability of
  membership in opens, needed by the ordinary skyscraper, is classical.
- `pointFunctorIso C x` identifies the ordinary stalk-skyscraper endofunctor
  `(Sheaf.forget C X ⋙ Presheaf.stalkFunctor C x) ⋙ skyscraperSheafFunctor x` with
  the published Godement point functor
  `pointFunctor (Cohomology.Flasque.spacePoints X) C x`.
  `unit_pointFunctorIso_hom_app` proves that it carries the unit of the ordinary
  stalk-skyscraper adjunction to the unit of the point's adjunction.
- `topZeroFunctor C X` is the product over all `x : X` of the ordinary
  stalk-skyscraper endofunctors, and `topCoaugmentation C X` is the product of
  the ordinary units.
- `topZeroFunctorIso C X : topZeroFunctor C X ≅ zeroFunctor (Cohomology.Flasque.spacePoints X) C`
  is the product of the isomorphisms `pointFunctorIso C x`.
  `topCoaugmentation_topZeroFunctorIso` proves that it carries
  `topCoaugmentation C X` to the published Godement coaugmentation
  `coaugmentation (Cohomology.Flasque.spacePoints X) C`.

Consequently the published Godement degree-zero functor over all points of a
space is the classical one: the product over the points of the skyscraper
sheaves of the stalks, whose sections over `U` are arbitrary families
`(s_x)_{x ∈ U}` with `s_x ∈ F_x`. Its coaugmentation sends a section to its
germs. In SGA 4, Exposé XVII (Deligne), 4.2.1–4.2.2 (original page 326), a
family of points indexed by a set `X` is a morphism `k : Top(X) → S` from the
topos of the discrete space `X`. The Godement resolution starts with
`C⁰(F) = k_* k^* F` and the adjunction map `ε : F → C⁰(F)`, and continues with
`C^{n+1}(F) = C⁰(coker d^{n-1})`. For the space's own points, `k_* k^* F` is
the product over `x` of the direct images of the stalks `F_x` from the points,
that is, of the skyscraper sheaves. The isomorphisms here identify the published
point-based construction with this description. Flasqueness, exactness of the
terms and splitting on stalks (Proposition 4.2.3 there) are not asserted.

Provenance: the content is derived infrastructure comparing two Mathlib
presentations of stalks and skyscraper sheaves with the published Godement
construction. The proof route through adjoint uniqueness is this module's own.

Sources: `sga4-1973-tome3-deligne-xvii-original-scan` (SGA 4 Tome 3, Lecture
Notes in Mathematics 305, 1973, original scan, SHA-256
`702fa23766ccec841d31ce0f21dfaacff8d8d31d4153de386587a27a4c01107a`),
Exposé XVII, 4.2.1–4.2.2, original page 326 (expose page 75, PDF page 329).
Worker 61 read this page on the original scan. Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
