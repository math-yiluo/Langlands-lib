# The underlying complex of the equivariant Godement complex

Author: Worker 61. Combines the published equivariant Godement construction
(`Langlands.Sheaf.Equivariant.Godement.{Zero,SkyscraperProduct,Complex}`), the
exactness of forgetting equivariance (`Langlands.Sheaf.Equivariant.Exact`), the
transport of the cokernel construction along a right exact functor
(`Langlands.Cohomology.CokernelComplex.Map`) and the identification of the
point-based Godement degree-zero functor of a topological space
(`Langlands.Sheaf.Godement.TopologicalPoints`).

Let `R` be a commutative ring, and let a group `G` act on a topological space
`X` by continuous individual operators, all in one universe `u`. Write
`toSheaf` for the functor `toSheaf G X (ModuleCat.{u} R)` that forgets
equivariance, and `pts` for `Cohomology.Flasque.spacePoints (TopCat.of X)`, the
standard points `x ↦ Opens.pointGrothendieckTopology x` of `X`.

Degree zero.

- `skyscraperMap_read` and `zeroMap_familyEvaluation` are the two naturality
  facts used below. Reading a skyscraper section commutes with the skyscraper
  map of a morphism. Evaluating a stalk family at a point commutes with the
  induced stalk maps.
- `skyscraperProjection_naturality`: the published projection from the
  underlying sheaf of `zeroSheaf F` to the ordinary skyscraper sheaf at `x`,
  with value the stalk of `F` at `x`, is natural in the equivariant sheaf `F`.
- `coaugmentation_skyscraperProjection`: applying `toSheaf` to the equivariant
  coaugmentation of `F` and then projecting to the skyscraper at `x` gives the
  unit of Mathlib's stalk–skyscraper adjunction `stalkSkyscraperSheafAdjunction x`
  at the underlying sheaf. Both send a section over an open containing `x` to
  its germ at `x`.
- `topFactors R X x` is the ordinary stalk-skyscraper endofunctor at `x`.
  `topZeroFunctor_hom_ext` says that maps into a value of the product of these
  functors are determined by their components.
- `zeroIsoTopApp R G X F` composes the published `skyscraperProductIso` with
  Mathlib's evaluation of a product of functors (`piObjIso`).
  `zeroIsoTopApp_hom_π` shows that its components are the skyscraper
  projections.
- `zeroIsoTop R G X : zeroFunctor R G X ⋙ toSheaf ≅ toSheaf ⋙ topZeroFunctor (ModuleCat.{u} R) (TopCat.of X)`
  is the resulting natural isomorphism. `zeroIso_comm_aux` shows that it
  carries the coaugmentation to the product of the ordinary units.
- `zeroIso R G X : zeroFunctor R G X ⋙ toSheaf ≅ toSheaf ⋙ Sheaf.Godement.zeroFunctor pts (ModuleCat.{u} R)`
  follows `zeroIsoTop` with the published `topZeroFunctorIso`.
  `zeroIso_comm` shows that it carries the equivariant coaugmentation to the
  published Godement coaugmentation:
  `toSheaf.map (coaugmentation.app F) ≫ (zeroIso R G X).hom.app F = (Sheaf.Godement.coaugmentation pts _).app (toSheaf.obj F)`.

All degrees.

- `underlyingComplexIso R G X` is the natural isomorphism of functors to
  nonnegative cochain complexes of ordinary module sheaves
  `complexFunctor R G X ⋙ toSheaf.mapHomologicalComplex (ComplexShape.up ℕ) ≅ toSheaf ⋙ Sheaf.Godement.complexFunctor pts (ModuleCat.{u} R)`.
  It is `CokernelComplex.functorIso` applied to `zeroIso` and `zeroIso_comm`.
  This needs `toSheaf` to preserve zero morphisms and cokernels, which the
  instances of `Langlands.Sheaf.Equivariant.Exact` supply. In degree `n` its
  component is built inductively from `zeroIso` and the cokernel comparisons of
  `toSheaf`.
- `underlyingComplexIso_augmentation`: in degree zero the isomorphism carries
  `toSheaf` of the equivariant coaugmentation to the ordinary augmentation
  `Sheaf.Godement.augmentation pts (ModuleCat.{u} R) (toSheaf.obj F)`.

So, after forgetting the group action, the equivariant Godement complex of `F`
is the classical Godement complex of the underlying sheaf, with matching
augmentations. This is the comparison used when equivariant Godement complexes
compute ordinary cohomology after forgetting the action. In Berkovich,
*Etale equivariant sheaves on p-adic analytic spaces* (unfinished 1995–1996
manuscript), section 1.5, printed page 10, the Godement complex is defined by
`C⁰(F)` with its adjunction morphism and `C^{m+1}(F) = C⁰(Coker d^{m-1})`. SGA 4,
Exposé XVII, 4.2.1–4.2.2 (original page 326) gives the same recipe for a family
of points of a topos, with `C⁰(F) = k_* k^* F`. The construction here is the
ordinary-topological transport-site version, not Berkovich's analytic
equivariant étale site. No flasqueness, exactness or acyclicity of either
complex is asserted.

Provenance: derived. The statement matches the form of the
"underlying comparison" proposed in Worker 3's (rejected, unpublished)
statement candidate 90b58de0. That candidate was rejected for source
documentation, not for its Lean content, and is not imported here. The proof
route is this module's own.

Sources: registered folder
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`
(digest `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`;
member PDF SHA-256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`), section
1.5, printed page 10; and `sga4-1973-tome3-deligne-xvii-original-scan`
(SHA-256 `702fa23766ccec841d31ce0f21dfaacff8d8d31d4153de386587a27a4c01107a`),
Exposé XVII, 4.2.1–4.2.2, original page 326. Worker 61 read both passages.
Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
