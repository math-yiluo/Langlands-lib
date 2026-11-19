# Pullback reflects stalk isomorphisms between finite free stalks

This internal module shows that ordinary pullback of module sheaves along an
arbitrary scheme morphism detects the stalk-isomorphism locus, once the stalks
involved are finite free. No flatness of the morphism is assumed. All schemes
lie in one universe `u`.

## Results

- `bijective_of_bijective_baseChange`: let `A → B` be a ring homomorphism that
  is local (`IsLocalHom (algebraMap A B)`), with `B` nontrivial. Let
  `φ : M →ₗ[A] N` be a linear map between finite free `A`-modules. If the base
  change `B ⊗ φ` is bijective, then `φ` is bijective.

  *Proof.* `A` is nontrivial because `B` is. The base change is an
  isomorphism, so the two finite ranks over `B` agree. Base change preserves
  finite rank (`Module.finrank_baseChange`), so the ranks over `A` agree, and
  there is a linear equivalence `e : N ≃ M`. The endomorphism `ψ = e ∘ φ` has
  bijective base change. Hence `ψ ⊗ B` is a unit and its determinant is a unit
  (`LinearMap.isUnit_iff_isUnit_det`). That determinant is the image of
  `det ψ` (`LinearMap.det_baseChange`). A local homomorphism reflects units,
  so `det ψ` is a unit and `ψ` is bijective. Finally `φ = e⁻¹ ∘ ψ`.
- `isIso_of_isIso_extendScalars_map`: the same statement for a local
  homomorphism `g : A ⟶ B` of commutative rings and a morphism `l` of finite
  free `A`-modules. If `(ModuleCat.extendScalars g).map l` is an isomorphism,
  then so is `l`. Mathlib's extension of scalars acts on morphisms by
  `LinearMap.baseChange`, for the algebra structure given by `g`.
- `mem_isoLocus_pullback_iff_of_free`: for `f : X ⟶ Y`, a morphism
  `φ : M ⟶ N` of module sheaves on `Y` and a point `x : X`, assume the stalks of
  `M` and `N` at `f x` are finite free over the local ring. Then `x` lies in the
  published `isoLocus` (bijective stalk map) of the pullback of `φ` exactly when
  `f x` lies in the iso locus of `φ`.

  The published `StalkPullback.pullbackStalkIso` identifies the stalk of the
  pullback at `x` with extension of scalars of the stalk at `f x` along the
  local stalk homomorphism `f.stalkMap x`. One direction is functoriality; the
  other is the previous result.
- `free_stalk_of_hasFiniteLocalBasis`: a module sheaf with finite local bases
  (`HasFiniteLocalBasis`) has finite free stalks. Its stalks are finitely
  presented (published `isFinitePresentation_of_hasFiniteLocalBasis` and
  `finitePresentation_stalk`) and flat (published
  `flat_stalk_of_hasFiniteLocalBasis`). Over a local ring this makes them free
  (`Module.free_of_flat_of_isLocalRing`).
- `mem_isoLocus_pullback_iff_of_hasFiniteLocalBasis`: the pullback criterion
  for morphisms between module sheaves with finite local bases.

## Provenance

Internal. These are standard facts: a square matrix over a ring is invertible
iff its determinant is a unit, and local homomorphisms reflect units. They are
assembled from Mathlib and the published Library modules `StalkIsoLocus`,
`StalkPullback`, `FiniteLocalBasisDescent` and `RankOneStalkReflection`.
