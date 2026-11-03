# Base change along an isomorphism of fields

Module `Langlands.GroupScheme.Absolute.AlgebraicClosureBaseChange`. It is derived
infrastructure for `Langlands.GroupScheme.ParabolicIntersectionGeometryStatement` (task
`7c372114-27b9-49eb-8f69-5b1df15fbbca`).

The proof of that statement works over `k̄ = AlgebraicClosure k`. It needs `G_{k̄}` to be
connected reductive and the base changes of the two parabolics to be parabolic. The Library
definitions of these properties (`IsConnectedReductive`, `IsParabolicSubgroup`) refer to a
further base change, from `k̄` to `AlgebraicClosure k̄`. Since `k̄` is algebraically closed,
`algebraMap k̄ (AlgebraicClosure k̄)` is bijective. This module shows that base change along
`Spec` of a bijective field map preserves every property involved. So the proof does not need
the general field-extension statements for connected reductive groups and parabolics.

## Retraction (section `Retraction`)

Let `e : S' ⟶ S` and `c : S ⟶ S'` be scheme morphisms with `h : c ≫ e = 𝟙 S`.

- `precompHom a G` and `precompEquiv a G`: precomposition with a morphism (resp.
  isomorphism) `a` of test objects in `Over S`, as a group homomorphism (resp. group
  isomorphism) of point groups of `G`.
- `overMapRetractionIso h T : (Over.map e).obj ((Over.map c).obj T) ≅ T`, the identity on
  underlying schemes. The structure maps agree because `c ≫ e = 𝟙`. The simp lemmas
  `overMapRetractionIso_hom_left` and `overMapRetractionIso_inv_left` say both components are
  identities.
- `retractionPointsEquiv h G T`: the group isomorphism between the `T`-points of
  `(bc c).obj ((bc e).obj G)` and the `T`-points of `G`. It composes
  `baseChangePointsEquiv c`, `baseChangePointsEquiv e`, and precomposition with
  `overMapRetractionIso`. `retractionPointsEquiv_naturality` shows it is natural in `T`.
- `baseChangeRetractionIso h G : (bc c).obj ((bc e).obj G) ≅ G`. It is built with the Library
  constructor `isoOfPoints` from the natural point isomorphisms.
  `comp_baseChangeRetractionIso_hom` and `comp_baseChangeRetractionIso_inv` compute it on
  points.
- `baseChangeRetractionIso_hom_naturality h f`: for `f : G ⟶ H`,
  `(bc c).map ((bc e).map f) ≫ η_H.hom = η_G.hom ≫ f`, where `η` is the retraction
  isomorphism. The proof checks equality on points (`hom_ext_points`) and unfolds
  `baseChangePointsEquiv_comp`.
- `range_eq_bot_of_range_baseChange_eq_bot h f hf`: if the range of `(bc e).map f` is `⊥`,
  then so is the range of `f`. Base change along `c` keeps the range `⊥`
  (`range_baseChangeHom`, `bot_baseChange`). By naturality, `f` is
  `η_H.inv ≫ (bc c).map ((bc e).map f) ≫ η_G.hom`, so every point of the range of `f` is `1`.
- `isIso_of_isIso_baseChange h f hf`: if `(bc e).map f` is an isomorphism, so is `f`. Same
  factorization of `f`.

## Isomorphic bases

- `connectedSpace_baseChange_of_isIso b G`: if `b` is an isomorphism and `G.X.left` is
  connected, then so is the underlying space of `(bc b).obj G`. The first projection of the
  pullback along an isomorphism is an isomorphism, hence a homeomorphism.

## Bijective field maps (section `Field`)

Let `φ : K →+* K'` be a bijective map of fields, `e = Spec.map (ofHom φ)` and
`c = Spec.map (ofHom σ⁻¹)` with `σ = RingEquiv.ofBijective φ hφ`.

- `scalarMap_overMap_specMap φ T a`: moving a test scheme `T` over `Spec K'` to `Spec K` along
  `e` composes its scalar map with `φ`.
- `specMap_symm_comp_specMap φ hφ : c ≫ e = 𝟙` and `specMap_comp_specMap_symm φ hφ :
  e ≫ c = 𝟙`.
- `IsUnipotent.baseChange_of_bijective φ hφ hH`: base change along `e` preserves `IsUnipotent`.
  Given a representation `ρ` of `(bc e).obj H` on `K'ⁿ`, form the representation
  `ρ₀ = η_H.inv ≫ (bc c).map ρ ≫ (GeneralLinear.baseChangeIso n c).hom` of `H` on `Kⁿ`.
  Unipotence of `H` gives a nonzero fixed vector `v` of `ρ₀`. Then `φ ∘ v` is nonzero
  (`φ` is injective) and fixed by `ρ`. For a test scheme `T` over `Spec K'` and a point `g`,
  the matrix of `ρ₀` at the corresponding point `g₀` of `H` over `(Over.map e).obj T` equals
  the matrix of `ρ` at `g` (key step, by the point formulas of `η_H` and of
  `GeneralLinear.baseChangeIso`, and `pointMatrix_naturality`). The scalar maps match by
  `scalarMap_overMap_specMap`.
- `HasTrivialUnipotentRadical.baseChange_of_bijective φ hφ hG`: base change along `e`
  preserves `HasTrivialUnipotentRadical`. Let `i : H ⟶ (bc e).obj G` be closed, smooth,
  connected, unipotent and with normal range. Its base change `(bc c).map i` into
  `(bc c).obj ((bc e).obj G) ≅ G` has the same five properties: closedness by
  `IsClosedSubgroup.baseChange`, smoothness by stability under pullback, connectedness by
  `connectedSpace_baseChange_of_isIso` (`c` is an isomorphism), unipotence by the previous
  theorem applied to `σ⁻¹`, and normality by `range_baseChangeHom` and `IsNormal.baseChange`.
  By `HasTrivialUnipotentRadical.of_iso` and `hG`, its range is `⊥`. Then
  `range_eq_bot_of_range_baseChange_eq_bot` (with `e ≫ c = 𝟙`) gives `range i = ⊥`.
- `IsBorelSubgroup.baseChange_of_bijective φ hφ hj`: base change along `e` preserves
  `IsBorelSubgroup`. Closedness, smoothness and connectedness are as above. Solvability is
  `IsSolvableGroupScheme.baseChange_of_bijective` (Worker 1240's module
  `Absolute.SolvableBijectiveBaseChange`). For maximality, let `f ≫ i' = (bc e).map j` with
  `i' : B' ⟶ (bc e).obj G` closed, smooth, connected and solvable. Then `j ≫ η_G.inv` is
  Borel (`IsBorelSubgroup.comp_iso`), and it factors through `(bc c).map i'` by
  `η_B.inv ≫ (bc c).map f`, using `baseChangeRetractionIso_hom_naturality`. The base change
  `(bc c).obj B'` is closed, smooth, connected and solvable as before. Maximality of
  `j ≫ η_G.inv` makes `η_B.inv ≫ (bc c).map f` an isomorphism, hence `(bc c).map f`. Then
  `isIso_of_isIso_baseChange` (with `e ≫ c = 𝟙`) makes `f` an isomorphism.

## Algebraic closures (section `AlgebraicClosure`)

- `bijective_algebraMap_algebraicClosure_algebraicClosure`: `algebraMap k̄
  (AlgebraicClosure k̄)` is bijective (Mathlib's `IsAlgClosed.algebraMap_bijective_of_isIntegral`).
- `IsConnectedReductive.baseChange_toAlgebraicClosure hG`: if `G` is connected reductive over
  `k`, then `(bc (toAlgebraicClosure k)).obj G` is connected reductive over `k̄`. Smoothness
  and affineness are stable under pullback. Connectedness is the Library theorem
  `IsConnectedReductive.connectedSpace_toAlgebraicClosure`. The trivial geometric unipotent
  radical is `HasTrivialUnipotentRadical.baseChange_of_bijective` applied to the field
  `hasTrivialGeometricUnipotentRadical` of `hG` and the bijection `k̄ → AlgebraicClosure k̄`.
- `IsParabolicSubgroup.baseChange_toAlgebraicClosure hj`: if `j : P ⟶ G` is parabolic over
  `k`, then `(bc (toAlgebraicClosure k)).map j` is parabolic over `k̄`. Closedness and
  smoothness are stable under base change. If `j₀ : B ⟶ G_{k̄}` is the Borel subgroup of `hj`
  with `f₀ ≫ j_{k̄} = j₀`, then the base change of `j₀` to `AlgebraicClosure k̄` is Borel by
  `IsBorelSubgroup.baseChange_of_bijective`, and the base change of `f₀` gives the
  factorization.

## Provenance

This module is derived, not a statement from a source. It transports Library definitions
along an isomorphism of base fields and uses no literature result. The external ingredients
are Mathlib's `IsAlgClosed.algebraMap_bijective_of_isIntegral` and the Library's point-wise
constructions `isoOfPoints`, `baseChangePointsEquiv` and `GeneralLinear.baseChangeIso`.

The general-base `precompEquiv` name abbreviates the existing
`CocharacterSplitting.precompEquiv`, with the group argument made explicit.
It retains the same precomposition maps.
