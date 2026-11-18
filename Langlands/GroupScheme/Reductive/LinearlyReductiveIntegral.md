# Linear reductivity and local right integrals

This module is internal supporting work for the proof of
`LinearlyReductiveFieldExtensionStatement` (in
[`LinearlyReductiveFieldExtensionProof`](LinearlyReductiveFieldExtensionProof.md)). It contains
no source-cited definition. Its main result, `linearlyReductive_iff_hasLocalRightIntegrals`,
characterizes linear reductivity by a condition on the coordinate bialgebra. The condition is
local: it asks for one normalized integral for each finite set of coordinates. Only finite-dimensional
representations appear.

Background. A group is linearly reductive exactly when its coordinate algebra has a normalized
invariant integral (Reynolds operator). The local version used here, and the proof below, are
internal to this module.

Throughout, `k` is a field, `H` is a group scheme over `Spec k`, and
`ψ : Spec B ≅ H.X` is any affine presentation of `H` over `k`. Write `e` for the published
corepresentation `corepresentableBy H ψ` of the affine point functor of `H` by `B`. `B` carries
the published bialgebra structure `bialgebra e`, with comultiplication `comul e`. For a
functional `r : B → k`, `leftAct r y = ∑ r(y₁) y₂` when `comul e y = ∑ y₁ ⊗ y₂` (published in
`AffineLinearEmbedding.Comodule`). `contract r : B ⊗ B → B` is `x ⊗ y ↦ r(x) y`, so
`leftAct r y = contract r (comul e y)` (`leftAct_eq_contract`, by definition).

## The main definition and theorem

- `HasLocalRightIntegrals ψ` (a `Prop`): for every finite set `T ⊆ B` there is a functional
  `r : B → k` with `r 1 = 1` and `leftAct r y = r(y) • 1` for every `y ∈ T`. This is the
  condition that `r` is a normalized right integral at each element of `T`.
- `simpleStable ρ`, for `ρ : MatrixRepresentation H n`, is the set of stable subspaces `W ≠ ⊥`
  whose only stable subspaces `U ≤ W` are `⊥` and `W`. For `n = Fin N` this is literally the set
  inside `sSup` in `LinearlyReductiveFieldExtensionStatement`.
- `linearlyReductive_iff_hasLocalRightIntegrals ψ`:
  `(∀ N (ρ : MatrixRepresentation H (Fin N)), sSup (simpleStable ρ) = ⊤) ↔
  HasLocalRightIntegrals ψ`.

## Stable subspaces form a complete sublattice

`coefficientMap ρ A x ℓ` is the linear map `v ↦ (ℓ((ρ(x) v)ᵢ))ᵢ` on `kⁿ`. By definition, `W` is
stable iff it is mapped into itself by every such map (`isStableSubspace_iff_le`). Hence stable
subspaces are closed under arbitrary `sSup` and under `⊓`, and `⊥` and `⊤` are stable.

- `exists_simpleStable_le`: every nonzero stable subspace contains a member of `simpleStable ρ`
  (strong induction on the dimension).
- `sSup_simpleStable_eq_top`: if every stable subspace has a stable complement, the simple
  stable subspaces span. The complement `C` of their sum `S` is stable. If `C ≠ ⊥`, it contains
  a simple stable subspace, which also lies in `S`, contradicting `S ⊓ C = ⊥`.
- `exists_isCompl_of_sSup_simpleStable`: conversely, if the simple stable subspaces span, every
  stable `W` has a stable complement. Take a stable `C` maximal with `W ⊓ C = ⊥` (`kⁿ` is
  Noetherian). For each simple stable `S`, `(W ⊔ C) ⊓ S` is a stable subspace of `S`, so it is
  `⊥` or `S`. If it were `⊥`, `C ⊔ S` would contradict maximality unless `S ≤ C`. So every `S`
  lies in `W ⊔ C`, and `W ⊔ C = ⊤`.

So `sSup (simpleStable ρ) = ⊤` for all `ρ` is equivalent to: every stable subspace of every
`ρ` has a stable complement.

## The universal matrix

`univMatrix ψ ρ = P ∈ GL_n(B)` is the matrix of `ρ` at the universal point `ψ.hom`.

- `affineMatrix_pt`, `affineMatrix_eq_map`: the matrix of `ρ` at any point `x` over `A` is the
  image of `P` under the algebra map `B → A` classifying `x`.
- `isStableSubspace_iff_univ`: `W` is stable iff for all `v ∈ W` and all functionals
  `ℓ : B → k`, the vector `(ℓ((P v)ᵢ))ᵢ` lies in `W`. One direction is the case `x = ψ.hom`; the
  other composes `ℓ` with the classifying map.
- `univMatrix_comul`: `comul(P) = P₁ P₂`, where `P₁` and `P₂` are the images of `P` under
  `b ↦ b ⊗ 1` and `b ↦ 1 ⊗ b`. This is multiplicativity of `ρ` at the two universal points
  over `B ⊗ B` (published `pt_comul`).

## Local integrals give stable complements

- `contract_matrix`: for `U, Y, V` over `B`, applying `contract r` entrywise to
  `U₂ Y₁ V₂` gives `U · r(Y) · V`, where `r(Y)` is `Y` with `r` applied to its entries and
  viewed in `B`. This uses that `contract r` is `B`-linear for the right factor.
- `avgConj ψ ρ Q = P⁻¹ Q P` for a constant matrix `Q`.
- `conj_average`: if `r` is a right integral at every entry of `X = P⁻¹ Q P`, then
  `P⁻¹ r(X) P = r(X)`. Indeed `comul(X) = (P⁻¹)₂ X₁ P₂` by `univMatrix_comul`, so
  `P⁻¹ r(X) P` is `contract r (comul X)`, entrywise. By the integral property, this is
  `r(X)`.
- `intertwines_of_commute_univ`: a constant matrix commuting with `P` commutes with every
  matrix of `ρ`, so it intertwines `ρ` with itself (published `Intertwines`). Hence its kernel is
  stable (published `IsStableSubspace.comap`).
- `exists_isCompl_of_hasLocalRightIntegrals`: local right integrals give every stable `W` a
  stable complement. Choose any linear complement and the projection `q` onto `W`, with matrix
  `Q`. Take `r` from `HasLocalRightIntegrals ψ` for the finite set of entries of `X = P⁻¹ Q P`,
  and put `π = r(X) ∈ M_n(k)`.
  - `π` commutes with `P` (`conj_average`), so `ker π` is stable.
  - `π w = w` for `w ∈ W`. The vector `y = P w` has all its functional images in `W`
    (stability), so `Q y = y` (`mulVec_eq_self_of_forall_dual`). Then `X w = P⁻¹ P w = w`, and
    `π w = r(X w) = w` since `r 1 = 1` (`map_dual_mulVec`).
  - `π v ∈ W` for every `v`. `P⁻¹` maps `W` into vectors with functional images in `W`
    (stability at the point `ψ.hom⁻¹`), and the columns of `Q` lie in `W`
    (`forall_dual_mulVec_mem`).
  - So `π` is a projection onto `W`, and `ker π` is a stable complement
    (`LinearMap.isCompl_of_proj`).

## Stable complements give local integrals

The `Model` section copies general lemmas of `IntegralModel.IntegralDiagonalRepresentation`
(`yonedaGrp_preimage_hom_hom`, `modelIso_hom_hom_hom`, `modelIso_inv_hom_hom`, `affinePointsEquiv_comp_inv`, `modelRep`,
`modelRep_affineMatrix_apply`, under names ending in `_eq` or `coeffRep`), so that this module does
not import that file. For a matrix `M` over `B` with `comul(Mᵢⱼ) = ∑ₗ Mᵢₗ ⊗ Mₗⱼ` and
`counit(M) = 1`, `coeffRep H ψ M` is the matrix representation
`(modelIso H ψ).inv ≫ toGLHom e M`, and `coeffRep_affineMatrix_apply` says that its matrix at a
point `x` is `M` with the classifying map of `x` applied to its entries. With
`homEquiv_symm_hom` (the universal point is classified by the identity), `univMatrix_coeffRep`
shows that the universal matrix of `coeffRep H ψ M` is `M`.

`hasLocalRightIntegrals_of_exists_isCompl`: if every stable subspace of every representation on
some `k^N` has a stable complement, then `HasLocalRightIntegrals ψ`. Given a finite `T`:

1. `V` is the published `Chevalley.regularSpan (insert 1 T)`: a finite-dimensional subspace of
   `B` containing `1` and `T`, stable under every `rightAct f`. With a basis `b` of `V`, the
   published `subspaceMatrix V b = M` is a matrix of multiplicative coefficients. Let `ρ` be
   `coeffRep H ψ M`, so its universal matrix is `M`.
2. The coordinate vector `u` of `1` in the basis `b` satisfies `M u = u`, because `comul 1 = 1 ⊗ 1`.
   So `k ∙ u` is stable. Take a stable complement `C`, and the functional `c` on `k^N` with
   `c(u) = 1` and `c(C) = 0`.
3. `c(coefficientMap ρ B ψ.hom ℓ v) = c(v) ℓ(1)` for every `ℓ` and `v`. Split `v` along
   `k ∙ u ⊕ C`. The `u`-part is multiplied by `ℓ(1)`, and `C` is stable.
   Testing against all `ℓ` (published `Unipotent.eq_of_forall_dual`) gives
   `∑ᵢ cᵢ Mᵢⱼ = cⱼ • 1` for every `j`, where `cᵢ = c(eᵢ)`.
4. Put `r = ∑ᵢ cᵢ · (i-th coordinate functional of b)`. Then `r(bⱼ) = cⱼ` and `r(1) = c(u) = 1`.
   Moreover `leftAct r (bⱼ) = ∑ᵢ cᵢ Mᵢⱼ = cⱼ • 1`: the left translates of `bⱼ` by coordinate
   functionals are the entries of `M`. By linearity `leftAct r y = r(y) • 1` for all `y ∈ V`,
   in particular for `y ∈ T`.

## Assembly

`linearlyReductive_iff_hasLocalRightIntegrals` combines the two lattice results with
`exists_isCompl_of_hasLocalRightIntegrals` and `hasLocalRightIntegrals_of_exists_isCompl`.

Two lemmas of the `Model` section, `modelIso_inv_hom_hom_eq` and `homEquiv_symm_hom`, are
elaborated with `set_option backward.isDefEq.respectTransparency false in`; the copied file sets
this option globally.
