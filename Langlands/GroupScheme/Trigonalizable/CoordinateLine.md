# Trigonalizable group schemes and semi-invariant lines in coordinate bialgebras

This module is an internal helper for the proof of
`Langlands.GroupScheme.TrigonalizableBaseChangeStatement` (Milne, *Algebraic Groups* (2017),
Corollary 16.4). Milne proves that corollary by embedding `G` in the group `T_n` of upper
triangular matrices. This module does not follow that route. Instead it adapts the published
proof that unipotence survives base change (`Langlands.GroupScheme.Unipotent.CoordinateBialgebra`
and `Langlands.GroupScheme.Unipotent.ScalarExtension`), replacing fixed vectors with stable lines.
Every result is proved here from the Library definitions; nothing is cited.

## The predicate `LineStable`

`LineStable K B` is an internal predicate on a bialgebra `B` over a field `K`. It has no
counterpart in the literature and is introduced only for this proof. It says: every nonzero
finite-dimensional subspace `V ⊆ B` that is stable under all right translations
`rightAct f` (`f` a `K`-linear functional on `B`; the Library's
`AffineLinearEmbedding.rightAct`, `(id ⊗ f) ∘ comul`) contains some `y ≠ 0` with
`comul y = y ⊗ χ` for some `χ ∈ B`. Such a `y` is called a semi-invariant with multiplier `χ`.
For a group scheme, `χ` is the character by which the group acts on the line through `y`.

## Linear algebra (section `Bialgebra`)

* `rightAct_of_comul_eq`: if `comul y = y ⊗ χ`, then `rightAct g y = g χ • y` for every
  functional `g`.
* `exists_semiInvariant` is the analogue of the Library's `Unipotent.exists_invariant`. Suppose
  `LineStable K B` holds. Let `M` be a module with operators `T g` indexed by functionals `g` on
  `B`, and let `π i : M → B` be a jointly injective family of linear maps with
  `π i ∘ T g = rightAct g ∘ π i`. Then every nonzero finite-dimensional `T`-stable subspace
  `W ⊆ M` contains `w ≠ 0` and some `χ` with `T g w = g χ • w` for all `g`.

  The proof is by strong induction on `finrank W`. Choose `w₀ ≠ 0` in `W` and an index `i` with
  `π i w₀ ≠ 0`. If `W ∩ ker (π i) = 0`, apply `LineStable` to the stable subspace `π i (W)`. This
  gives a semi-invariant `π i w` with multiplier `χ`. Then `T g w - g χ • w` lies in
  `W ∩ ker (π i) = 0`, by `rightAct_of_comul_eq`. Otherwise `W ∩ ker (π i)` is a nonzero
  `T`-stable subspace of smaller dimension (it misses `w₀`), and the induction hypothesis applies.

## Trigonalizability in coordinates (section `Corepresented`)

Let `F : CommAlgCat k ⥤ GrpCat` be corepresented by `B` via `e`, over a field `k`. The
coordinate bialgebra is the Library's `AffineLinearEmbedding.bialgebra e`.

* `lineStable_of_isTrigonalizable`: if `Corepresented.groupScheme F e` is trigonalizable, then
  `LineStable k B`. Let `V` be a nonzero finite-dimensional stable subspace with basis `b`.
  Trigonalizability, applied to the Library's `Chevalley.regularRepresentation e hR V b hV`, gives
  a nonzero `v` spanning a stable line. Evaluate the stable-line equation at the universal point
  `𝟙 : Spec B ⟶ G`. As in `Unipotent.oneMemStable_of_isUnipotent`, the matrix there is
  `subspaceMatrix V b` carried along the section comparison `Corepresented.affineSectionsIso B`,
  whose inverse `φ` is bijective. Write the multiplier as `φ χ`. Injectivity of `φ` gives
  `∑ⱼ vⱼ • subspaceMatrix i j = vᵢ • χ` for each row `i`. With `comul_basis`, the element
  `y = ∑ⱼ vⱼ • bⱼ ∈ V` satisfies `comul y = y ⊗ χ`. It is nonzero because the `bⱼ` are linearly
  independent and `v ≠ 0`.
* `isTrigonalizable_of_lineStable`: conversely, `LineStable k B` implies that
  `Corepresented.groupScheme F e` is trigonalizable. Let `ρ` be a matrix representation indexed
  by a nonempty finite type `n`. Let `N = universalMatrix e ρ`; the Library's
  `comul_universalMatrix` and `counit_universalMatrix` give `comul (N i j) = ∑ₗ N i l ⊗ N l j` and
  `ε (N i j) = δᵢⱼ`. On `kⁿ`, put `T g = (N.map g).mulVec` and `π i v = ∑ⱼ vⱼ • N i j`. Then
  `π i ∘ T g = rightAct g ∘ π i`, and the counit shows that the `π i` are jointly injective.
  `exists_semiInvariant`, applied to `⊤ ⊆ kⁿ`, gives `w ≠ 0` and `χ ∈ B` with `T g w = g χ • w`
  for all `g`. Separating by functionals (`Unipotent.eq_of_forall_dual`) gives
  `∑ⱼ wⱼ • N i j = wᵢ • χ`. At an arbitrary point `g : T' ⟶ G`, the matrix of `ρ` is `N` mapped
  along the ring map `ψ : B → Γ(T', ⊤)` determined by `g` (`pointMatrix_naturality`,
  `pointMatrix_eq_affineMatrix`). Mapping the row identity along `ψ` shows that `w` spans a
  stable line with multiplier `ψ χ`.

## Extension of scalars (section `ScalarExtension`)

Let `k → K` be a field extension and `B` a `k`-bialgebra. `K ⊗[k] B` carries Mathlib's
tensor-product `K`-bialgebra structure.

* `tensor_ext_right`: over a field `k`, two tensors `t, t' ∈ M ⊗[k] N` are equal if
  `rid ((id ⊗ g) t) = rid ((id ⊗ g) t')` for every functional `g` on `N`. Proof: compare
  coefficients in `TensorProduct.equivFinsuppOfBasisRight` for a basis of `N`; these are the
  contractions with the coordinate functionals.
* `comul_baseChange_of_semiInvariant`: suppose `w ∈ K ⊗[k] B` and `χ ∈ B` satisfy
  `(rightAct g).lTensor K w = g χ • w` for every `k`-functional `g` on `B`. Then `w` is a
  semi-invariant of `K ⊗[k] B` with multiplier `1 ⊗ χ`, that is,
  `comul w = w ⊗[K] (1 ⊗ χ)`. Let `Φ : (K ⊗[k] B) ⊗[k] B → (K ⊗[k] B) ⊗[K] (K ⊗[k] B)` send
  `m ⊗ b` to `m ⊗ (1 ⊗ b)`. On pure tensors one checks that the comultiplication of `K ⊗[k] B` is
  `Φ ∘ assoc⁻¹ ∘ (id_K ⊗ comul_B)`. Contracting `assoc⁻¹ ((id_K ⊗ comul_B) w)` with any `g`
  gives `(rightAct g).lTensor K w = g χ • w`. This is also the contraction of `w ⊗ χ`, so
  `tensor_ext_right` gives `assoc⁻¹ ((id_K ⊗ comul_B) w) = w ⊗ χ`. Applying `Φ` gives the claim.
* `LineStable.baseChange`: `LineStable k B` implies `LineStable K (K ⊗[k] B)`. The argument is
  the one in `Unipotent.OneMemStable.baseChange`, with `exists_semiInvariant` in place of
  `exists_invariant`. Let `V` be a nonzero finite-dimensional `K`-subspace stable under all
  `K`-linear right translations. View `K ⊗[k] B` as a `k`-module with:
  * the operators `T g = (rightAct g).lTensor K` for `k`-functionals `g` on `B`; they preserve
    `V` by the Library's `rightAct_baseChange`;
  * the projections `π l = lid ∘ (l ⊗ id)` for `k`-functionals `l` on `K`; they satisfy
    `π l ∘ T g = rightAct g ∘ π l` and are jointly injective by `tensor_ext_left`.

  `V` need not be finite-dimensional over `k`, so pick `v₀ ≠ 0` in `V` and write it as a finite
  sum of pure tensors. Let `L ⊆ K` be the `k`-span of the first factors and
  `U = regularSpan` of the second factors, a finite-dimensional stable subspace. Then
  `W = image (L ⊗ U → K ⊗ B) ∩ V` is a nonzero, finite-dimensional, `T`-stable `k`-subspace.
  `exists_semiInvariant` gives `w ≠ 0` in `W` and `χ` with `T g w = g χ • w`. By
  `comul_baseChange_of_semiInvariant`, `w ∈ V` is a semi-invariant with multiplier `1 ⊗ χ`.

## Invariance under isomorphism

`Langlands.GroupScheme.IsTrigonalizable.of_iso`: if `H ≅ H'` are group schemes over `Spec k` and
`H'` is trigonalizable, then so is `H`. A representation `ρ` of `H` is restricted along `e.inv`
to a representation of `H'` (`MatrixRepresentation.restrict`). A stable line for the restricted
representation is a stable line for `ρ`: evaluate at `g ≫ e.hom` and use
`pointMatrix_restrict` and `e.hom ≫ e.inv = 𝟙`.

The transport of trigonalizability across an isomorphism uses `IsTrigonalizable.of_iso` from `MatrixCriterion`.
