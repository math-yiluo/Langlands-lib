# A splitting criterion from a universal subtorus and a finite part

This helper module serves the proof of
`Langlands.GroupScheme.MultiplicativeTypeQuasiIsotrivialStatement` (Conrad, *Reductive group
schemes* (2014), Proposition B.3.4, pp.290–292). It contains the last step of the local
argument. A group `G` over `X` is shown to be diagonalizable if two conditions
hold. First, `G` has a split universal subtorus `D_X(I' → ℤ)`. Second, `G` has a
homomorphism from a finite diagonalizable group `D_X(A)` that becomes the inclusion of the
finite factor after an fppf splitting of `G`. Conrad's proof does not isolate this step as a
lemma. All statements below are internal to the proof, and the module states nothing beyond
them.

Notation. `GroupScheme S` is `Grp (Over S)`. `D_S(Λ)` is
`RelativeMultiplicativeType.diagonalizable S Λ`, the base change along `S ⟶ Spec ℤ` of
`Diagonalizable.groupScheme ℤ Λ` (here `ℤ` stands for `ULift ℤ`). `G_W` is
`(GroupScheme.baseChange q).obj G`. `A ⊗ B` is the product of group schemes over `S`.
`prodHom a b hab : A ⊗ B ⟶ M` is the product homomorphism `(x, y) ↦ a(x) * b(y)`
of two homomorphisms whose values commute (`hab`), from
`Langlands.GroupScheme.Rational.SplitTorusFactorization`. `IsUniversalSubtorus` is the
Library predicate: a closed subgroup that is a relative torus and through which every
homomorphism from a relative torus factors, after any base change.

## Declarations

All names are in `Langlands.GroupScheme`.

### Product homomorphisms

Let `A`, `B`, `M` be group schemes over `S` and `a : A ⟶ M`, `b : B ⟶ M` homomorphisms.

- `commute_of_isCommMonObj`: if `M` is commutative (`IsCommMonObj M.X`), then for every
  `T : Over S` and points `x : T ⟶ A.X`, `y : T ⟶ B.X` the points `x ≫ a` and `y ≫ b` of `M`
  commute. This supplies the commutativity hypothesis of `prodHom` when the target is
  commutative.
- `prodHom_hom_hom`: the underlying morphism of `prodHom a b hab` is the product
  `(fst ≫ a) * (snd ≫ b)` in the monoid of morphisms `A.X ⊗ B.X ⟶ M.X`.
- `prodHom_congr`: `prodHom a b hab = prodHom a' b' hab'` if `a = a'` and `b = b'`.
- `prodHom_comp`: for a homomorphism `f : M ⟶ N`,
  `prodHom a b hab ≫ f = prodHom (a ≫ f) (b ≫ f) hab'`.
- `tensorHom_prodHom`: for homomorphisms `f : A' ⟶ A` and `g : B' ⟶ B`,
  `(f ⊗ₘ g) ≫ prodHom a b hab = prodHom (f ≫ a) (g ≫ b) hab'`.
- `baseChange_prodHom_inv`: for `q : S' ⟶ S`,
  `(baseChangeTensorIso q A B).inv ≫ (baseChange q).map (prodHom a b hab) =
  prodHom ((baseChange q).map a) ((baseChange q).map b) hab'`. Here
  `baseChangeTensorIso q A B : (A ⊗ B)_{S'} ≅ A_{S'} ⊗ B_{S'}` is the comparison
  isomorphism of `Langlands.GroupScheme.Torus.Products`.

In each lemma the commutativity proofs `hab`, `hab'` are arbitrary.

### Universal subtori

- `IsUniversalSubtorus.exists_iso`: let `j₁ : T₁ ⟶ H` and `j₂ : T₂ ⟶ H` be universal subtori
  of the same group scheme `H` over `S`. Then there is an isomorphism `g : T₁ ≅ T₂` with
  `g.hom ≫ j₂ = j₁`.

### The model decomposition

Let `e : Λ ≃+ (I → ℤ) × A` be an isomorphism of additive groups. `Diagonalizable.freeInclusion
R e : D(I → ℤ) ⟶ D(Λ)` and `Diagonalizable.freeInclusionOverScheme S e : D_S(I → ℤ) ⟶ D_S(Λ)`
are the inclusions of the free factor, induced by the projection
`Λ ⟶ I → ℤ` given by `e`.

All names in this subsection are in `Langlands.GroupScheme.Diagonalizable`.

- `finiteInclusion R e : D(A) ⟶ D(Λ)` (definition), over `Spec R` for a commutative ring
  `R`: the homomorphism `restrictMap R (snd ∘ e)` induced on diagonalizable groups by the
  projection `Λ ⟶ A` given by `e`. On points it sends a character `χ : A → Γ(T)ˣ` to the
  character `χ ∘ snd ∘ e` of `Λ`.
- `isIso_prodHom_freeInclusion_finiteInclusion R e`: the product homomorphism
  `prodHom (freeInclusion R e) (finiteInclusion R e) _ : D(I → ℤ) ⊗ D(A) ⟶ D(Λ)` is an
  isomorphism.
- `finiteInclusionOverScheme Y e : D_Y(A) ⟶ D_Y(Λ)` (definition), for a scheme `Y`: the base
  change of `finiteInclusion ℤ e` along `Y ⟶ Spec ℤ`. It is the finite-factor analogue of
  `freeInclusionOverScheme`.
- `isCommMonObj_diagonalizable Y Λ` (instance): `D_Y(Λ)` is commutative.
- `isIso_prodHom_freeInclusionOverScheme_finiteInclusionOverScheme Y e`: the product
  homomorphism
  `prodHom (freeInclusionOverScheme Y e) (finiteInclusionOverScheme Y e) _ :
  D_Y(I → ℤ) ⊗ D_Y(A) ⟶ D_Y(Λ)` is an isomorphism.

### The splitting criterion

- `isDiagonalizable_of_split_parts`: the hypotheses are as follows.
  - `q : W ⟶ X` is surjective, flat and locally of finite presentation.
  - `G` is a group scheme over `X`. Commutativity of `G` is not assumed; the proof derives
    it.
  - `I'` and `I` are finite types with decidable equality, `A` is a finite additive
    commutative group, and `e : Λ ≃+ (I → ℤ) × A`.
  - `τ : D_X(I' → ℤ) ⟶ G` is a universal subtorus (`hτ : IsUniversalSubtorus τ`).
  - `σ : D_X(A) ⟶ G` is a homomorphism.
  - `ψ : G_W ≅ D_W(Λ)` is an isomorphism of group schemes over `W`.
  - `hσ`: `(diagonalizableBaseChangeIso q A).inv ≫ σ_W ≫ ψ.hom =
    finiteInclusionOverScheme W e`. Here `diagonalizableBaseChangeIso q A :
    D_X(A)_W ≅ D_W(A)` is the comparison isomorphism.

  The conclusion is `RelativeMultiplicativeType.IsDiagonalizable G`. More precisely, the
  proof shows `G ≅ D_X((I' → ℤ) × A)`.

## Proofs

**Product homomorphisms.** `prodHom_hom_hom` is `comp_prodHom` at the identity point.
`prodHom_comp` is checked on points. It uses `comp_prodHom` and the fact that composing with
a homomorphism is multiplicative (`MonObj.mul_comp`). `tensorHom_prodHom` is checked on
underlying morphisms. It uses `prodHom_hom_hom`, `MonObj.comp_mul`, and
`(f ⊗ₘ g) ≫ fst = fst ≫ f` and its analogue for `snd`. `baseChange_prodHom_inv` is also checked
on underlying morphisms. Base change is the monoidal functor `Over.pullback q`, which
preserves products of morphisms into a monoid object (`Functor.map_mul`). The lemmas
`baseChangeTensorIso_inv_map_fst` and `baseChangeTensorIso_inv_map_snd` identify the
projections.

**Universal subtori.** By the factorization property in `IsUniversalSubtorus`, applied with
the identity base change, each of `j₁`, `j₂` factors through the other:
`a ≫ j₂ = j₁` and `c ≫ j₁ = j₂`. The underlying morphism of a closed subgroup is a
monomorphism (`IsClosedSubgroup.mono_overHom`). Hence `a ≫ c = 𝟙` and `c ≫ a = 𝟙`, and
`g := ⟨a, c⟩`.

**Model decomposition over `Spec R`.** Let `φ` be the isomorphism
`congrIso R e ≪≫ productIso R (I → ℤ) A : D(Λ) ≅ D(I → ℤ) ⊗ D(A)`. The proof shows
`φ.hom ≫ prodHom (freeInclusion R e) (finiteInclusion R e) _ = 𝟙` on points, using the
character description `characterPointsEquiv` of points of `D(Λ)`. A point `x` of
`D(Λ)` is a character `χ` of `Λ`. The two components of `φ.hom x` are the characters
`i ↦ χ(e⁻¹(i, 0))` of `I → ℤ` and `a ↦ χ(e⁻¹(0, a))` of `A`. The free and finite inclusions
then turn these into the characters
`l ↦ χ(e⁻¹((e l).1, 0))` and `l ↦ χ(e⁻¹(0, (e l).2))` of `Λ`. Their product is
`l ↦ χ(e⁻¹(e l)) = χ(l)`. The facts used are `pointsEquiv_restrictMap`, `congrIso_hom` and
`isoOfPointModels_hom` for `productIso`. Hence the product homomorphism equals `φ.inv` and is
an isomorphism.

**Model decomposition over `Y`.** The instance is Mathlib's `Functor.isCommMonObj_obj` for
the braided functor `Over.pullback (Y ⟶ Spec ℤ)`, applied to the commutative group
`D(Λ)`. By `baseChange_prodHom_inv` along `Y ⟶ Spec ℤ`, the product homomorphism over `Y` equals
`(baseChangeTensorIso _ _ _).inv` followed by the base change of the model isomorphism over
`Spec ℤ`. Hence it is an isomorphism.

**Splitting criterion.** Write `F` for base change along `q` and `dbci` for
`diagonalizableBaseChangeIso q`.

0. `G` is commutative. First, `G_W` is commutative: `isoPointsEquiv ψ U`
   identifies the points of `G_W` and `D_W(Λ)` over each `U` as groups, and `D_W(Λ)` is
   commutative (`isCommMonObj_diagonalizable`); Mathlib's `isCommMonObj_iff_isMulCommutative`
   turns this pointwise commutativity into `IsCommMonObj`. Second, the Library's
   `isCommMonObj_of_fppfCover` descends commutativity along an fppf cover. The cover used
   has the single member `q`; it is Mathlib's `Scheme.Cover.mkOfCovers` with index type
   `PUnit`, using that `q` is surjective, flat and locally of finite presentation.

The values of `τ` and `σ` commute because `G` is commutative, so
`Ψ := prodHom τ σ _ : D_X(I' → ℤ) ⊗ D_X(A) ⟶ G` is defined.

1. `τ_W := (dbci (I' → ℤ)).inv ≫ F.map τ ≫ ψ.hom : D_W(I' → ℤ) ⟶ D_W(Λ)` is a universal
   subtorus. This follows from `IsUniversalSubtorus.baseChange`, `comp_iso`
   and `iso_comp`.
2. The Library's `isUniversalSubtorus_freeInclusionOverScheme W e` says that
   `freeInclusionOverScheme W e` is also a universal subtorus of `D_W(Λ)`. By
   `IsUniversalSubtorus.exists_iso` there is `g : D_W(I' → ℤ) ≅ D_W(I → ℤ)` with
   `g.hom ≫ freeInclusionOverScheme W e = τ_W`.
3. The lemmas `baseChange_prodHom_inv`, `prodHom_comp`, `tensorHom_prodHom` and `prodHom_congr`,
   together with `hσ` and step 2, give
   `((dbci (I' → ℤ)).inv ⊗ₘ (dbci A).inv) ≫ (baseChangeTensorIso q _ _).inv ≫ F.map Ψ ≫
   ψ.hom = (g.hom ⊗ₘ 𝟙) ≫ prodHom (freeInclusionOverScheme W e)
   (finiteInclusionOverScheme W e) _`.
4. The right side is an isomorphism by the model decomposition over `W`. Cancelling the
   isomorphisms on both sides of `F.map Ψ` (`IsIso.of_isIso_comp_left`,
   `IsIso.of_isIso_comp_right`) shows that `F.map Ψ` is an isomorphism.
5. By `TorusIsomorphismLocus.isIso_of_fppf_baseChange`, `Ψ` is an isomorphism,
   because `q` is surjective, flat and locally of finite presentation.
6. `(I' → ℤ) × A` is a finitely generated `ℤ`-module, so it is a finitely generated abelian
   group (`Module.Finite.iff_addGroup_fg`). The required isomorphism is
   `G ≅ D_X(I' → ℤ) ⊗ D_X(A) ≅ (D(I' → ℤ) ⊗ D(A))_X ≅ D_X((I' → ℤ) × A)`. It is built from
   `Ψ⁻¹`, `(baseChangeTensorIso _ _ _).symm`, and the base change of
   `(productIso ℤ (I' → ℤ) A).symm`.

The module sets `backward.isDefEq.respectTransparency false` and
`backward.isDefEq.respectTransparency.types false`, as the Library's
`RelativeMultiplicativeType` and `DiagonalizableUniversalSubtorus` modules do.
