/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.OverProduct
public import WeilConjectures.AlgebraicGeometry.PolynomialAffineSpace
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineSmooth

/-!
# The relative projective line as a scheme over a base

For a scheme `B` over a base `S`, `AlgebraicGeometry.Scheme.overProjectiveLine B` is the
projective line `ℙ¹_B = ProjectiveLine B.left` as a scheme over `S`, through `B`. It is proper
and smooth of relative dimension one over `B`, functorial in `B`, and its formation commutes with
base change.

Over a field `k`, for `E` over `k` and `B = 𝔸ʲ_k ×_k E`, the scheme `𝔸^{j+1}_k ×_k E` is the
affine line over `B` with coordinate `X₀`, the coordinate forgotten by
`AlgebraicGeometry.polyAffineProj`; this embeds it into `ℙ¹_B` as an open subscheme, naturally
in `E`.

## Main definitions

- `AlgebraicGeometry.Scheme.overProjectiveLine`: the projective line `ℙ¹_B` over `B`, as a
  scheme over `S`.
- `AlgebraicGeometry.Scheme.overProjectiveLineProj`: the projection `ℙ¹_B ⟶ B`.
- `AlgebraicGeometry.Scheme.overProjectiveLineMap`,
  `AlgebraicGeometry.Scheme.overProjectiveLineIso`: functoriality of `ℙ¹_B` in `B`.
- `AlgebraicGeometry.Scheme.overAffineLineι`: the open immersion
  `𝔸^{j+1}_k ×_k E ⟶ ℙ¹_{𝔸ʲ_k ×_k E}`, `x ↦ [X₀(x) : 1]`.

## Main results

- `AlgebraicGeometry.Scheme.isPullback_overProjectiveLineMap`: `ℙ¹_B` commutes with base change.
- `AlgebraicGeometry.Scheme.overAffineLineι_proj`,
  `AlgebraicGeometry.Scheme.overAffineLineι_naturality`: the open immersion lies over the
  projection `𝔸^{j+1}_k ×_k E ⟶ 𝔸ʲ_k ×_k E` and is natural in `E`.
- `AlgebraicGeometry.Scheme.range_overAffineLineι`: the complement of its image is the section
  at infinity.
-/

@[expose] public section

universe u

open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry

namespace ProjectiveSpace

variable {n : Type u} {X S T : Scheme.{u}}

/-- `homOfSections` only depends on the structure morphism and the sections. -/
lemma homOfSections_congr {g g' : X ⟶ S} {s s' : n → Γ(X, ⊤)} (hg : g = g') (hs : s = s')
    {h : Ideal.span (Set.range s) = ⊤} {h' : Ideal.span (Set.range s') = ⊤} :
    homOfSections g s h = homOfSections g' s' h' := by
  subst hg hs
  rfl

/-- `homOfSections` is natural in the base: composing with `map n f` composes the structure
morphism with `f`. -/
@[reassoc (attr := simp)]
lemma homOfSections_map (g : X ⟶ S) (f : S ⟶ T) (s : n → Γ(X, ⊤))
    (hs : Ideal.span (Set.range s) = ⊤) :
    homOfSections g s hs ≫ map n f = homOfSections (g ≫ f) s hs :=
  hom_ext n T (by simp) (by
    rw [Category.assoc, map_toProjInt, homOfSections_toProjInt, homOfSections_toProjInt])

end ProjectiveSpace

namespace ProjectiveLine

/-- Pulling back the homogeneous coordinates `[a : b]` along `h` gives `[h^* a : h^* b]`. -/
lemma appTop_pairSections {X Y : Scheme.{u}} (h : Y ⟶ X) (a b : Γ(X, ⊤)) :
    (fun i ↦ h.appTop.hom (pairSections a b i)) =
      pairSections (h.appTop.hom a) (h.appTop.hom b) := by
  funext ⟨i⟩
  fin_cases i <;> rfl

end ProjectiveLine

section PolyAffine

variable (k : Type u) [Field k] (j : ℕ)

/-- The ring isomorphism `k[X₁, …, Xⱼ][T] ≅ k[X₀, …, Xⱼ]`, `T ↦ X₀`, `Xᵢ ↦ Xᵢ`, presenting
`k[X₀, …, Xⱼ]` as a polynomial ring in one variable over `k[X₁, …, Xⱼ]`. -/
def polyAffineSuccRingEquiv :
    MvPolynomial PUnit.{u + 1} (MvPolynomial (Fin j) k) ≃+* MvPolynomial (Fin (j + 1)) k :=
  (MvPolynomial.uniqueAlgEquiv _ PUnit.{u + 1}).toRingEquiv.trans
    (MvPolynomial.finSuccEquiv k j).symm.toRingEquiv

/-- `polyAffineSuccRingEquiv` is a ring isomorphism over `k[X₁, …, Xⱼ]`. -/
lemma polyAffineSuccRingEquiv_comp_C :
    (polyAffineSuccRingEquiv k j).toRingHom.comp MvPolynomial.C = polyAffineProjRingHom k j := by
  rw [polyAffineProjRingHom_eq]
  refine RingHom.ext fun r ↦ ?_
  have h := (MvPolynomial.uniqueAlgEquiv (MvPolynomial (Fin j) k) PUnit.{u + 1}).commutes r
  rw [MvPolynomial.algebraMap_eq, Polynomial.algebraMap_eq] at h
  simp [polyAffineSuccRingEquiv, h]

/-- `polyAffineSuccRingEquiv` sends the variable `T` to `X₀`. -/
lemma polyAffineSuccRingEquiv_X :
    polyAffineSuccRingEquiv k j (MvPolynomial.X PUnit.unit) = MvPolynomial.X 0 := by
  simp [polyAffineSuccRingEquiv, AlgEquiv.symm_apply_eq, MvPolynomial.finSuccEquiv_X_zero]

/-- The coordinate `X₀` of `𝔸^{j+1}_k`. -/
def polyAffineCoordZero : Γ(Spec (.of (MvPolynomial (Fin (j + 1)) k)), ⊤) :=
  (Scheme.ΓSpecIso (.of (MvPolynomial (Fin (j + 1)) k))).inv (MvPolynomial.X 0)

/-- `𝔸^{j+1}_k` is the affine line over `𝔸ʲ_k` with coordinate `X₀`: the morphism
`𝔸^{j+1}_k ⟶ 𝔸¹_{𝔸ʲ_k}` over `polyAffineProj` given by `X₀`. It is an isomorphism. -/
def polyAffineSuccHom : Spec (.of (MvPolynomial (Fin (j + 1)) k)) ⟶
    𝔸(PUnit.{u + 1}; Spec (.of (MvPolynomial (Fin j) k))) :=
  AffineSpace.homOfVector (Spec.map (CommRingCat.ofHom (polyAffineProjRingHom k j)))
    fun _ ↦ polyAffineCoordZero k j

/-- `polyAffineSuccHom` is `Spec` of `polyAffineSuccRingEquiv`. -/
lemma polyAffineSuccHom_eq :
    polyAffineSuccHom k j =
      Spec.map (CommRingCat.ofHom (polyAffineSuccRingEquiv k j).toRingHom) ≫
      (AffineSpace.SpecIso PUnit.{u + 1} (.of (MvPolynomial (Fin j) k))).inv := by
  refine AffineSpace.hom_ext ?_ fun _ ↦ ?_
  · rw [polyAffineSuccHom, AffineSpace.homOfVector_over, Category.assoc,
      AffineSpace.SpecIso_inv_over, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      polyAffineSuccRingEquiv_comp_C]
  · rw [polyAffineSuccHom, AffineSpace.homOfVector_appTop_coord, Scheme.Hom.comp_appTop,
      CommRingCat.comp_apply, AffineSpace.SpecIso_inv_appTop_coord, ← CommRingCat.comp_apply,
      ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply, polyAffineCoordZero,
      ← polyAffineSuccRingEquiv_X]
    rfl

instance : IsIso (polyAffineSuccHom k j) := by
  rw [polyAffineSuccHom_eq]
  have : IsIso (Spec.map (CommRingCat.ofHom (polyAffineSuccRingEquiv k j).toRingHom)) :=
    inferInstanceAs (IsIso (Spec.map (polyAffineSuccRingEquiv k j).toCommRingCatIso.hom))
  infer_instance

end PolyAffine

namespace Scheme

open ProjectiveSpace ProjectiveLine

section Base

variable {S : Scheme.{u}}

/-- The projective line `ℙ¹_B` over a scheme `B` over `S`, as a scheme over `S`. -/
def overProjectiveLine (B : Over S) : Over S :=
  Over.mk (ProjectiveLine B.left ↘ B.left ≫ B.hom)

instance (B : Over S) [LocallyOfFiniteType B.hom] :
    LocallyOfFiniteType (overProjectiveLine B).hom := by
  dsimp only [overProjectiveLine, Over.mk_hom]
  infer_instance

instance (B : Over S) [QuasiCompact B.hom] : QuasiCompact (overProjectiveLine B).hom := by
  dsimp only [overProjectiveLine, Over.mk_hom]
  infer_instance

instance (B : Over S) [IsSeparated B.hom] : IsSeparated (overProjectiveLine B).hom := by
  dsimp only [overProjectiveLine, Over.mk_hom]
  infer_instance

/-- The projection `ℙ¹_B ⟶ B`. -/
def overProjectiveLineProj (B : Over S) : overProjectiveLine B ⟶ B :=
  Over.homMk (ProjectiveLine B.left ↘ B.left) rfl

/-- The underlying morphism of `overProjectiveLineProj B` is the structure morphism. -/
lemma overProjectiveLineProj_left (B : Over S) :
    (overProjectiveLineProj B).left = ProjectiveLine B.left ↘ B.left :=
  rfl

instance (B : Over S) : IsProper (overProjectiveLineProj B).left :=
  inferInstanceAs (IsProper (ProjectiveLine B.left ↘ B.left))

instance (B : Over S) : SmoothOfRelativeDimension 1 (overProjectiveLineProj B).left :=
  inferInstanceAs (SmoothOfRelativeDimension 1 (ProjectiveLine B.left ↘ B.left))

/-- The morphism `ℙ¹_B ⟶ ℙ¹_{B'}` induced by a morphism `a : B ⟶ B'`. -/
def overProjectiveLineMap {B B' : Over S} (a : B ⟶ B') :
    overProjectiveLine B ⟶ overProjectiveLine B' :=
  Over.homMk (ProjectiveSpace.map _ a.left) (by
    simp [overProjectiveLine, Over.w a])

/-- The underlying morphism of `overProjectiveLineMap a` is `ProjectiveSpace.map`. -/
lemma overProjectiveLineMap_left {B B' : Over S} (a : B ⟶ B') :
    (overProjectiveLineMap a).left = ProjectiveSpace.map _ a.left :=
  rfl

/-- `ℙ¹` of the identity is the identity. -/
@[simp]
lemma overProjectiveLineMap_id (B : Over S) : overProjectiveLineMap (𝟙 B) = 𝟙 _ := by
  ext1
  exact ProjectiveSpace.map_id _ B.left

/-- `ℙ¹` of a composite is the composite. -/
@[reassoc]
lemma overProjectiveLineMap_comp {B B' B'' : Over S} (a : B ⟶ B') (a' : B' ⟶ B'') :
    overProjectiveLineMap (a ≫ a') = overProjectiveLineMap a ≫ overProjectiveLineMap a' := by
  ext1
  rw [overProjectiveLineMap_left, Over.comp_left, ProjectiveSpace.map_comp, Over.comp_left]
  rfl

/-- `overProjectiveLineMap a` lies over `a`. -/
@[reassoc (attr := simp)]
lemma overProjectiveLineMap_proj {B B' : Over S} (a : B ⟶ B') :
    overProjectiveLineMap a ≫ overProjectiveLineProj B' = overProjectiveLineProj B ≫ a := by
  ext1
  exact ProjectiveSpace.map_over _ a.left

/-- **`ℙ¹_B` commutes with base change**: for `a : B ⟶ B'`, `ℙ¹_B` is the base change of
`ℙ¹_{B'}` along `a`. -/
lemma isPullback_overProjectiveLineMap {B B' : Over S} (a : B ⟶ B') :
    IsPullback (overProjectiveLineMap a).left (overProjectiveLineProj B).left
      (overProjectiveLineProj B').left a.left :=
  ProjectiveSpace.isPullback_map _ a.left

/-- The isomorphism `ℙ¹_B ≅ ℙ¹_{B'}` induced by an isomorphism `e : B ≅ B'`. -/
@[simps]
def overProjectiveLineIso {B B' : Over S} (e : B ≅ B') :
    overProjectiveLine B ≅ overProjectiveLine B' where
  hom := overProjectiveLineMap e.hom
  inv := overProjectiveLineMap e.inv
  hom_inv_id := by rw [← overProjectiveLineMap_comp, e.hom_inv_id, overProjectiveLineMap_id]
  inv_hom_id := by rw [← overProjectiveLineMap_comp, e.inv_hom_id, overProjectiveLineMap_id]

/-- `ℙ¹` of the identity isomorphism is the identity. -/
@[simp]
lemma overProjectiveLineIso_refl (B : Over S) :
    overProjectiveLineIso (Iso.refl B) = Iso.refl _ := by
  ext1
  exact overProjectiveLineMap_id B

/-- `ℙ¹` of a composite isomorphism is the composite. -/
lemma overProjectiveLineIso_trans {B B' B'' : Over S} (e : B ≅ B') (e' : B' ≅ B'') :
    overProjectiveLineIso (e ≪≫ e') = overProjectiveLineIso e ≪≫ overProjectiveLineIso e' := by
  ext1
  exact overProjectiveLineMap_comp _ _

end Base

section AffineLine

variable {k : Type u} [Field k]

/-- The coordinate `X₀` of `𝔸^{j+1}_k`, pulled back to `𝔸^{j+1}_k ×_k E`. -/
def overAffineLineCoord (j : ℕ) (E : Over (Spec (.of k))) :
    Γ((overProd (polyAffine k (j + 1)) E).left, ⊤) :=
  (pullback.fst (polyAffine k (j + 1)).hom E.hom).appTop (polyAffineCoordZero k j)

/-- `𝔸^{j+1}_k ×_k E ⟶ 𝔸¹_{𝔸ʲ_k ×_k E}`, given by the coordinate `X₀`, is an isomorphism: it is
the base change of `polyAffineSuccHom` along `𝔸ʲ_k ×_k E ⟶ 𝔸ʲ_k`. -/
lemma isIso_homOfVector_overAffineLineCoord (j : ℕ) (E : Over (Spec (.of k))) :
    IsIso (AffineSpace.homOfVector (overProdMap (polyAffineProj k j) (𝟙 E)).left
      fun _ : PUnit.{u + 1} ↦ overAffineLineCoord j E) := by
  have h₀ : IsPullback (polyAffineSuccHom k j) (polyAffineProj k j).left
      (𝔸(PUnit.{u + 1}; (polyAffine k j).left) ↘ (polyAffine k j).left) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by
      rw [polyAffineSuccHom, AffineSpace.homOfVector_over, Category.comp_id]
      rfl⟩
  have h := (isPullback_overProdMap_left (polyAffineProj k j) E).flip.paste_horiz h₀
  rw [Category.comp_id] at h
  have h₂ := AffineSpace.isPullback_map (n := PUnit.{u + 1})
    (S := (overProd (polyAffine k j) E).left) (pullback.fst (polyAffine k j).hom E.hom)
  have hmid : AffineSpace.homOfVector ((overProdMap (polyAffineProj k j) (𝟙 E)).left ≫
      pullback.fst (polyAffine k j).hom E.hom) (fun _ : PUnit.{u + 1} ↦ overAffineLineCoord j E) =
        pullback.fst (polyAffine k (j + 1)).hom E.hom ≫ polyAffineSuccHom k j := by
    refine Eq.trans ?_ (AffineSpace.comp_homOfVector _ _ _).symm
    congr 1
    exact (isPullback_overProdMap_left (polyAffineProj k j) E).w
  have he : AffineSpace.homOfVector (overProdMap (polyAffineProj k j) (𝟙 E)).left
      (fun _ : PUnit.{u + 1} ↦ overAffineLineCoord j E) = (h.isoIsPullback _ _ h₂).hom := by
    refine h₂.hom_ext ?_ ?_
    · exact (AffineSpace.homOfVector_map _ _ _).trans
        (hmid.trans (IsPullback.isoIsPullback_hom_fst _ _ h h₂).symm)
    · exact (AffineSpace.homOfVector_over _ _).trans
        (IsPullback.isoIsPullback_hom_snd _ _ h h₂).symm
  rw [he]
  infer_instance

/-- The open immersion `𝔸^{j+1}_k ×_k E ⟶ ℙ¹_{𝔸ʲ_k ×_k E}`, `x ↦ [X₀(x) : 1]`, exhibiting
`𝔸^{j+1}_k ×_k E` as the affine line over `𝔸ʲ_k ×_k E` with coordinate `X₀`. -/
def overAffineLineι (j : ℕ) (E : Over (Spec (.of k))) :
    overProd (polyAffine k (j + 1)) E ⟶ overProjectiveLine (overProd (polyAffine k j) E) :=
  Over.homMk (homOfSections (overProdMap (polyAffineProj k j) (𝟙 E)).left
    (pairSections (overAffineLineCoord j E) 1) (span_range_pairSections_one _)) (by
      dsimp only [overProjectiveLine, Over.mk_hom]
      rw [homOfSections_over_assoc, Over.w])

/-- `overAffineLineι` is the isomorphism `𝔸^{j+1}_k ×_k E ≅ 𝔸¹_{𝔸ʲ_k ×_k E}` followed by the
affine chart. -/
lemma overAffineLineι_left (j : ℕ) (E : Over (Spec (.of k))) :
    (overAffineLineι j E).left =
      AffineSpace.homOfVector (overProdMap (polyAffineProj k j) (𝟙 E)).left
        (fun _ ↦ overAffineLineCoord j E) ≫ affineChart _ := by
  exact (homOfVector_comp_affineChart _ _).symm

instance (j : ℕ) (E : Over (Spec (.of k))) : IsOpenImmersion (overAffineLineι j E).left := by
  have := isIso_homOfVector_overAffineLineCoord j E
  rw [overAffineLineι_left]
  infer_instance

/-- `overAffineLineι` lies over the projection `𝔸^{j+1}_k ×_k E ⟶ 𝔸ʲ_k ×_k E`. -/
@[reassoc (attr := simp)]
lemma overAffineLineι_proj (j : ℕ) (E : Over (Spec (.of k))) :
    overAffineLineι j E ≫ overProjectiveLineProj _ = overProdMap (polyAffineProj k j) (𝟙 E) := by
  ext1
  exact homOfSections_over _ _ (span_range_pairSections_one _)

/-- `overAffineLineι` is natural in `E`. -/
@[reassoc]
lemma overAffineLineι_naturality (j : ℕ) {E E' : Over (Spec (.of k))} (b : E ⟶ E') :
    overProdMap (𝟙 _) b ≫ overAffineLineι j E' =
      overAffineLineι j E ≫ overProjectiveLineMap (overProdMap (𝟙 _) b) := by
  have hg : (overProdMap (𝟙 (polyAffine k (j + 1))) b).left ≫
      (overProdMap (polyAffineProj k j) (𝟙 E')).left =
        (overProdMap (polyAffineProj k j) (𝟙 E)).left ≫
          (overProdMap (𝟙 (polyAffine k j)) b).left := by
    simp only [← Over.comp_left, ← overProdMap_comp, Category.comp_id, Category.id_comp]
  have hfst : (overProdMap (𝟙 (polyAffine k (j + 1))) b).left ≫
      pullback.fst (polyAffine k (j + 1)).hom E'.hom =
        pullback.fst (polyAffine k (j + 1)).hom E.hom := by
    simp [overProdMap_left]
  have hs : (fun i ↦ (overProdMap (𝟙 (polyAffine k (j + 1))) b).left.appTop.hom
      (pairSections (overAffineLineCoord j E') 1 i)) =
        pairSections (overAffineLineCoord j E) 1 := by
    rw [appTop_pairSections, map_one, overAffineLineCoord, overAffineLineCoord, ← hfst]
    rfl
  ext1
  exact (comp_homOfSections _ _ _ (span_range_pairSections_one _)).trans
    ((homOfSections_congr hg hs).trans
      (homOfSections_map _ _ _ (span_range_pairSections_one _)).symm)

/-- **The complement of `𝔸^{j+1}_k ×_k E` in `ℙ¹_{𝔸ʲ_k ×_k E}` is the section at infinity**:
the image of `overAffineLineι` is the complement of the image of `ProjectiveLine.infinity`. -/
lemma range_overAffineLineι (j : ℕ) (E : Over (Spec (.of k))) :
    Set.range (overAffineLineι j E).left =
      (Set.range (infinity (overProd (polyAffine k j) E).left))ᶜ := by
  have := isIso_homOfVector_overAffineLineCoord j E
  rw [range_infinity, compl_compl, overAffineLineι_left, ← Scheme.Hom.coe_opensRange,
    Scheme.Hom.opensRange_comp_of_isIso]

end AffineLine

end Scheme

end AlgebraicGeometry
