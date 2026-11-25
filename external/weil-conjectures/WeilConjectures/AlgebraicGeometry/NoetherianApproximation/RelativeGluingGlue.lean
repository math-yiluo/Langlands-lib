/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.AlgebraicGeometry.NoetherianApproximation.RelativeGluingValid

/-!
# Finite-presentation descent by relative gluing

Let `{Dⱼ}` be a cofiltered system of quasi-compact quasi-separated schemes with affine
transition maps and limit `S = lim Dⱼ`, and let `g : X ⟶ S` be of finite presentation. Gluing the
valid relative gluing datum `R_{X,λ_rel}`
(`AlgebraicGeometry.RelativeAffinePresentation.ChartModels.validDatum`) gives a scheme
`X_λ ⟶ D_λ` of finite presentation (`λ = λ_rel`), and gluing the chartwise identifications gives
a morphism `X ⟶ X_λ` which exhibits `X` as the base change `X_λ ×_{D_λ} S`.

## Main definitions and results

- `AlgebraicGeometry.Scheme.isPullback_of_isOpenImmersion_family`: a commutative square is
  cartesian if it is so over an open cover of the top right corner.
- `AlgebraicGeometry.RelativeAffinePresentation.ChartModels.descended`,
  `AlgebraicGeometry.RelativeAffinePresentation.ChartModels.descendedHom`: the glued scheme
  `X_λ ⟶ D_λ`.
- `AlgebraicGeometry.RelativeAffinePresentation.ChartModels.toDescended`: the glued morphism
  `X ⟶ X_λ`.
- `AlgebraicGeometry.RelativeAffinePresentation.ChartModels.descendedIso`: the comparison
  isomorphism `ε_X : X_λ ×_{D_λ} S ≅ X`.
- `AlgebraicGeometry.RelativeAffinePresentation.ChartModels.isPullback_toDescended`: the
  square is cartesian.
- `AlgebraicGeometry.finitePresentationDescent`, `AlgebraicGeometry.finitePresentationDescentHom`,
  `AlgebraicGeometry.finitePresentationDescentIso`: the construction for the selected
  presentation and chart models, with `AlgebraicGeometry.isPullback_finitePresentationDescent`.

## Implementation details

`AlgebraicGeometry.isPullback_finitePresentationDescent` is an explicit construction for
Stacks 01ZM; the existence statement is
`AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation`.

## References

* Stacks Project, Tag 01ZM
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- A commutative square `h ≫ s = g ≫ π` is cartesian if `Z` is covered by open immersions
`ιₐ : Uₐ ⟶ Z` whose preimages `ℓₐ : Lₐ ⟶ X` form cartesian squares over `π`. -/
theorem Scheme.isPullback_of_isOpenImmersion_family {X Z S B : Scheme.{u}} {h : X ⟶ Z} {g : X ⟶ S}
    {s : Z ⟶ B} {π : S ⟶ B} (comm : CommSq h g s π) {J : Type*} {U : J → Scheme.{u}}
    (ι : ∀ a, U a ⟶ Z) [∀ a, IsOpenImmersion (ι a)] (hcov : ⨆ a, (ι a).opensRange = ⊤)
    {L : J → Scheme.{u}} (ℓ : ∀ a, L a ⟶ X) [∀ a, IsOpenImmersion (ℓ a)] (m : ∀ a, L a ⟶ U a)
    (hm : ∀ a, IsPullback (m a) (ℓ a) (ι a) h)
    (hsq : ∀ a, IsPullback (m a) (ℓ a ≫ g) (ι a ≫ s) π) : IsPullback h g s π := by
  let κ : X ⟶ pullback s π := pullback.lift h g comm.w
  let W (a : J) : (pullback s π).Opens := pullback.fst s π ⁻¹ᵁ (ι a).opensRange
  let q (a : J) : (W a).toScheme ⟶ U a :=
    IsOpenImmersion.lift (ι a) ((W a).ι ≫ pullback.fst s π) (by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Hom.comp_apply]
      exact x.2)
  have hq (a : J) : q a ≫ ι a = (W a).ι ≫ pullback.fst s π := IsOpenImmersion.lift_fac _ _ _
  have hW (a : J) : IsPullback (q a) ((W a).ι ≫ pullback.snd s π) (ι a ≫ s) π :=
    (IsOpenImmersion.isPullback (q a) (W a).ι (ι a) (pullback.fst s π) (hq a).symm
      (by rw [Scheme.Opens.opensRange_ι])).paste_vert (IsPullback.of_hasPullback s π)
  let e (a : J) : L a ≅ (W a).toScheme := (hsq a).isoIsPullback _ _ (hW a)
  let v (a : J) : L a ⟶ pullback s π := (e a).hom ≫ (W a).ι
  have hv (a : J) : ℓ a ≫ κ = v a := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.assoc, ← hq, ← (hm a).w]
      exact (IsPullback.isoIsPullback_hom_fst_assoc _ _ (hsq a) (hW a) _).symm
    · rw [Category.assoc, pullback.lift_snd]
      exact (IsPullback.isoIsPullback_hom_snd _ _ (hsq a) (hW a)).symm
  have hrange (a : J) : κ ⁻¹ᵁ (v a).opensRange = (ℓ a).opensRange := by
    have e₁ := Scheme.Hom.opensRange_comp_of_isIso (hm a).isoPullback.hom
      (pullback.snd (ι a) h)
    simp only [IsPullback.isoPullback_hom_snd] at e₁
    rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Opens.opensRange_ι,
      ← Scheme.Hom.comp_preimage, pullback.lift_fst, e₁, Scheme.Hom.opensRange_pullbackSnd]
  have (a : J) : IsOpenImmersion (v a) := by
    dsimp only [v]
    infer_instance
  let 𝒰 : (pullback s π).OpenCover := Scheme.Cover.mkOfCovers J L v (fun x ↦ by
    have hx : pullback.fst s π x ∈ ⨆ a, (ι a).opensRange := by
      rw [hcov]
      trivial
    obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    have hx' : x ∈ (v a).opensRange := by
      rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Opens.opensRange_ι]
      exact ha
    obtain ⟨y, hy⟩ := hx'
    exact ⟨a, y, hy⟩)
  have hiso : IsIso κ := by
    refine IsZariskiLocalAtTarget.of_openCover (P := MorphismProperty.isomorphisms Scheme) 𝒰
      fun a ↦ ?_
    have hp : IsPullback (ℓ a) (𝟙 (L a)) κ (v a) :=
      (IsOpenImmersion.isPullback (𝟙 (L a)) (ℓ a) (v a) κ (by rw [hv, Category.id_comp])
        (hrange a)).flip
    have e' : 𝒰.pullbackHom κ a = hp.isoPullback.inv := by
      rw [← cancel_epi hp.isoPullback.hom, Iso.hom_inv_id]
      exact IsPullback.isoPullback_hom_snd _
    rw [e']
    exact inferInstanceAs (IsIso _)
  exact IsPullback.of_iso_pullback comm (asIso κ) (pullback.lift_fst _ _ _)
    (pullback.lift_snd _ _ _)

namespace RelativeAffinePresentation.ChartModels

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} {c : Cone D} (hc : IsLimit c)
  [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
  {X : Scheme.{u}} {g : X ⟶ c.pt} {R : RelativeAffinePresentation c g} (M : R.ChartModels)
  [QuasiSeparatedSpace X]

/-- The scheme `X^desc_{λ_rel}` obtained by gluing the valid relative datum `R_{X,λ_rel}`. -/
noncomputable def descended : Scheme.{u} :=
  RelativeGluingDatum.glued (M.isValid_validDatum hc)

/-- The structure morphism
`X^desc_{λ_rel} ⟶ D_{λ_rel}`. -/
noncomputable def descendedHom : M.descended hc ⟶ D.obj (M.relStage hc).left :=
  RelativeGluingDatum.toBase (M.isValid_validDatum hc)

/-- The open immersion of the chart `Yₐ ×_{D_i} D_{λ_rel}` into `X^desc_{λ_rel}`. -/
noncomputable abbrev descendedι (a : R.J) :
    pullback (M.p a) (D.map (M.relStage hc).hom) ⟶ M.descended hc :=
  RelativeGluingDatum.ι (M.isValid_validDatum hc) a

/-- The base change map `Yₐ ×_{D_i} lim Dⱼ ⟶ Yₐ ×_{D_i} D_{λ_rel}`. -/
noncomputable abbrev limitChartMap (a : R.J) :
    pullback (M.p a) (c.π.app M.stage) ⟶ pullback (M.p a) (D.map (M.relStage hc).hom) :=
  RelativeGluingDatum.chartMap M.p (c.π.app (M.relStage hc).left) (c.w (M.relStage hc).hom) a

omit [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
  [QuasiSeparatedSpace X] in
lemma exists_ℓ_eq (x : X) :
    ∃ (a : R.J) (y : ↥(pullback (M.p a) (c.π.app M.stage))), M.ℓ a y = x := by
  have hx : x ∈ ⨆ a, (M.ℓ a).opensRange := by
    rw [M.iSup_opensRange_ℓ]
    trivial
  obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  obtain ⟨y, hy⟩ := ha
  exact ⟨a, y, hy⟩

/-- The open cover of `X` by the charts `ℓₐ : Lₐ ⟶ X`. -/
noncomputable def limitCover : X.OpenCover :=
  Scheme.Cover.mkOfCovers R.J _ M.ℓ M.exists_ℓ_eq

lemma limitChartMap_ι_compat (a b : R.J) :
    pullback.fst (M.ℓ a) (M.ℓ b) ≫ M.limitChartMap hc a ≫ M.descendedι hc a =
      pullback.snd (M.ℓ a) (M.ℓ b) ≫ M.limitChartMap hc b ≫ M.descendedι hc b := by
  have hv := M.isValid_validDatum hc
  have hcomp := M.isCompatible_validDatum hc
  have hT := RelativeGluingDatum.isTransport_transport (c.π.app (M.relStage hc).left)
    (c.w (M.relStage hc).hom) (M.validDatum hc)
  have hsub : Set.range (pullback.fst (M.ℓ a) (M.ℓ b)) ⊆
      ((M.limitTransport (M.validDatum hc)).V a b : Set ↥(pullback (M.p a) (c.π.app M.stage))) := by
    rintro _ ⟨x, rfl⟩
    rw [hcomp.V_eq]
    simp only [SetLike.mem_coe, Scheme.Hom.mem_preimage, Scheme.Hom.mem_opensRange]
    refine ⟨pullback.snd (M.ℓ a) (M.ℓ b) x, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]
  let κ := IsOpenImmersion.lift ((M.limitTransport (M.validDatum hc)).V a b).ι
    (pullback.fst (M.ℓ a) (M.ℓ b)) (by rwa [Scheme.Opens.range_ι])
  have hκ : κ ≫ ((M.limitTransport (M.validDatum hc)).V a b).ι = pullback.fst _ _ :=
    IsOpenImmersion.lift_fac _ _ _
  have hκ' : κ ≫ (M.limitTransport (M.validDatum hc)).map a b = pullback.snd _ _ := by
    rw [← cancel_mono (M.ℓ b), Category.assoc, hcomp.map_comp, reassoc_of% hκ,
      pullback.condition]
  rw [← hκ, Category.assoc, ← Scheme.Hom.resLE_comp_ι_assoc (M.limitChartMap hc a) (hT.V_eq a b).le,
    ← RelativeGluingDatum.glue_condition, ← hT.map_chartMap_assoc, reassoc_of% hκ']

/-- The morphism
`X ⟶ X^desc_{λ_rel}` glued from the chartwise identifications
`Wₐ ≅ Yₐ ×_{D_i} lim Dⱼ ⟶ Yₐ ×_{D_i} D_{λ_rel}`. -/
noncomputable def toDescended : X ⟶ M.descended hc :=
  (M.limitCover).glueMorphisms (fun a ↦ M.limitChartMap hc a ≫ M.descendedι hc a)
    (M.limitChartMap_ι_compat hc)

@[reassoc]
lemma ℓ_toDescended (a : R.J) :
    M.ℓ a ≫ M.toDescended hc = M.limitChartMap hc a ≫ M.descendedι hc a :=
  Scheme.Cover.ι_glueMorphisms M.limitCover _ _ a

lemma toDescended_descendedHom :
    M.toDescended hc ≫ M.descendedHom hc = g ≫ c.π.app (M.relStage hc).left := by
  refine Scheme.Cover.hom_ext M.limitCover _ _ fun a ↦ ?_
  have h₁ := M.ℓ_toDescended_assoc hc a (M.descendedHom hc)
  have h₂ := M.ℓ_comp_assoc a (c.π.app (M.relStage hc).left)
  rw [descendedHom, RelativeGluingDatum.ι_toBase, RelativeGluingDatum.chartMap_snd] at h₁
  exact h₁.trans h₂.symm

lemma preimage_toDescended (a : R.J) :
    M.toDescended hc ⁻¹ᵁ (M.descendedι hc a).opensRange = (M.ℓ a).opensRange := by
  have hcomp := M.isCompatible_validDatum hc
  ext x
  obtain ⟨b, y, rfl⟩ := M.exists_ℓ_eq x
  have e₁ : (M.ℓ b ≫ M.toDescended hc) y ∈ (M.descendedι hc a).opensRange ↔
      M.limitChartMap hc b y ∈ (M.validDatum hc).V b a := by
    rw [M.ℓ_toDescended, ← RelativeGluingDatum.preimage_opensRange_ι (M.isValid_validDatum hc),
      Scheme.Hom.comp_apply]
    rfl
  have e₂ : M.ℓ b y ∈ (M.ℓ a).opensRange ↔
      y ∈ (M.limitTransport (M.validDatum hc)).V b a := by
    rw [hcomp.V_eq]
    rfl
  rw [SetLike.mem_coe, Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, e₁, SetLike.mem_coe, e₂]
  rfl

/-- The morphism
`X ⟶ X^desc_{λ_rel}` exhibits `X` as the base change of `X^desc_{λ_rel} ⟶ D_{λ_rel}` along
`lim Dⱼ ⟶ D_{λ_rel}`. -/
theorem isPullback_toDescended :
    IsPullback (M.toDescended hc) g (M.descendedHom hc) (c.π.app (M.relStage hc).left) :=
  Scheme.isPullback_of_isOpenImmersion_family (CommSq.mk (M.toDescended_descendedHom hc))
    (M.descendedι hc)
    (RelativeGluingDatum.iSup_opensRange_ι _) M.ℓ (M.limitChartMap hc)
    (fun a ↦ IsOpenImmersion.isPullback _ _ _ _ (M.ℓ_toDescended hc a)
      (M.preimage_toDescended hc a))
    (fun a ↦ by
      rw [ℓ_comp, descendedHom, RelativeGluingDatum.ι_toBase]
      exact isPullback_baseChangeCone_π D c (M.p a) (M.relStage hc))

/-- The isomorphism
`ε_X : X^desc_{λ_rel} ×_{D_{λ_rel}} lim Dⱼ ≅ X` over `lim Dⱼ`, the inverse of the morphism
`X ⟶ X^desc_{λ_rel} ×_{D_{λ_rel}} lim Dⱼ` induced by the glued chartwise identifications. -/
noncomputable def descendedIso :
    pullback (M.descendedHom hc) (c.π.app (M.relStage hc).left) ≅ X :=
  (M.isPullback_toDescended hc).isoPullback.symm

@[reassoc (attr := simp)]
lemma descendedIso_hom_comp :
    (M.descendedIso hc).hom ≫ g = pullback.snd _ _ := by
  simp [descendedIso]

@[reassoc (attr := simp)]
lemma descendedIso_inv_fst :
    (M.descendedIso hc).inv ≫ pullback.fst _ _ = M.toDescended hc := by
  simp [descendedIso]

instance locallyOfFinitePresentation_descendedHom :
    LocallyOfFinitePresentation (M.descendedHom hc) :=
  RelativeGluingDatum.locallyOfFinitePresentation_toBase _

instance compactSpace_descended : CompactSpace (M.descended hc) :=
  RelativeGluingDatum.compactSpace_glued _

instance quasiCompact_descendedHom [∀ i, QuasiSeparatedSpace (D.obj i)] :
    QuasiCompact (M.descendedHom hc) :=
  inferInstance

instance quasiSeparatedSpace_descended : QuasiSeparatedSpace (M.descended hc) := by
  have (a : R.J) : IsAffine (pullback (M.p a) (D.map (M.relStage hc).hom)) := by
    have : IsAffineHom (pullback.fst (M.p a) (D.map (M.relStage hc).hom)) :=
      MorphismProperty.pullback_fst _ _ inferInstance
    exact isAffine_of_isAffineHom (pullback.fst (M.p a) (D.map (M.relStage hc).hom))
  exact RelativeGluingDatum.quasiSeparatedSpace_glued _ (M.isCompact_validDatum_V hc)

instance quasiSeparated_descendedHom : QuasiSeparated (M.descendedHom hc) :=
  inferInstance

end RelativeAffinePresentation.ChartModels

section Selected

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} {c : Cone D} (hc : IsLimit c)
  [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ i, QuasiSeparatedSpace (D.obj i)]
  {X : Scheme.{u}} (g : X ⟶ c.pt) [LocallyOfFinitePresentation g] [CompactSpace X]
  [QuasiSeparatedSpace X] [Nonempty I]

/-- The selected chart models of the selected relative affine presentation of `g`. -/
noncomputable abbrev finitePresentationDescentModels :
    (relativeAffinePresentation g).ChartModels :=
  (relativeAffinePresentation g).chartModels hc

/-- The stage `λ_rel(X/S)` of the finite-presentation descent construction. -/
noncomputable abbrev finitePresentationDescentStage : I :=
  ((finitePresentationDescentModels hc g).relStage hc).left

/-- Finite-presentation descent
construction. The scheme `X^desc_{λ_rel}`, glued from the valid relative datum
`R_{X,λ_rel}` of the selected presentation. -/
noncomputable abbrev finitePresentationDescent : Scheme.{u} :=
  (finitePresentationDescentModels hc g).descended hc

/-- The structure morphism
`X^desc_{λ_rel} ⟶ D_{λ_rel}`. -/
noncomputable abbrev finitePresentationDescentHom :
    finitePresentationDescent hc g ⟶ D.obj (finitePresentationDescentStage hc g) :=
  (finitePresentationDescentModels hc g).descendedHom hc

/-- The comparison isomorphism
`ε_X : X^desc_{λ_rel} ×_{D_{λ_rel}} lim Dⱼ ≅ X`, obtained by gluing the chartwise
identifications. -/
noncomputable abbrev finitePresentationDescentIso :
    pullback (finitePresentationDescentHom hc g) (c.π.app (finitePresentationDescentStage hc g))
      ≅ X :=
  (finitePresentationDescentModels hc g).descendedIso hc

/-- The constructed `X^desc_{λ_rel} ⟶ D_{λ_rel}` is of finite presentation (locally of finite
presentation, quasi-compact and quasi-separated), and the square formed by `X ⟶ X^desc_{λ_rel}`,
`g` and the projections is cartesian. -/
theorem isPullback_finitePresentationDescent :
    LocallyOfFinitePresentation (finitePresentationDescentHom hc g) ∧
      QuasiCompact (finitePresentationDescentHom hc g) ∧
      QuasiSeparated (finitePresentationDescentHom hc g) ∧
      IsPullback ((finitePresentationDescentModels hc g).toDescended hc) g
        (finitePresentationDescentHom hc g) (c.π.app (finitePresentationDescentStage hc g)) :=
  ⟨inferInstance, inferInstance, inferInstance,
    (finitePresentationDescentModels hc g).isPullback_toDescended hc⟩

omit [∀ i, QuasiSeparatedSpace (D.obj i)] in
lemma finitePresentationDescentIso_hom_comp :
    (finitePresentationDescentIso hc g).hom ≫ g = pullback.snd _ _ :=
  RelativeAffinePresentation.ChartModels.descendedIso_hom_comp _ _

end Selected

end AlgebraicGeometry
