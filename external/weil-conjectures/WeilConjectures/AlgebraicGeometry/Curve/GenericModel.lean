/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.FiniteMorphism
public import WeilConjectures.AlgebraicGeometry.Curve.GenericModelSpread
public import WeilConjectures.AlgebraicGeometry.GenericFiber.PurelyInseparableModel

/-!
# A generic curve model for a projective family of dimension at most one

Let `f : X ⟶ S` be projective with `S` integral of finite type over a field and geometric fibres
of dimension at most one. Over a nonempty open of `S` and after a finite surjective base change
`S' ⟶ S`, the reduced family `T = (X ×_S S')_red` is the target of a finite surjection
`ν : ∐ₐ Yₐ ⟶ T` from a finite disjoint union of smooth projective curve families and finite
étale families, which is an isomorphism outside a closed subscheme `D ⊆ T` finite over `S'`
(`proposition-proper-direct-image-finite-coefficients`). The construction normalizes the geometric
generic fibre and spreads the result out.

## Main statements

- `AlgebraicGeometry.exists_isFinite_sigmaDesc_genericCurveModel`
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- Generic curve model data transport along an isomorphism of the source. -/
lemma IsGenericCurveModelData.of_iso {F : Type u} [Field F] {X₁ X₂ : Scheme.{u}} (e : X₁ ≅ X₂)
    {g₂ : X₂ ⟶ Spec (.of F)} (h : IsGenericCurveModelData g₂) :
    IsGenericCurveModelData (e.hom ≫ g₂) := by
  obtain ⟨ι, _, Y, ν, d, W, hfin, hsm, hsurj, hci, hW⟩ := h
  have hσ : Sigma.desc (fun a ↦ ν a ≫ e.inv) = Sigma.desc ν ≫ e.inv := by
    ext
    simp
  refine ⟨ι, inferInstance, Y, fun a ↦ ν a ≫ e.inv, d, e.hom ⁻¹ᵁ W, fun a ↦ inferInstance,
    fun a ↦ ⟨(hsm a).1, by simpa using (hsm a).2⟩, by rw [hσ]; infer_instance, ?_, ?_⟩
  · rw [hσ, morphismRestrict_comp]
    have : IsClosedImmersion (Sigma.desc ν ∣_ (e.inv ⁻¹ᵁ (e.hom ⁻¹ᵁ W))) := by
      refine Scheme.Hom.restrict_of_le _ _ ?_ hci
      intro x hx
      have hx' : (e.inv ≫ e.hom) x ∈ W := hx
      simpa using hx'
    infer_instance
  · refine (hW.image e.inv).subset ?_
    intro x hx
    refine ⟨e.hom x, hx, ?_⟩
    rw [← Scheme.Hom.comp_apply, e.hom_inv_id]
    rfl

/-- Generic curve model transport along an isomorphism of the source. -/
lemma IsGenericCurveModel.of_iso {X₁ X₂ S : Scheme.{u}} (e : X₁ ≅ X₂) {F : X₂ ⟶ S}
    (h : IsGenericCurveModel F) : IsGenericCurveModel (e.hom ≫ F) := by
  obtain ⟨T, t, _, _, _, ι, _, Y, ν, _, _, D, d, _, hD, hiso, hY⟩ := h
  refine ⟨T, t ≫ e.inv, inferInstance, inferInstance, inferInstance, ι, inferInstance, Y, ν,
    inferInstance, inferInstance, D, d, inferInstance, ?_, hiso, fun a ↦ ?_⟩
  · simpa using hD
  · simpa using hY a

/-- Blueprint `proposition-proper-direct-image-finite-coefficients`: A generic curve model with
finite comparison boundary.

Let `S` be integral of finite type over a field `k`, `f : X ⟶ S` projective (`f = π ∘ i` for a
closed immersion `i : X ⟶ ℙ(n; S)`) with geometric fibres of dimension at most one. There are

* a nonempty open `U ⊆ S`, an integral scheme `S'` and a finite surjection `p : S' ⟶ U`;
* the reduced scheme `T = (X_U ×_U S')_red`, given with its surjective closed immersion
  `t : T ⟶ X_U ×_U S'`;
* finitely many schemes `Yₐ` over `S'` and a finite surjection `ν : ∐ₐ Yₐ ⟶ T`, each `Yₐ ⟶ S'`
  being either projective and smooth of relative dimension one, or finite étale;
* a closed subscheme `d : D ⟶ T`, finite over `S'`, outside of which `ν` is an isomorphism. -/
theorem exists_isFinite_sigmaDesc_genericCurveModel {k : Type u} [Field k] {X S : Scheme.{u}}
    [IsIntegral S] (aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS] [QuasiCompact aS]
    (f : X ⟶ S) {n : Type u} [Finite n] (i : X ⟶ ℙ(n; S)) [IsClosedImmersion i]
    (hi : i ≫ ℙ(n; S) ↘ S = f)
    (hf : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
      topologicalKrullDim (pullback f s : Scheme.{u}) ≤ 1) :
    ∃ (U : S.Opens) (_ : U ≠ ⊥) (S' : Scheme.{u}) (_ : IsIntegral S') (p : S' ⟶ U.toScheme)
      (_ : IsFinite p) (_ : Surjective p)
      (T : Scheme.{u}) (t : T ⟶ pullback (f ∣_ U) p) (_ : IsClosedImmersion t)
      (_ : Surjective t) (_ : IsReduced T)
      (ι : Type u) (_ : Finite ι) (Y : ι → Scheme.{u}) (ν : ∐ Y ⟶ T) (_ : IsFinite ν)
      (_ : Surjective ν) (D : Scheme.{u}) (d : D ⟶ T) (_ : IsClosedImmersion d),
      IsFinite (d ≫ t ≫ pullback.snd _ _) ∧
      IsIso (ν ∣_ ⟨(Set.range d.base)ᶜ, d.isClosedEmbedding.isClosed_range.isOpen_compl⟩) ∧
      ∀ a : ι,
        ((∃ (m : Type u) (_ : Finite m) (j : Y a ⟶ ℙ(m; S')), IsClosedImmersion j ∧
            j ≫ ℙ(m; S') ↘ S' = Sigma.ι Y a ≫ ν ≫ t ≫ pullback.snd _ _) ∧
          SmoothOfRelativeDimension 1 (Sigma.ι Y a ≫ ν ≫ t ≫ pullback.snd _ _)) ∨
        (IsFinite (Sigma.ι Y a ≫ ν ≫ t ≫ pullback.snd _ _) ∧
          Etale (Sigma.ι Y a ≫ ν ≫ t ≫ pullback.snd _ _)) := by
  classical
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian aS
  have : IsProper f := by
    subst hi
    infer_instance
  set η := S.fromSpecFunctionField
  -- the generic fibre has dimension at most one
  have hdim : topologicalKrullDim (pullback f η : Scheme.{u}) ≤ 1 := by
    let t : Spec (.of (AlgebraicClosure S.functionField)) ⟶ Spec S.functionField :=
      Spec.map (CommRingCat.ofHom (algebraMap S.functionField (AlgebraicClosure S.functionField)))
    have h1 := hf (AlgebraicClosure S.functionField) (t ≫ η)
    have e1 : topologicalKrullDim (pullback f (t ≫ η) : Scheme.{u}) =
        topologicalKrullDim (pullback (pullback.snd f η) t : Scheme.{u}) :=
      IsHomeomorph.topologicalKrullDim_eq _
        (Scheme.homeoOfIso (pullbackLeftPullbackSndIso f η t).symm).isHomeomorph
    rw [e1, topologicalKrullDim_pullback_eq_of_field (k := S.functionField)
      (pullback.snd f η) t] at h1
    exact h1
  -- a generic curve model datum after a purely inseparable extension `L`
  obtain ⟨L, _, _, _, _, YL, a, b, hpb, hdata⟩ :=
    exists_isPurelyInseparable_isGenericCurveModelData S.functionField (pullback.snd f η) hdim
  have hpb' := hpb.paste_horiz (IsPullback.of_hasPullback f η)
  -- a radicial model `Spec B ⟶ S` of `L` over a nonempty affine open of `S`
  obtain ⟨_, ⟨U₀, hU₀, rfl⟩, hη, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint S)) isOpen_univ
  have : Nonempty U₀ := ⟨⟨_, hη⟩⟩
  have : IsNoetherianRing Γ(S, U₀) := IsLocallyNoetherian.component_noetherian ⟨U₀, hU₀⟩
  let := TopCat.Presheaf.algebra_section_stalk S.presheaf (⟨genericPoint S, hη⟩ : U₀)
  have := functionField_isFractionRing_of_isAffineOpen S U₀ hU₀
  obtain ⟨c, hc, B, _, _, _, _, _, hfin, huh, hcomp⟩ :=
    exists_finite_isUniversalHomeomorphism_isFractionRing Γ(S, U₀) S.functionField L
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing (Localization.Away c) B
  let j : Spec (.of (Localization.Away c)) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U₀) _)) ≫ hU₀.fromSpec
  have : IsOpenImmersion j := by
    have : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U₀)
        (Localization.Away c)))) := IsOpenImmersion.of_isLocalization c
    infer_instance
  let π₀ : Spec (.of B) ⟶ Spec (.of (Localization.Away c)) :=
    Spec.map (CommRingCat.ofHom (algebraMap _ B))
  have : IsFinite π₀ := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr hfin
  have : IsUniversalHomeomorphism π₀ := huh.isUniversalHomeomorphism
  set σ := π₀ ≫ j
  have hσ : Spec.map (CommRingCat.ofHom (algebraMap B L)) ≫ σ =
      Spec.map (CommRingCat.ofHom (algebraMap S.functionField L)) ≫ η := by
    have hη' : η = hU₀.fromSpecStalk hη := (hU₀.fromSpecStalk_eq_fromSpecStalk hη).symm
    rw [hη', IsAffineOpen.fromSpecStalk]
    simp only [σ, j, π₀, ← Spec.map_comp_assoc]
    congr 2
    ext r
    exact hcomp r
  -- the model over `Spec B` and its generic fibre
  let fB := pullback.snd f σ
  let qL : Spec (.of L) ⟶ Spec (.of B) := Spec.map (CommRingCat.ofHom (algebraMap B L))
  have HB : IsPullback (pullback.fst fB qL ≫ pullback.fst f σ) (pullback.snd fB qL) f
      (Spec.map (CommRingCat.ofHom (algebraMap S.functionField L)) ≫ η) := by
    rw [← hσ]
    exact (IsPullback.of_hasPullback fB qL).paste_horiz (IsPullback.of_hasPullback f σ)
  have hdataB : IsGenericCurveModelData (pullback.snd fB qL) := by
    have := IsGenericCurveModelData.of_iso (hpb'.isoIsPullback _ _ HB).symm hdata
    rwa [Iso.symm_hom, IsPullback.isoIsPullback_inv_snd] at this
  -- spreading out over an affine open `S' ⊆ Spec B`
  obtain ⟨S', _, _, ρ, _, X', F', iX, hsq, hmodel⟩ :=
    exists_isGenericCurveModel_of_isFractionRing fB hdataB
  -- the open `U ⊆ S` and the finite surjection `p : S' ⟶ U`
  let τ := ρ ≫ σ
  have hπ₀ : IsHomeomorph π₀ := π₀.isHomeomorph
  have hσo : IsOpenMap σ := j.isOpenEmbedding.isOpenMap.comp hπ₀.isOpenMap
  have hσi : Function.Injective σ := j.isOpenEmbedding.injective.comp hπ₀.injective
  have hτo : IsOpenMap τ := hσo.comp ρ.isOpenEmbedding.isOpenMap
  have hτi : Function.Injective τ := hσi.comp ρ.isOpenEmbedding.injective
  let U : S.Opens := ⟨Set.range τ, hτo.isOpen_range⟩
  have hτU : Set.range τ ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    exact subset_rfl
  let p : S' ⟶ U.toScheme := IsOpenImmersion.lift U.ι τ hτU
  have hp : p ≫ U.ι = τ := IsOpenImmersion.lift_fac _ _ _
  have hτU' : τ ⁻¹ᵁ U = ⊤ := eq_top_iff.mpr fun x _ ↦ ⟨x, rfl⟩
  have : IsIso (τ ⁻¹ᵁ U).ι := by
    rw [isIso_iff_isOpenImmersion_and_surjective]
    refine ⟨inferInstance, ⟨fun x ↦ ⟨⟨x, hτU' ▸ trivial⟩, rfl⟩⟩⟩
  have hpι : (τ ⁻¹ᵁ U).ι ≫ p = τ ∣_ U := by
    rw [← cancel_mono U.ι, Category.assoc, hp, morphismRestrict_ι]
  have hσU : σ ⁻¹ᵁ U ≤ ρ.opensRange := by
    rintro x ⟨y, hy⟩
    exact ⟨y, hσi hy⟩
  have hjU : U ≤ j.opensRange := by
    rintro _ ⟨y, rfl⟩
    exact ⟨π₀ (ρ y), rfl⟩
  have := isIso_morphismRestrict_of_le_opensRange ρ hσU
  have := isIso_morphismRestrict_of_le_opensRange j hjU
  have hτres : τ ∣_ U = ρ ∣_ (σ ⁻¹ᵁ U) ≫ π₀ ∣_ (j ⁻¹ᵁ U) ≫ j ∣_ U := by
    rw [morphismRestrict_comp, morphismRestrict_comp]
  have : IsFinite (τ ∣_ U) := by
    rw [hτres]
    infer_instance
  have hpfin : IsFinite p := by
    have hp' : p = inv (τ ⁻¹ᵁ U).ι ≫ τ ∣_ U := by rw [← hpι, IsIso.inv_hom_id_assoc]
    rw [hp']
    infer_instance
  have hpsurj : Surjective p := by
    refine ⟨fun x ↦ ?_⟩
    obtain ⟨y, hy⟩ := x.2
    refine ⟨y, U.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hp]
    exact hy
  -- the generic curve model over `S'`
  have Hτ : IsPullback (iX ≫ pullback.fst f σ) F' f (p ≫ U.ι) := by
    rw [hp]
    exact hsq.paste_horiz (IsPullback.of_hasPullback f σ)
  obtain ⟨qq, hqq⟩ := isPullback_morphismRestrict_lift Hτ
  have hmodel' : IsGenericCurveModel (pullback.snd (f ∣_ U) p) := by
    have := IsGenericCurveModel.of_iso hqq.isoPullback.symm hmodel
    rwa [Iso.symm_hom, IsPullback.isoPullback_inv_snd] at this
  obtain ⟨T, t, htc, hts, hTr, ι, _, Y, ν, hνf, hνs, D, d, hdc, hD, hiso, hY⟩ := hmodel'
  -- a projective embedding of `(X_U) ×_U S'` over `S'`
  have HP : IsPullback (pullback.fst (f ∣_ U) p ≫ (f ⁻¹ᵁ U).ι) (pullback.snd (f ∣_ U) p)
      (i ≫ ℙ(n; S) ↘ S) (p ≫ U.ι) := by
    rw [hi]
    exact (IsPullback.of_hasPullback (f ∣_ U) p).paste_horiz (isPullback_morphismRestrict f U).flip
  have hw : pullback.snd (f ∣_ U) p ≫ (p ≫ U.ι) =
      ((pullback.fst (f ∣_ U) p ≫ (f ⁻¹ᵁ U).ι) ≫ i) ≫ ℙ(n; S) ↘ S := by
    rw [Category.assoc]
    exact HP.w.symm
  let i' := ProjectiveSpace.liftBaseChange (pullback.snd (f ∣_ U) p)
    ((pullback.fst (f ∣_ U) p ≫ (f ⁻¹ᵁ U).ι) ≫ i) hw
  have hi' : IsClosedImmersion i' :=
    MorphismProperty.of_isPullback (ProjectiveSpace.isPullback_liftBaseChange _ HP hw)
      inferInstance
  have hi'S : i' ≫ ℙ(n; S') ↘ S' = pullback.snd (f ∣_ U) p :=
    ProjectiveSpace.liftBaseChange_over _ _ _
  refine ⟨U, ?_, S', inferInstance, p, hpfin, hpsurj, T, t, htc, hts, hTr, ι, inferInstance, Y,
    ν, hνf, hνs, D, d, hdc, hD, hiso, fun a ↦ ?_⟩
  · obtain ⟨x⟩ : Nonempty S' := inferInstance
    intro hU
    have hx : τ x ∈ U := ⟨x, rfl⟩
    rw [hU] at hx
    exact hx
  · obtain ⟨hfa, h1 | h2⟩ := hY a
    · left
      have := hfa
      obtain ⟨m, hm, jj, hjj, hjjS⟩ := ProjectiveSpace.exists_isClosedImmersion_of_isFinite
        (t ≫ pullback.snd (f ∣_ U) p) (t ≫ i') (by rw [Category.assoc, hi'S])
        (Sigma.ι Y a ≫ ν)
      exact ⟨⟨m, hm, jj, hjj, by rw [hjjS]; simp⟩, h1⟩
    · right
      exact h2

end AlgebraicGeometry
