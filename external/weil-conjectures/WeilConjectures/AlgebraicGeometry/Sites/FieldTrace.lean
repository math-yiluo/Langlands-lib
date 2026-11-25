/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.GaloisCech
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.Section
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FiniteEtale

/-!
# The trace along a finite separable extension of fields

Let `K'/K` be a finite separable field extension of degree `d` and `f : Spec K' ⟶ Spec K`. Since
`f` is finite étale, the direct image `f_*` is left adjoint to the restriction `f^*`
(`AlgebraicGeometry.Etale.lowerStarLocalizationRestrictionAdjunction`); its counit is the *trace*
`f_* f^* M ⟶ M`. We show that the composite of the unit `M ⟶ f_* f^* M` of `f^* ⊣ f_*` with the
trace is multiplication by `d`.

On the spectrum `V = Spec E` of a field `E` over `K'` admitting `d` embeddings `τ : K' → E`, the
scheme `V ×_K Spec K'` is the disjoint union of the graphs `γ_τ` of the morphisms
`Spec τ : V ⟶ Spec K'`, and the pullback of a section `x` to it is the sum of the extensions by
zero of `x` off these graphs; the trace sends each of them to `x`. These `V` cover every étale
`K'`-scheme, and the general case follows by restriction.

## Main statements

- `AlgebraicGeometry.Scheme.FieldTrace.unit_comp_trace`: `M ⟶ f_* f^* M ⟶ M` is
  multiplication by `[K' : K]`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Module

/-- Every point of an étale `K`-scheme is hit by the spectrum of a finite separable field
extension of `K`. -/
lemma AlgebraicGeometry.Scheme.exists_etaleSpec_field_left_apply_eq {K : Type u} [Field K]
    (W : (Spec (.of K)).Etale) (w : W.left) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : Algebra.Etale K L)
      (g : etaleSpec K L ⟶ W) (y : (etaleSpec K L).left), g.left y = w := by
  let 𝒱 := W.left.affineOpenCover
  let k := 𝒱.idx w
  obtain ⟨z, hz⟩ : ∃ z : Spec (𝒱.X k), (𝒱.f k).base z = w := 𝒱.covers w
  have hc : Etale (𝒱.f k ≫ W.hom) := by
    have := W.prop
    infer_instance
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (𝒱.f k ≫ W.hom)
  rw [← hφ, HasRingHomProperty.Spec_iff (P := @Etale)] at hc
  algebraize [φ.hom]
  have : Module.Finite K (𝒱.X k) := Algebra.FormallyUnramified.finite_of_free K _
  have : IsArtinianRing (𝒱.X k) := IsArtinianRing.of_finite K _
  let m := (z : PrimeSpectrum (𝒱.X k)).asIdeal
  have : m.IsMaximal := IsArtinianRing.isMaximal_of_isPrime m
  let := Ideal.Quotient.field m
  have : Algebra.FormallyEtale K (𝒱.X k ⧸ m) := Algebra.FormallyEtale.of_isSeparable K _
  have : Algebra.Etale K (𝒱.X k ⧸ m) :=
    ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  let g : etaleSpec K (𝒱.X k ⧸ m) ⟶ W :=
    MorphismProperty.Over.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk m)) ≫ 𝒱.f k)
      (by
        change (_ ≫ _) ≫ W.hom = Spec.map _
        rw [Category.assoc, ← hφ, ← Spec.map_comp]
        rfl)
  let y : PrimeSpectrum (𝒱.X k ⧸ m) := ⟨⊥, Ideal.isPrime_bot⟩
  refine ⟨_, _, _, _, g, y, ?_⟩
  rw [← hz]
  change (𝒱.f k).base ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk m))).base y) = _
  congr 1
  apply PrimeSpectrum.ext
  ext a
  change a ∈ Ideal.comap (Ideal.Quotient.mk m) ⊥ ↔ _
  exact Ideal.Quotient.eq_zero_iff_mem (I := m)

namespace AlgebraicGeometry.Scheme.FieldTrace

open AlgebraicGeometry.Etale

variable (K : Type u) [Field K] (K' : Type u) [Field K'] [Algebra K K'] [Algebra.Etale K K']

/-- The morphism `Spec K' ⟶ Spec K`. -/
noncomputable abbrev f : Spec (.of K') ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K K'))

instance : AlgebraicGeometry.Etale (f K K') :=
  HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr inferInstance)

instance : IsFinite (f K K') := by
  have : Module.Finite K K' := Algebra.FormallyUnramified.finite_of_free K K'
  rw [IsFinite.SpecMap_iff]
  exact RingHom.finite_algebraMap.mpr inferInstance

instance : IsSeparated (f K K') := inferInstance

variable (M : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})

/-- The restriction `f^* M` along `f : Spec K' ⟶ Spec K`. -/
noncomputable abbrev res : Sheaf (Spec (.of K')).smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (Etale.localizationRestriction AddCommGrpCat.{u + 1} (f K K') inferInstance).obj M

/-- The unit `M ⟶ f_* f^* M` of `f^* ⊣ f_*`. -/
noncomputable def unit : M ⟶ (f K K')_*[AddCommGrpCat.{u + 1}].obj (res K K' M) :=
  (Etale.localizationRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} (f K K')
    inferInstance).unit.app M

/-- The trace `f_* f^* M ⟶ M`, the counit of `f_* ⊣ f^*`. -/
noncomputable def trace : (f K K')_*[AddCommGrpCat.{u + 1}].obj (res K K' M) ⟶ M :=
  (Etale.lowerStarLocalizationRestrictionAdjunction AddCommGrpCat.{u + 1} (f K K')).counit.app M

/-- The counit `W ×_K Spec K' ⟶ W` of the adjunction between `Over.map f` and base change. -/
noncomputable abbrev counitMor (W : (Spec (.of K)).Etale) :
    (MorphismProperty.Over.map ⊤ (inferInstance : AlgebraicGeometry.Etale (f K K'))).obj
      ((f K K').Etale.obj W) ⟶ W :=
  (MorphismProperty.Over.mapPullbackAdj @AlgebraicGeometry.Etale ⊤ (f K K') inferInstance
    _root_.trivial).counit.app W

lemma unit_app (W : (Spec (.of K)).Etale) :
    (unit K K' M).hom.app (op W) = M.obj.map (counitMor K K' W).op := by
  simp [unit, Etale.localizationRestrictionLowerStarAdjunction, counitMor]

section TestObject

variable (E : Type u) [Field E] [Algebra K' E] [Algebra K E] [IsScalarTower K K' E]
  [Algebra.Etale K' E]

/-- `Spec E` as an étale `K`-scheme, via `K'`. -/
noncomputable abbrev V : (Spec (.of K)).Etale :=
  (MorphismProperty.Over.map ⊤ (inferInstance : AlgebraicGeometry.Etale (f K K'))).obj
    (etaleSpec K' E)

/-- `V ×_K Spec K'`, as an étale `K`-scheme. -/
noncomputable abbrev Q : (Spec (.of K)).Etale :=
  (MorphismProperty.Over.map ⊤ (inferInstance : AlgebraicGeometry.Etale (f K K'))).obj
    ((f K K').Etale.obj (V K K' E))

lemma V_hom : (V K K' E).hom = Spec.map (CommRingCat.ofHom (algebraMap K E)) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

omit [Algebra.Etale K K'] [Algebra K' E] [IsScalarTower K K' E] [Algebra.Etale K' E] in
variable {K K' E} in
lemma specMap_comp_f (τ : K' →ₐ[K] E) :
    Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ f K K' =
      Spec.map (CommRingCat.ofHom (algebraMap K E)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x
  simp

variable {K K' E} in
/-- The graph `V ⟶ V ×_K Spec K'` of `Spec τ : V ⟶ Spec K'`. -/
noncomputable def γ (τ : K' →ₐ[K] E) : V K K' E ⟶ Q K K' E :=
  MorphismProperty.Over.homMk (pullback.lift (𝟙 _) (Spec.map (CommRingCat.ofHom τ.toRingHom))
    (by rw [Category.id_comp, V_hom, specMap_comp_f])) (by
      change pullback.lift _ _ _ ≫ pullback.snd _ _ ≫ f K K' = _
      rw [pullback.lift_snd_assoc, specMap_comp_f, V_hom]) _root_.trivial

variable {K K' E} in
@[reassoc (attr := simp)]
lemma γ_left_fst (τ : K' →ₐ[K] E) :
    (γ τ).left ≫ pullback.fst (V K K' E).hom (f K K') = 𝟙 _ :=
  pullback.lift_fst _ _ _

variable {K K' E} in
@[reassoc (attr := simp)]
lemma γ_left_snd (τ : K' →ₐ[K] E) :
    (γ τ).left ≫ pullback.snd (V K K' E).hom (f K K') =
      Spec.map (CommRingCat.ofHom τ.toRingHom) :=
  pullback.lift_snd _ _ _

variable {K K' E} in
lemma γ_comp_counitMor (τ : K' →ₐ[K] E) : γ τ ≫ counitMor K K' (V K K' E) = 𝟙 _ :=
  MorphismProperty.Over.Hom.ext (γ_left_fst τ)

variable {K K' E} in
lemma isOpenImmersion_γ_left (τ : K' →ₐ[K] E) : IsOpenImmersion (γ τ).left := by
  have : AlgebraicGeometry.Etale (pullback.fst (V K K' E).hom (f K K')) := inferInstance
  exact IsOpenImmersion.of_section_of_etale (pullback.fst (V K K' E).hom (f K K')) _
    (γ_left_fst τ)

variable {K K' E} in
/-- Two graphs meeting at a point coincide. -/
lemma eq_of_γ_left_apply_eq {σ τ : K' →ₐ[K] E} (a b : (V K K' E).left)
    (h : (γ σ).left a = (γ τ).left b) : σ = τ := by
  have := isOpenImmersion_γ_left σ
  have := isOpenImmersion_γ_left τ
  have hsub : Set.range (γ σ).left ⊆ Set.range (γ τ).left := by
    rintro _ ⟨c, rfl⟩
    refine ⟨b, ?_⟩
    have hc : c = a := @Subsingleton.elim (Spec (.of E)) _ _ _
    rw [hc, h]
  have hl := IsOpenImmersion.lift_fac (γ τ).left (γ σ).left hsub
  have h1 : IsOpenImmersion.lift (γ τ).left (γ σ).left hsub = 𝟙 _ := by
    have := congrArg (· ≫ pullback.fst (V K K' E).hom (f K K')) hl
    simp only [Category.assoc, γ_left_fst, Category.comp_id] at this
    exact this
  rw [h1, Category.id_comp] at hl
  have h2 := congrArg (· ≫ pullback.snd (V K K' E).hom (f K K')) hl
  simp only [γ_left_snd] at h2
  have h3 := Spec.map_injective h2
  ext x
  exact congrArg (fun φ ↦ φ.hom x) h3.symm

variable {K K' E} in
/-- **The graphs cover `V ×_K Spec K'`** when `E` has `[K' : K]` embeddings of `K'`: a point
`z` with residue field `κ` gives embeddings `E → κ` and `K' → κ`, and the latter is one of the
`[K' : K]` composites of `E → κ` with an embedding `K' → E`, as `K'` has at most `[K' : K]`
embeddings into `κ`. -/
lemma iUnion_range_γ_left (hcard : Nat.card (K' →ₐ[K] E) = finrank K K') :
    ⋃ τ : K' →ₐ[K] E, Set.range (γ τ).left = Set.univ := by
  have : Module.Finite K K' := Algebra.FormallyUnramified.finite_of_free K K'
  refine Set.eq_univ_of_forall fun z ↦ ?_
  let κ := (Q K K' E).left.residueField z
  let p := (Q K K' E).left.fromSpecResidueField z
  let c : Γ(Spec κ, ⊤) →+* κ := (Scheme.ΓSpecIso κ).hom.hom
  let x₁ : Spec κ ⟶ Spec (.of E) := p ≫ pullback.fst (V K K' E).hom (f K K')
  let x₂ : Spec κ ⟶ Spec (.of K') := p ≫ pullback.snd (V K K' E).hom (f K K')
  let ι₁ : E →+* κ := c.comp (GaloisCech.toRing x₁)
  let ι₂ : K' →+* κ := c.comp (GaloisCech.toRing x₂)
  have hcomm : ι₂.comp (algebraMap K K') = ι₁.comp (algebraMap K E) := by
    have h : (x₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap K' E))) ≫ f K K' =
        x₂ ≫ f K K' := by
      simp only [x₁, x₂, Category.assoc]
      exact congrArg (p ≫ ·) pullback.condition
    have h' := congrArg (fun φ ↦ GaloisCech.toRing φ) h
    simp only [GaloisCech.toRing_comp_specMap] at h'
    ext x
    have := congrArg (fun φ : K →+* _ ↦ c (φ x)) h'
    simp only [RingHom.comp_apply] at this
    simp only [ι₁, ι₂, RingHom.comp_apply, IsScalarTower.algebraMap_apply K K' E]
    exact this.symm
  let : Algebra K κ := (ι₁.comp (algebraMap K E)).toAlgebra
  let ι₁' : E →ₐ[K] κ := { ι₁ with commutes' := fun c ↦ rfl }
  let ι₂' : K' →ₐ[K] κ :=
    { ι₂ with commutes' := fun c ↦ congrArg (fun φ : K →+* κ ↦ φ c) hcomm }
  have hinj : Function.Injective fun σ : K' →ₐ[K] E ↦ ι₁'.comp σ := by
    intro σ τ hστ
    ext x
    exact ι₁.injective (DFunLike.congr_fun hστ x)
  have hbij := hinj.bijective_of_nat_card_le
    ((card_algHom_le_finrank K K' κ).trans hcard.ge)
  obtain ⟨σ, hσ⟩ := hbij.2 ι₂'
  have hσ' : (GaloisCech.toRing (p ≫ pullback.fst (V K K' E).hom (f K K'))).comp
      σ.toRingHom = GaloisCech.toRing (p ≫ pullback.snd (V K K' E).hom (f K K')) := by
    ext x
    have := DFunLike.congr_fun hσ x
    exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso κ).hom).1 this
  have hp : p = (p ≫ pullback.fst (V K K' E).hom (f K K')) ≫ (γ σ).left := by
    apply pullback.hom_ext
    · simp only [Category.assoc, γ_left_fst]
      erw [Category.comp_id]
    · rw [Category.assoc, γ_left_snd]
      refine (GaloisCech.eq_of_toRing_eq ?_).symm
      rw [GaloisCech.toRing_comp_specMap]
      exact hσ'
  refine Set.mem_iUnion.2 ⟨σ, (p ≫ pullback.fst _ _) (IsLocalRing.closedPoint κ), ?_⟩
  have h2 := congrArg (fun φ : Spec κ ⟶ _ ↦ φ (IsLocalRing.closedPoint κ)) hp
  simp only [Scheme.Hom.comp_apply] at h2 ⊢
  exact h2.symm.trans ((Q K K' E).left.fromSpecResidueField_apply z _)

variable {K K' E} in
/-- `Spec E` as an étale `K'`-scheme via `τ : K' → E`. -/
noncomputable def Uτ (τ : K' →ₐ[K] E) : (Spec (.of K')).Etale :=
  MorphismProperty.Over.mk ⊤ (Spec.map (CommRingCat.ofHom τ.toRingHom)) (by
    have : AlgebraicGeometry.Etale (Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ f K K') := by
      rw [specMap_comp_f]
      exact HasRingHomProperty.Spec_iff.mpr
        (RingHom.etale_algebraMap.mpr (Algebra.Etale.comp K K' E))
    exact AlgebraicGeometry.Etale.of_comp _ (f K K'))

variable {K K' E} in
/-- `Spec E` as an étale `K`-scheme, via `τ`. -/
noncomputable abbrev Vτ (τ : K' →ₐ[K] E) : (Spec (.of K)).Etale :=
  (MorphismProperty.Over.map ⊤ (inferInstance : AlgebraicGeometry.Etale (f K K'))).obj (Uτ τ)

variable {K K' E} in
/-- The identification of the two structures of étale `K`-scheme on `Spec E`. -/
noncomputable def eτ (τ : K' →ₐ[K] E) : Vτ τ ≅ V K K' E :=
  MorphismProperty.Over.isoMk (Iso.refl (Spec (.of E)))
    ((Category.id_comp _).trans ((V_hom K K' E).trans (specMap_comp_f τ).symm))

variable {K K' E} in
/-- The base change of `eτ⁻¹`, from `V ×_K Spec K'` to `Vτ ×_K Spec K'`. -/
noncomputable abbrev φτ (τ : K' →ₐ[K] E) :
    Q K K' E ⟶ (MorphismProperty.Over.map ⊤ (inferInstance : AlgebraicGeometry.Etale (f K K'))).obj
      ((f K K').Etale.obj (Vτ τ)) :=
  (MorphismProperty.Over.map ⊤ (inferInstance : AlgebraicGeometry.Etale (f K K'))).map
    ((f K K').Etale.map (eτ τ).inv)

variable {K K' E} in
lemma γ_comp_φτ (τ : K' →ₐ[K] E) :
    γ τ ≫ φτ τ = (eτ τ).inv ≫
      (MorphismProperty.Over.map ⊤ (inferInstance : AlgebraicGeometry.Etale (f K K'))).map
        (Etale.graph (f K K') (Uτ τ)) := by
  apply MorphismProperty.Over.Hom.ext
  rw [MorphismProperty.Comma.comp_left, MorphismProperty.Comma.comp_left]
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc]
    have h1 := Hom.etale_map_left_comp_fst (f K K') (eτ τ).inv
    have h2 := Etale.graph_left_fst (f K K') (Uτ τ)
    have h3 := γ_left_fst τ
    exact ((congrArg ((γ τ).left ≫ ·) h1).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (eτ τ).inv.left) h3).trans (Category.id_comp _)))).trans
      ((congrArg ((eτ τ).inv.left ≫ ·) h2).trans (Category.comp_id _)).symm
  · rw [Category.assoc, Category.assoc]
    have h1 := Hom.etale_map_left_comp_snd (f K K') (eτ τ).inv
    have h2 := Etale.graph_left_snd (f K K') (Uτ τ)
    have h3 := γ_left_snd τ
    exact ((congrArg ((γ τ).left ≫ ·) h1).trans h3).trans
      ((congrArg ((eτ τ).inv.left ≫ ·) h2).trans (Category.id_comp _)).symm

variable {K K' E} in
lemma γ_comp_φτ_left_apply (τ : K' →ₐ[K] E) (a : (V K K' E).left) :
    (φτ τ).left ((γ τ).left a) = (Etale.graph (f K K') (Uτ τ)).left ((eτ τ).inv.left a) := by
  exact congrArg (fun φ ↦ φ.left a) (γ_comp_φτ τ)

variable {K K' E} in
/-- The graph `γ σ` misses the graph of `Uτ` for `σ ≠ τ`. -/
lemma γ_comp_φτ_left_mem_graphCompl {σ τ : K' →ₐ[K] E} (hστ : σ ≠ τ) (a : (V K K' E).left) :
    (φτ τ).left ((γ σ).left a) ∈ Etale.graphCompl (f K K') (Uτ τ) := by
  rintro ⟨b, hb⟩
  have hinj : Function.Injective (φτ τ).left := by
    let ψ := (MorphismProperty.Over.map ⊤ (inferInstance : AlgebraicGeometry.Etale (f K K'))).map
      ((f K K').Etale.map (eτ τ).hom)
    have hψ : φτ τ ≫ ψ = 𝟙 _ := by
      simp only [φτ, ψ, ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]
    intro a b hab
    have ha : ψ.left ((φτ τ).left a) = a := congrArg (fun φ : Q K K' E ⟶ _ ↦ φ.left a) hψ
    have hb : ψ.left ((φτ τ).left b) = b := congrArg (fun φ : Q K K' E ⟶ _ ↦ φ.left b) hψ
    exact ha.symm.trans ((congrArg ψ.left hab).trans hb)
  have hb' : (Etale.graph (f K K') (Uτ τ)).left b =
      (φτ τ).left ((γ τ).left b) := by
    rw [γ_comp_φτ_left_apply]
    rfl
  rw [hb'] at hb
  exact hστ (eq_of_γ_left_apply_eq a b (hinj hb.symm))

variable {K K' E} in
/-- The extension by zero of `x ∈ M(Spec E)` off the graph of `Spec τ`, as a section of `M`
over `V ×_K Spec K'`. -/
noncomputable def ext (τ : K' →ₐ[K] E) (x : M.obj.obj (op (V K K' E))) :
    M.obj.obj (op (Q K K' E)) :=
  M.obj.map (φτ τ).op ((Etale.graphExtend (f K K') (res K K' M) (Uτ τ)).hom
    (M.obj.map (eτ τ).hom.op x))

omit [Algebra.Etale K K'] in
lemma map_map_apply {C : Type*} [Category C] (F : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}) {X Y Z : C}
    (a : X ⟶ Y) (b : Y ⟶ Z) (x : F.obj (op Z)) :
    F.map a.op (F.map b.op x) = F.map (a ≫ b).op x := by
  rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

omit [Algebra.Etale K K'] in
/-- A section vanishing on an open subscheme vanishes on everything mapping into it. -/
lemma map_eq_zero_of_range_subset {W T O : (Spec (.of K)).Etale} (i : O ⟶ T)
    (hi : IsOpenImmersion i.left) (h : W ⟶ T) (hr : Set.range h.left ⊆ Set.range i.left)
    (s : M.obj.obj (op T)) (hs : M.obj.map i.op s = 0) : M.obj.map h.op s = 0 := by
  have := hi
  let ζ : W ⟶ O := MorphismProperty.Over.homMk (IsOpenImmersion.lift i.left h.left hr) (by
    rw [← MorphismProperty.Over.w i, ← Category.assoc, IsOpenImmersion.lift_fac]
    exact MorphismProperty.Over.w h) _root_.trivial
  have hζ : ζ ≫ i = h := MorphismProperty.Over.Hom.ext (IsOpenImmersion.lift_fac _ _ _)
  rw [← hζ, ← map_map_apply, hs, map_zero]

variable {K K' E} in
lemma map_γ_ext_self (τ : K' →ₐ[K] E) (x : M.obj.obj (op (V K K' E))) :
    M.obj.map (γ τ).op (ext M τ x) = x := by
  have h := congrArg (fun φ : V K K' E ⟶ _ ↦ M.obj.map φ.op
    ((Etale.graphExtend (f K K') (res K K' M) (Uτ τ)).hom (M.obj.map (eτ τ).hom.op x)))
    (γ_comp_φτ τ)
  refine (map_map_apply M.obj _ _ _).trans (h.trans ?_)
  refine (map_map_apply M.obj _ _ _).symm.trans ?_
  have hg := ConcreteCategory.congr_hom
    (Etale.graphExtend_graph (f K K') (res K K' M) (Uτ τ)) (M.obj.map (eτ τ).hom.op x)
  refine (congrArg (M.obj.map (eτ τ).inv.op) hg).trans ?_
  refine (map_map_apply M.obj _ _ _).trans ?_
  rw [Iso.inv_hom_id, op_id, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]

variable {K K' E} in
lemma map_γ_ext_of_ne {σ τ : K' →ₐ[K] E} (hστ : σ ≠ τ) (x : M.obj.obj (op (V K K' E))) :
    M.obj.map (γ σ).op (ext M τ x) = 0 := by
  refine (map_map_apply M.obj _ _ _).trans (map_eq_zero_of_range_subset K M
    ((MorphismProperty.Over.map ⊤ (inferInstance : AlgebraicGeometry.Etale (f K K'))).map
      (Etale.graphComplι (f K K') (Uτ τ)))
      (inferInstanceAs (IsOpenImmersion (Etale.graphCompl (f K K') (Uτ τ)).ι)) (γ σ ≫ φτ τ) ?_ _ ?_)
  · rintro _ ⟨a, rfl⟩
    change _ ∈ Set.range (Etale.graphCompl (f K K') (Uτ τ)).ι
    rw [Scheme.Opens.range_ι]
    exact γ_comp_φτ_left_mem_graphCompl hστ a
  · exact ConcreteCategory.congr_hom
      (Etale.graphExtend_graphComplι (f K K') (res K K' M) (Uτ τ)) (M.obj.map (eτ τ).hom.op x)

variable {K K' E} in
lemma trace_ext (τ : K' →ₐ[K] E) (x : M.obj.obj (op (V K K' E))) :
    (trace K K' M).hom.app (op (V K K' E)) (ext M τ x) = x := by
  have hnat := NatTrans.naturality_apply (trace K K' M).hom (eτ τ).inv.op
    ((Etale.graphExtend (f K K') (res K K' M) (Uτ τ)).hom (M.obj.map (eτ τ).hom.op x))
  refine hnat.trans ?_
  have htri := congrArg (fun φ ↦ (φ.hom.app (op (Uτ τ))).hom (M.obj.map (eτ τ).hom.op x))
    ((Etale.lowerStarLocalizationRestrictionAdjunction AddCommGrpCat.{u + 1}
      (f K K')).right_triangle_components M)
  simp only [Etale.lowerStarLocalizationRestrictionAdjunction_unit] at htri
  refine (congrArg (M.obj.map (eτ τ).inv.op) htri).trans ?_
  refine (map_map_apply M.obj _ _ _).trans ?_
  rw [Iso.inv_hom_id, op_id, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]

variable {K K' E} in
/-- **The trace on a test object.** -/
theorem trace_unit_apply (hcard : Nat.card (K' →ₐ[K] E) = finrank K K')
    (x : M.obj.obj (op (V K K' E))) :
    (trace K K' M).hom.app (op (V K K' E)) ((unit K K' M).hom.app (op (V K K' E)) x) =
      (finrank K K' : ℤ) • x := by
  classical
  have : Module.Finite K K' := Algebra.FormallyUnramified.finite_of_free K K'
  have : Fintype (K' →ₐ[K] E) := Fintype.ofFinite _
  have hsum : (unit K K' M).hom.app (op (V K K' E)) x = ∑ τ, ext M τ x := by
    refine (isSheafFor_ofArrows M (fun τ : K' →ₐ[K] E ↦ γ τ)
      (iUnion_range_γ_left hcard)).isSeparatedFor.ext fun Z g ⟨σ⟩ ↦ ?_
    change M.obj.map (γ σ).op _ = M.obj.map (γ σ).op _
    rw [map_sum, Finset.sum_eq_single σ (fun τ _ hτ ↦ map_γ_ext_of_ne M (Ne.symm hτ) x)
        (by simp), map_γ_ext_self, unit_app]
    refine (map_map_apply M.obj _ _ _).trans ?_
    rw [γ_comp_counitMor, op_id, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]
  rw [hsum, map_sum]
  simp only [trace_ext, Finset.sum_const, Finset.card_univ]
  rw [← Nat.card_eq_fintype_card, hcard, natCast_zsmul]

end TestObject


/-- Every finite separable extension `L / K` embeds into a finite separable extension `E / K`
receiving `[K' : K]` distinct `K`-embeddings of `K'`. -/
lemma exists_testObject (L : Type u) [Field L] [Algebra K L] [Algebra.Etale K L] :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra K' E) (_ : Algebra K E)
      (_ : IsScalarTower K K' E) (_ : Algebra.Etale K' E) (_ : Algebra.Etale K E)
      (_ : L →ₐ[K] E), Nat.card (K' →ₐ[K] E) = finrank K K' := by
  have : Module.Finite K L := Algebra.FormallyUnramified.finite_of_free K L
  have : Algebra.IsSeparable K L := Algebra.FormallyUnramified.isSeparable K L
  have : Module.Finite K K' := Algebra.FormallyUnramified.finite_of_free K K'
  have : Algebra.IsSeparable K K' := Algebra.FormallyUnramified.isSeparable K K'
  let F := SeparableClosure L
  have : Algebra.IsSeparable K F := Algebra.IsSeparable.trans K L F
  have : IsSepClosed F := inferInstance
  let E : IntermediateField K F :=
    (IsScalarTower.toAlgHom K L F).fieldRange ⊔ IntermediateField.normalClosure K K' F
  have hE : IntermediateField.normalClosure K K' F ≤ E := le_sup_right
  let ι₀ : K' →ₐ[K] F := IsSepClosed.lift
  let ι : K' →ₐ[K] E := ι₀.codRestrict E.toSubalgebra fun x ↦
    hE (ι₀.fieldRange_le_normalClosure ⟨x, rfl⟩)
  have : FiniteDimensional K (IsScalarTower.toAlgHom K L F).fieldRange :=
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom K L F)).toLinearEquiv.finiteDimensional
  let : Algebra K' E := ι.toRingHom.toAlgebra
  have : IsScalarTower K K' E := IsScalarTower.of_algebraMap_eq fun x ↦ (ι.commutes x).symm
  have : FiniteDimensional K E := IntermediateField.finiteDimensional_sup _ _
  have : Algebra.IsSeparable K E := Algebra.isSeparable_tower_bot_of_isSeparable K E F
  have : Algebra.FormallyEtale K E := Algebra.FormallyEtale.of_isSeparable K E
  have : Algebra.Etale K E :=
    ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  have : Module.Finite K' E := Module.Finite.of_restrictScalars_finite K K' E
  have : Algebra.IsSeparable K' E := Algebra.isSeparable_tower_top_of_isSeparable K K' E
  have : Algebra.FormallyEtale K' E := Algebra.FormallyEtale.of_isSeparable K' E
  have : Algebra.Etale K' E :=
    ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  refine ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, (IsScalarTower.toAlgHom K L F).codRestrict E.toSubalgebra fun x ↦
      le_sup_left (a := (IsScalarTower.toAlgHom K L F).fieldRange) ⟨x, rfl⟩, ?_⟩
  have hbij : Function.Bijective fun τ : K' →ₐ[K] E ↦ E.val.comp τ := by
    refine ⟨fun σ τ h ↦ AlgHom.ext fun x ↦ Subtype.ext (AlgHom.congr_fun h x), fun τ ↦
      ⟨τ.codRestrict E.toSubalgebra fun x ↦ hE (τ.fieldRange_le_normalClosure ⟨x, rfl⟩), ?_⟩⟩
    ext
    rfl
  rw [Nat.card_eq_of_bijective _ hbij]
  exact AlgHom.natCard_of_splits K K' F fun x ↦
    IsSepClosed.splits_codomain _ (Algebra.IsSeparable.isSeparable K x)



/-- A morphism `Spec E ⟶ W` from a test object: `E` is a finite separable extension of `K'`
receiving `[K' : K]` distinct `K`-embeddings of `K'`. -/
structure TestCover (W : (Spec (.of K)).Etale) where
  /-- The field. -/
  E : Type u
  [field : Field E]
  [algebra' : Algebra K' E]
  [algebra : Algebra K E]
  [isScalarTower : IsScalarTower K K' E]
  [etale' : Algebra.Etale K' E]
  /-- The morphism to `W`. -/
  g : V K K' E ⟶ W
  card_eq : Nat.card (K' →ₐ[K] E) = finrank K K'

attribute [instance] TestCover.field TestCover.algebra' TestCover.algebra
  TestCover.isScalarTower TestCover.etale'

lemma iUnion_range_testCover (W : (Spec (.of K)).Etale) :
    ⋃ a : TestCover K K' W, Set.range a.g.left = Set.univ := by
  refine Set.eq_univ_of_forall fun w ↦ Set.mem_iUnion.2 ?_
  obtain ⟨L, _, _, _, g, y, hy⟩ := exists_etaleSpec_field_left_apply_eq W w
  obtain ⟨E, _, _, _, _, _, _, φ, hcard⟩ := exists_testObject K K' L
  let h : V K K' E ⟶ etaleSpec K L :=
    MorphismProperty.Over.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom)) (by
      rw [V_hom]
      change Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp]
      congr 1
      ext x
      exact φ.commutes x)
  obtain ⟨z⟩ : Nonempty (Spec (.of E)) := inferInstance
  refine ⟨⟨E, h ≫ g, hcard⟩, z, ?_⟩
  rw [← hy]
  change g.left (h.left z) = _
  congr 1
  exact Subsingleton.elim (α := Spec (.of L)) _ _

/-- **The trace along a finite separable extension.** The composite `M ⟶ f_* f^* M ⟶ M` of the
unit and the trace is multiplication by `[K' : K]`. -/
theorem unit_comp_trace : unit K K' M ≫ trace K K' M = (finrank K K' : ℤ) • 𝟙 M := by
  apply Sheaf.hom_ext
  ext W x
  refine (isSheafFor_ofArrows M (fun a : TestCover K K' W.unop ↦ a.g)
    (iUnion_range_testCover K K' W.unop)).isSeparatedFor.ext fun Z g ⟨a⟩ ↦ ?_
  change M.obj.map a.g.op _ = M.obj.map a.g.op _
  have hd : ((finrank K K' : ℤ) • 𝟙 M).hom.app W x = (finrank K K' : ℤ) • x := by
    have := (sheafToPresheaf _ AddCommGrpCat.{u + 1}).map_zsmul (f := 𝟙 M)
      (r := (finrank K K' : ℤ))
    simp_all
  change _ = M.obj.map a.g.op (((finrank K K' : ℤ) • 𝟙 M).hom.app W x)
  rw [hd]
  change M.obj.map a.g.op ((trace K K' M).hom.app W ((unit K K' M).hom.app W x)) = _
  rw [← NatTrans.naturality_apply (trace K K' M).hom,
    ← NatTrans.naturality_apply (unit K K' M).hom, trace_unit_apply M a.card_eq, map_zsmul]

end AlgebraicGeometry.Scheme.FieldTrace
