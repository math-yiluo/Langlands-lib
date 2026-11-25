/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.FieldDevissage
public import WeilConjectures.CategoryTheory.DerivedCategory.FieldExtensionHom
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatExtendScalarsComp
public import WeilConjectures.CategoryTheory.FilteredTwoColimit
public import WeilConjectures.CategoryTheory.RingObjects.EllAdic

/-!
# `Dᵇ_fd(ℚ̄_ℓ)` as the 2-colimit of the `Dᵇ_fd(E)`

Let `E` run over the finite subextensions `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`
(`PadicAlgCl.FiniteIntermediateField ℓ`). Blueprint `lemma-perfect-complexes-geometric-point`
defines `Dᵇ_fd(ℚ̄_ℓ) := 2-colim_E Dᵇ_fd(E)`, with transition functors `- ⊗_E F`. This file shows
that the bounded derived category of finite-dimensional `ℚ̄_ℓ`-vector spaces, with the extensions of
scalars `- ⊗_E ℚ̄_ℓ`, *is* this filtered 2-colimit (`PadicAlgCl.fdCocone_isFilteredTwoColimit`,
in the sense of `CategoryTheory.CategoryCocone.IsFilteredTwoColimit`):

* morphisms descend to a finite stage: for `X`, `Y` in `Dᵇ_fd(E)`,
  `Hom(X_{ℚ̄_ℓ}, Y_{ℚ̄_ℓ}) = ℚ̄_ℓ ⊗_E Hom(X, Y)` (`ModuleCat.tensorBijective_fieldExtendScalars`),
  and the finitely many coefficients of a morphism lie in a finite subextension;
* extension of scalars along a field extension is faithful on `Dᵇ_fd`;
* objects descend, by dévissage: the objects of `Dᵇ_fd(ℚ̄_ℓ)` coming from a finite stage form a
  triangulated subcategory, since morphisms descend, containing `ℚ̄_ℓ[0]`.

The fields are represented by their universe `u + 1` copies `ULift E`, so that the ring maps
between the stages compose definitionally; the transitivity isomorphisms of the extensions of
scalars are `ModuleCat.derivedExtendScalarsComp`, whose coherence
`ModuleCat.derivedExtendScalarsComp_assoc` is used to compare stages.
-/

@[expose] public section

universe u

open CategoryTheory Limits DerivedCategory Pretriangulated

namespace PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- Any ring morphism between fields is flat. -/
lemma flat_of_field {K L : Type*} [Field K] [CommRing L] (f : K →+* L) : f.Flat := by
  let := f.toAlgebra
  change Module.Flat K L
  infer_instance

/-- The ring map `E ⟶ F` between the universe `u + 1` copies of finite subextensions
`E ≤ F` of `ℚ̄_ℓ`. -/
noncomputable def stageMap {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    ULift.{u + 1} E.1 →+* ULift.{u + 1} F.1 :=
  ULift.ringEquiv.symm.toRingHom.comp
    ((IntermediateField.inclusion (show E.1 ≤ F.1 from h)).toRingHom.comp
      ULift.ringEquiv.toRingHom)

/-- The ring map `E ⟶ ℚ̄_ℓ` between universe `u + 1` copies. -/
noncomputable def toAlgCl (E : FiniteIntermediateField ℓ) :
    ULift.{u + 1} E.1 →+* ULift.{u + 1} (PadicAlgCl ℓ) :=
  ULift.ringEquiv.symm.toRingHom.comp (E.1.val.toRingHom.comp ULift.ringEquiv.toRingHom)

lemma toAlgCl_comp_stageMap {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    (toAlgCl.{u} ℓ F).comp (stageMap ℓ h) = toAlgCl ℓ E := rfl

lemma stageMap_comp_stageMap {E F G : FiniteIntermediateField ℓ} (h : E ≤ F) (h' : F ≤ G) :
    (stageMap.{u} ℓ h').comp (stageMap ℓ h) = stageMap ℓ (h.trans h') := rfl

/-- `Dᵇ_fd(E)`, for the universe `u + 1` copy of `E`. -/
abbrev FdStage (E : FiniteIntermediateField ℓ) : Type _ :=
  BoundedFiniteCohomology (ULift.{u + 1} E.1)

/-- `Dᵇ_fd(ℚ̄_ℓ)`, for the universe `u + 1` copy of `ℚ̄_ℓ`. -/
abbrev FdAlgCl : Type _ :=
  BoundedFiniteCohomology (ULift.{u + 1} (PadicAlgCl ℓ))

/-- The derived extension of scalars `D(E) ⥤ D(F)` for `E ≤ F`. -/
noncomputable def stageDerived {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} E.1)) ⥤
      DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} F.1)) :=
  ModuleCat.derivedExtendScalars (stageMap ℓ h) (flat_of_field _)

/-- The derived extension of scalars `D(E) ⥤ D(ℚ̄_ℓ)`. -/
noncomputable def algClDerived (E : FiniteIntermediateField ℓ) :
    DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} E.1)) ⥤
      DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl ℓ))) :=
  ModuleCat.derivedExtendScalars (toAlgCl ℓ E) (flat_of_field _)

noncomputable instance {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    (stageDerived.{u} ℓ h).CommShift ℤ := by
  unfold stageDerived; infer_instance

instance {E F : FiniteIntermediateField ℓ} (h : E ≤ F) : (stageDerived.{u} ℓ h).IsTriangulated := by
  unfold stageDerived; infer_instance

noncomputable instance (E : FiniteIntermediateField ℓ) : (algClDerived.{u} ℓ E).CommShift ℤ := by
  unfold algClDerived; infer_instance

instance (E : FiniteIntermediateField ℓ) : (algClDerived.{u} ℓ E).IsTriangulated := by
  unfold algClDerived; infer_instance

instance (E : FiniteIntermediateField ℓ) : (algClDerived.{u} ℓ E).Additive := by
  unfold algClDerived; infer_instance

/-- The transitivity isomorphism `- ⊗_E ℚ̄_ℓ ≅ (- ⊗_E F) ⊗_F ℚ̄_ℓ`. -/
noncomputable def stageCompIso {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    algClDerived.{u} ℓ E ≅ stageDerived ℓ h ⋙ algClDerived ℓ F :=
  ModuleCat.derivedExtendScalarsComp (stageMap ℓ h) (toAlgCl ℓ F) (flat_of_field _)
    (flat_of_field _) (flat_of_field _)

/-- The transitivity isomorphism `- ⊗_E G ≅ (- ⊗_E F) ⊗_F G`. -/
noncomputable def stageStageIso {E F G : FiniteIntermediateField ℓ} (h : E ≤ F) (h' : F ≤ G) :
    stageDerived.{u} ℓ (h.trans h') ≅ stageDerived ℓ h ⋙ stageDerived ℓ h' :=
  ModuleCat.derivedExtendScalarsComp (stageMap ℓ h) (stageMap ℓ h') (flat_of_field _)
    (flat_of_field _) (flat_of_field _)

/-- The coherence of the transitivity isomorphisms along `E ≤ F ≤ G`. -/
lemma stageCompIso_assoc {E F G : FiniteIntermediateField ℓ} (h : E ≤ F) (h' : F ≤ G)
    (X : DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} E.1))) :
    (stageCompIso ℓ h).hom.app X ≫ (stageCompIso ℓ h').hom.app ((stageDerived ℓ h).obj X) =
      (stageCompIso ℓ (h.trans h')).hom.app X ≫
        (algClDerived ℓ G).map ((stageStageIso ℓ h h').hom.app X) :=
  ModuleCat.derivedExtendScalarsComp_assoc (stageMap ℓ h) (stageMap ℓ h') (toAlgCl ℓ G)
    (flat_of_field _) (flat_of_field _) (flat_of_field _) (flat_of_field _) (flat_of_field _)
    (flat_of_field _) X

lemma algClDerived_map_smul (E : FiniteIntermediateField ℓ) (r : ULift.{u + 1} E.1)
    {X Y : DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} E.1))} (φ : X ⟶ Y) :
    (algClDerived ℓ E).map (r • φ) = toAlgCl ℓ E r • (algClDerived ℓ E).map φ :=
  ModuleCat.derivedExtendScalars_map_smul _ _ r φ

/-- The extension of scalars `- ⊗_E F : Dᵇ_fd(E) ⥤ Dᵇ_fd(F)`. -/
noncomputable def fdTransition {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    FdStage.{u} ℓ E ⥤ FdStage.{u} ℓ F :=
  (boundedFiniteCohomology _).lift ((boundedFiniteCohomology _).ι ⋙ stageDerived ℓ h)
    fun X ↦ ModuleCat.boundedFiniteCohomology_derivedExtendScalars_obj _ _ X.2

/-- The extension of scalars `- ⊗_E ℚ̄_ℓ : Dᵇ_fd(E) ⥤ Dᵇ_fd(ℚ̄_ℓ)`. -/
noncomputable def fdToAlgCl (E : FiniteIntermediateField ℓ) : FdStage.{u} ℓ E ⥤ FdAlgCl.{u} ℓ :=
  (boundedFiniteCohomology _).lift ((boundedFiniteCohomology _).ι ⋙ algClDerived ℓ E)
    fun X ↦ ModuleCat.boundedFiniteCohomology_derivedExtendScalars_obj _ _ X.2

/-- The transitivity isomorphism `(- ⊗_E F) ⊗_F ℚ̄_ℓ ≅ - ⊗_E ℚ̄_ℓ`. -/
noncomputable def fdTransitionCompIso {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    fdTransition.{u} ℓ h ⋙ fdToAlgCl ℓ F ≅ fdToAlgCl ℓ E :=
  NatIso.ofComponents (fun X ↦ (boundedFiniteCohomology _).isoMk
      ((stageCompIso ℓ h).app X.obj).symm)
    fun {X Y} f ↦ by
      ext
      exact (stageCompIso ℓ h).inv.naturality f.hom

/-- The cocone of categories `E ↦ Dᵇ_fd(E)` with vertex `Dᵇ_fd(ℚ̄_ℓ)`. -/
noncomputable def fdCocone :
    CategoryCocone (fun E : FiniteIntermediateField ℓ ↦ FdStage.{u} ℓ E) (FdAlgCl.{u} ℓ) where
  T h := fdTransition ℓ h
  Φ E := fdToAlgCl ℓ E
  iso h := fdTransitionCompIso ℓ h

/-- Finitely many elements of `ℚ̄_ℓ` lie in a finite subextension containing a given one. -/
lemma exists_le_forall_mem (m : FiniteIntermediateField ℓ) (S : Finset (PadicAlgCl ℓ)) :
    ∃ L : FiniteIntermediateField ℓ, m ≤ L ∧ ∀ x ∈ S, x ∈ L.1 := by
  let A := IntermediateField.adjoin ℚ_[ℓ] (S : Set (PadicAlgCl ℓ))
  have : FiniteDimensional ℚ_[ℓ] A :=
    IntermediateField.finiteDimensional_adjoin fun x _ ↦ Algebra.IsIntegral.isIntegral x
  exact ⟨⟨m.1 ⊔ A, inferInstance⟩, le_sup_left (a := m.1),
    fun x hx ↦ le_sup_right (a := m.1) (IntermediateField.subset_adjoin _ _ hx)⟩

/-- **(Hom), injectivity**: extension of scalars `Dᵇ_fd(E) ⥤ Dᵇ_fd(ℚ̄_ℓ)` is faithful. -/
theorem fdCocone_homInj : (fdCocone.{u} ℓ).HomInj := by
  intro k x y g g' h
  refine ⟨k, le_rfl, ?_⟩
  have : g = g' := by
    ext
    exact ModuleCat.derivedExtendScalars_map_injective_of_field _ _ x.2 y.2
      (congr_arg (fun t ↦ t.hom) h)
  rw [this]

/-- An elementary identity between conjugates by isomorphisms. -/
private lemma conj_aux {𝒞 : Type*} [Category* 𝒞] {Xi Yj X0 Y0 X1 Y1 XL YL : 𝒞}
    (f : Xi ⟶ Yj) (u : Xi ≅ X0) (v : Yj ≅ Y0) (wx : X0 ≅ X1) (wy : Y0 ≅ Y1) (p : Xi ≅ XL)
    (q : Yj ≅ YL) (rx : XL ≅ X1) (ry : YL ≅ Y1) (hx : p.hom ≫ rx.hom = u.hom ≫ wx.hom)
    (hy : q.hom ≫ ry.hom = v.hom ≫ wy.hom) (M : X1 ⟶ Y1) (S : X0 ⟶ Y0)
    (hM : M = wx.inv ≫ S ≫ wy.hom) (hS : S = u.inv ≫ f ≫ v.hom) :
    f = p.hom ≫ rx.hom ≫ M ≫ ry.inv ≫ q.inv := by
  have hy' : ry.inv ≫ q.inv = wy.inv ≫ v.inv := by
    rw [← cancel_epi (q.hom ≫ ry.hom), Category.assoc, ry.hom_inv_id_assoc, q.hom_inv_id, hy,
      Category.assoc, wy.hom_inv_id_assoc, v.hom_inv_id]
  rw [hy', hM, hS, reassoc_of% hx]
  simp

lemma algClDerived_map_sum_stageDerived {m L : FiniteIntermediateField ℓ} (hmL : m ≤ L)
    {X Y : DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} m.1))} {ι : Type*} (t : Finset ι)
    (a : ι → ULift.{u + 1} L.1) (φ : ι → (X ⟶ Y)) :
    (algClDerived ℓ L).map (∑ i ∈ t, a i • (stageDerived ℓ hmL).map (φ i)) =
      (stageCompIso ℓ hmL).inv.app X ≫
        (∑ i ∈ t, toAlgCl ℓ L (a i) • (algClDerived ℓ m).map (φ i)) ≫
        (stageCompIso ℓ hmL).hom.app Y := by
  rw [Functor.map_sum]
  rw [Preadditive.sum_comp]
  refine Eq.trans ?_ (Preadditive.comp_sum _ _ _).symm
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hn : (algClDerived ℓ L).map ((stageDerived ℓ hmL).map (φ i)) =
      (stageCompIso ℓ hmL).inv.app X ≫ (algClDerived ℓ m).map (φ i) ≫
        (stageCompIso ℓ hmL).hom.app Y := by
    rw [← cancel_epi ((stageCompIso ℓ hmL).hom.app X), Iso.hom_inv_id_app_assoc]
    exact ((stageCompIso ℓ hmL).hom.naturality (φ i)).symm
  refine (algClDerived_map_smul ℓ L (a i) _).trans ?_
  refine (congrArg (fun t ↦ toAlgCl ℓ L (a i) • t) hn).trans ?_
  exact ((congrArg (fun t ↦ (stageCompIso ℓ hmL).inv.app X ≫ t)
    (Linear.smul_comp (r := toAlgCl ℓ L (a i)) (f := (algClDerived ℓ m).map (φ i))
      (g := (stageCompIso ℓ hmL).hom.app Y))).trans
    (Linear.comp_smul (f := (stageCompIso ℓ hmL).inv.app X) (r := toAlgCl ℓ L (a i))
      (g := (algClDerived ℓ m).map (φ i) ≫ (stageCompIso ℓ hmL).hom.app Y))).symm

/-- **(Hom), surjectivity**: every morphism between extensions of scalars to `ℚ̄_ℓ` is defined
over a finite subextension. -/
theorem fdCocone_homSurj : (fdCocone.{u} ℓ).HomSurj := by
  classical
  intro i j x y f
  obtain ⟨m, hi, hj⟩ := exists_ge_ge i j
  let x' := (fdTransition ℓ hi).obj x
  let y' := (fdTransition ℓ hj).obj y
  let f' := ((fdCocone ℓ).iso hi).hom.app x ≫ f ≫ ((fdCocone ℓ).iso hj).inv.app y
  obtain ⟨s, hs⟩ := ModuleCat.exists_eq_sum_smul_derivedExtendScalars_map_of_field (toAlgCl ℓ m)
    (flat_of_field _) x'.2 y'.2 f'.hom
  obtain ⟨L, hmL, hL⟩ := exists_le_forall_mem ℓ m (s.image fun p ↦ p.1.down)
  have hL' (p) (hp : p ∈ s) : p.1.down ∈ L.1 := hL _ (Finset.mem_image_of_mem _ hp)
  let a : s → ULift.{u + 1} L.1 := fun p ↦ ⟨⟨p.1.1.down, hL' p.1 p.2⟩⟩
  have ha (p : s) : toAlgCl ℓ L (a p) = p.1.1 := rfl
  let M := (algClDerived ℓ L).map (∑ p : s, a p • (stageDerived ℓ hmL).map p.1.2)
  let g' : (fdTransition ℓ (hi.trans hmL)).obj x ⟶ (fdTransition ℓ (hj.trans hmL)).obj y :=
    ObjectProperty.homMk ((stageStageIso ℓ hi hmL).hom.app x.obj ≫
      (∑ p : s, a p • (stageDerived ℓ hmL).map p.1.2) ≫ (stageStageIso ℓ hj hmL).inv.app y.obj)
  refine ⟨L, hi.trans hmL, hj.trans hmL, g', ?_⟩
  ext
  have hf' : f'.hom = ∑ p : s, p.1.1 • (algClDerived ℓ m).map p.1.2 :=
    hs.trans (Finset.sum_coe_sort s (fun p ↦ p.1 • _)).symm
  have ef' : f'.hom = (stageCompIso ℓ hi).inv.app x.obj ≫ f.hom ≫
      (stageCompIso ℓ hj).hom.app y.obj := rfl
  have Knat (φ : x'.obj ⟶ y'.obj) : (algClDerived ℓ L).map ((stageDerived ℓ hmL).map φ) =
      (stageCompIso ℓ hmL).inv.app x'.obj ≫ (algClDerived ℓ m).map φ ≫
        (stageCompIso ℓ hmL).hom.app y'.obj := by
    rw [← cancel_epi ((stageCompIso ℓ hmL).hom.app x'.obj), Iso.hom_inv_id_app_assoc]
    exact ((stageCompIso ℓ hmL).hom.naturality φ).symm
  have hf'' : (∑ p : s, p.1.1 • (algClDerived ℓ m).map p.1.2) =
      (stageCompIso ℓ hi).inv.app x.obj ≫ f.hom ≫ (stageCompIso ℓ hj).hom.app y.obj :=
    hf'.symm.trans ef'
  have hM : M = (stageCompIso ℓ hmL).inv.app x'.obj ≫
      (∑ p : s, p.1.1 • (algClDerived ℓ m).map p.1.2) ≫
      (stageCompIso ℓ hmL).hom.app y'.obj :=
    algClDerived_map_sum_stageDerived ℓ hmL Finset.univ a (fun p ↦ p.1.2)
  have := conj_aux f.hom ((stageCompIso ℓ hi).app x.obj) ((stageCompIso ℓ hj).app y.obj)
    ((stageCompIso ℓ hmL).app x'.obj) ((stageCompIso ℓ hmL).app y'.obj)
    ((stageCompIso ℓ (hi.trans hmL)).app x.obj) ((stageCompIso ℓ (hj.trans hmL)).app y.obj)
    ((algClDerived ℓ L).mapIso ((stageStageIso ℓ hi hmL).app x.obj))
    ((algClDerived ℓ L).mapIso ((stageStageIso ℓ hj hmL).app y.obj))
    (stageCompIso_assoc ℓ hi hmL x.obj).symm (stageCompIso_assoc ℓ hj hmL y.obj).symm M _ hM hf''
  change f.hom = (stageCompIso ℓ (hi.trans hmL)).hom.app x.obj ≫
    (algClDerived ℓ L).map ((stageStageIso ℓ hi hmL).hom.app x.obj ≫
      (∑ p : s, a p • (stageDerived ℓ hmL).map p.1.2) ≫ (stageStageIso ℓ hj hmL).inv.app y.obj) ≫
      (stageCompIso ℓ (hj.trans hmL)).inv.app y.obj
  simp only [Functor.map_comp, Category.assoc]
  exact this

/-- The objects of `D(ℚ̄_ℓ)` coming from a finite stage. -/
def fromFiniteStage : ObjectProperty (DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1}
    (PadicAlgCl ℓ)))) :=
  fun V ↦ ∃ (E : FiniteIntermediateField ℓ) (x : FdStage.{u} ℓ E),
    Nonempty ((algClDerived ℓ E).obj x.obj ≅ V)

instance : (fromFiniteStage.{u} ℓ).IsClosedUnderIsomorphisms where
  of_iso e := fun ⟨E, x, ⟨e'⟩⟩ ↦ ⟨E, x, ⟨e' ≪≫ e⟩⟩

/-- **(Obj)**: every object of `Dᵇ_fd(ℚ̄_ℓ)` comes from a finite stage. -/
theorem fdCocone_essSurjObj : (fdCocone.{u} ℓ).EssSurjObj := by
  intro d
  obtain ⟨E₀⟩ : Nonempty (FiniteIntermediateField ℓ) := inferInstance
  have h : fromFiniteStage.{u} ℓ d.obj := by
    refine prop_of_boundedFiniteCohomology_of_field _ (fun X hX ↦ ?_) (fun X Y hX hY ↦ ?_)
      (fun X n hX ↦ ?_) ?_ d.2
    · obtain ⟨Z, hZ⟩ : ∃ Z : DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} E₀.1)),
          IsZero Z := ⟨_, Limits.isZero_zero _⟩
      exact ⟨E₀, ⟨Z, (boundedFiniteCohomology _).prop_of_isZero hZ⟩,
        ⟨((algClDerived ℓ E₀).map_isZero hZ).iso hX⟩⟩
    · obtain ⟨a, x, ⟨ex⟩⟩ := hX
      obtain ⟨b, y, ⟨ey⟩⟩ := hY
      obtain ⟨k, ha, hb⟩ := exists_ge_ge a b
      let x' := (fdTransition ℓ ha).obj x
      let y' := (fdTransition ℓ hb).obj y
      have := preservesBinaryBiproducts_of_preservesBiproducts (algClDerived.{u} ℓ k)
      refine ⟨k, ⟨x'.obj ⊞ y'.obj, (boundedFiniteCohomology _).ext_of_isTriangulatedClosed₂ _
        (binaryBiproductTriangle_distinguished _ _) x'.2 y'.2⟩,
        ⟨(algClDerived ℓ k).mapBiprod _ _ ≪≫ biprod.mapIso
          (((stageCompIso ℓ ha).app x.obj).symm ≪≫ ex)
          (((stageCompIso ℓ hb).app y.obj).symm ≪≫ ey)⟩⟩
    · obtain ⟨a, x, ⟨ex⟩⟩ := hX
      exact ⟨a, ⟨x.obj⟦n⟧, (boundedFiniteCohomology _).le_shift n _ x.2⟩,
        ⟨((algClDerived ℓ a).commShiftIso n).app x.obj ≪≫ (shiftFunctor _ n).mapIso ex⟩⟩
    · exact ⟨E₀, ⟨_, @boundedFiniteCohomology_singleFunctor _ _
        (ModuleCat.of _ (ULift.{u + 1} E₀.1)) (Module.Finite.self _)⟩,
        ⟨ModuleCat.derivedExtendScalarsSingleIso _ _⟩⟩
  obtain ⟨E, x, ⟨e⟩⟩ := h
  exact ⟨E, x, ⟨(boundedFiniteCohomology _).isoMk e⟩⟩

/-- Blueprint `lemma-perfect-complexes-geometric-point` (the target `Dᵇ_fd(ℚ̄_ℓ)`): the bounded
derived category of finite-dimensional `ℚ̄_ℓ`-vector spaces, with the extensions of scalars
`- ⊗_E ℚ̄_ℓ : Dᵇ_fd(E) ⥤ Dᵇ_fd(ℚ̄_ℓ)`, is the filtered 2-colimit
`Dᵇ_fd(ℚ̄_ℓ) = 2-colim_E Dᵇ_fd(E)` over the finite subextensions `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, with the
transition functors `- ⊗_E F`. -/
theorem fdCocone_isFilteredTwoColimit : (fdCocone.{u} ℓ).IsFilteredTwoColimit where
  essSurjObj := fdCocone_essSurjObj ℓ
  homSurj := fdCocone_homSurj ℓ
  homInj := fdCocone_homInj ℓ

end PadicAlgCl
