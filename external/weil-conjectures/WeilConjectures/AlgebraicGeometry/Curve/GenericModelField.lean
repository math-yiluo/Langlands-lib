/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.GenericModelAux
public import WeilConjectures.AlgebraicGeometry.DenseOpenComponentModifications
public import WeilConjectures.AlgebraicGeometry.FieldBaseChangeDimension
public import WeilConjectures.AlgebraicGeometry.GenericFiber.GenericSmoothness
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization

/-!
# The generic curve model over a field

Let `X` be of finite type over a field `F`, of dimension at most one. A *generic curve model
datum* for `X` (`AlgebraicGeometry.IsGenericCurveModelData`) is a finite family of finite
morphisms `νₐ : Yₐ ⟶ X` with `Yₐ` smooth over `F` of relative dimension `0` or `1`, jointly
surjective, whose sum `∐ Yₐ ⟶ X` is a closed immersion over an open of `X` with finite
complement.

Over a perfect field such a datum is given by the normalizations of the irreducible components
of `X_red` (`AlgebraicGeometry.isGenericCurveModelData_of_perfectField`); over an arbitrary field
it exists after a finite purely inseparable extension
(`AlgebraicGeometry.exists_isPurelyInseparable_isGenericCurveModelData`), by descent from the
perfect closure. These are the generic-fibre steps of
`proposition-proper-direct-image-finite-coefficients`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- A *generic curve model datum* for a scheme `X` over a field `F`: finitely many finite
morphisms `νₐ : Yₐ ⟶ X`, with `Yₐ` smooth over `F` of relative dimension `dₐ ≤ 1`, such that
`∐ Yₐ ⟶ X` is surjective and is a closed immersion over an open `W ⊆ X` with finite
complement. -/
def IsGenericCurveModelData {F : Type u} [Field F] {X : Scheme.{u}} (g : X ⟶ Spec (.of F)) :
    Prop :=
  ∃ (ι : Type u) (_ : Finite ι) (Y : ι → Scheme.{u}) (ν : ∀ a, Y a ⟶ X) (d : ι → ℕ)
    (W : X.Opens), (∀ a, IsFinite (ν a)) ∧
    (∀ a, d a ≤ 1 ∧ SmoothOfRelativeDimension (d a) (ν a ≫ g)) ∧
    Surjective (Sigma.desc ν) ∧ IsClosedImmersion (Sigma.desc ν ∣_ W) ∧ (W : Set X)ᶜ.Finite

/-- A nonempty space of dimension at most one has dimension `0` or `1`. -/
lemma exists_nat_le_one_of_topologicalKrullDim_le_one {X : Type*} [TopologicalSpace X]
    [Nonempty X] (h : topologicalKrullDim X ≤ 1) :
    ∃ d : ℕ, d ≤ 1 ∧ topologicalKrullDim X = d := by
  obtain ⟨x⟩ := ‹Nonempty X›
  have : Nonempty (TopologicalSpace.IrreducibleCloseds X) :=
    ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  have h0 : 0 ≤ topologicalKrullDim X := Order.krullDim_nonneg
  induction h' : topologicalKrullDim X using WithBot.recBotCoe with
  | bot => rw [h'] at h0; simp at h0
  | coe m =>
    induction m using ENat.recTopCoe with
    | top =>
      rw [h'] at h
      have h2 : (⊤ : ℕ∞) ≤ 1 := by exact_mod_cast h
      exact absurd h2 (by simp)
    | coe n =>
      rw [h'] at h
      have hn : n ≤ 1 := by exact_mod_cast h
      exact ⟨n, hn, rfl⟩

/-- A reduced noetherian scheme admits a finite list of its distinct irreducible components,
each with an integral closed subscheme structure. -/
lemma exists_integral_component_cover {X : Scheme.{u}} [IsReduced X] [IsNoetherian X] :
    ∃ (n : ℕ) (C : Fin n → Scheme.{u}) (ι : ∀ i, C i ⟶ X),
      (∀ i, IsIntegral (C i) ∧ IsClosedImmersion (ι i) ∧
        Set.range (ι i) ∈ irreducibleComponents X) ∧
      Function.Injective (fun i => Set.range (ι i)) ∧
      (∀ Z ∈ irreducibleComponents X, ∃ i, Set.range (ι i) = Z) := by
  classical
  let A := {Z : Set X // Z ∈ irreducibleComponents X}
  have : Fintype A := (finite_irreducibleComponents_of_isNoetherian (X := X)).fintype
  let e : Fin (Fintype.card A) ≃ A := (Fintype.equivFin A).symm
  let Z (i : Fin (Fintype.card A)) : TopologicalSpace.Closeds X :=
    ⟨(e i).1, isClosed_of_mem_irreducibleComponents _ (e i).2⟩
  let I (i : Fin (Fintype.card A)) := Scheme.IdealSheafData.vanishingIdeal (Z i)
  refine ⟨Fintype.card A, fun i => (I i).subscheme, fun i => (I i).subschemeι, ?_, ?_, ?_⟩
  · intro i
    have hr : Set.range (I i).subschemeι = (e i).1 := by
      simp [I, Z]
    have hi : IrreducibleSpace (I i).subscheme := Subtype.irreducibleSpace (e i).2.1
    have : IsIntegral (I i).subscheme := isIntegral_of_irreducibleSpace_of_isReduced _
    exact ⟨inferInstance, inferInstance, hr.symm ▸ (e i).2⟩
  · intro i j hij
    apply e.injective
    apply Subtype.ext
    simpa [I, Z] using hij
  · intro W hW
    obtain ⟨i, hi⟩ := e.surjective ⟨W, hW⟩
    refine ⟨i, ?_⟩
    simp [I, Z, hi]

/-- The normalization of an integral scheme of dimension at most one, of finite type over a
perfect field, is finite over it, smooth of relative dimension `0` or `1` over the field, and an
isomorphism over a dense open. -/
lemma exists_smoothOfRelativeDimension_fromNormalization {k : Type u} [Field k]
    [PerfectField k] (C : Scheme.{u}) [IsIntegral C] (q : C ⟶ Spec (.of k))
    [LocallyOfFiniteType q] (hdim : topologicalKrullDim C ≤ 1) :
    ∃ d : ℕ, d ≤ 1 ∧ IsFinite C.fromNormalization ∧
      SmoothOfRelativeDimension d (C.fromNormalization ≫ q) ∧
      ∃ U : C.Opens, Dense (U : Set C) ∧ IsIso (C.fromNormalization ∣_ U) := by
  have := C.isFinite_fromNormalization_of_locallyOfFiniteType q
  have : IsLocallyNoetherian C.normalization :=
    LocallyOfFiniteType.isLocallyNoetherian (C.fromNormalization ≫ q)
  have hK (x : Spec C.functionField) :
      IsIntegrallyClosed ((Spec C.functionField).presheaf.stalk x) := by
    let := TopCat.Presheaf.algebra_section_stalk (Spec C.functionField).presheaf
      (⟨x, trivial⟩ : (⊤ : (Spec C.functionField).Opens))
    have := (isAffineOpen_top (Spec C.functionField)).isLocalization_stalk ⟨x, trivial⟩
    have : IsIntegrallyClosed Γ(Spec C.functionField, ⊤) :=
      .of_equiv (Scheme.ΓSpecIso C.functionField).commRingCatIsoToRingEquiv.symm
    exact isIntegrallyClosed_of_isLocalization _ _
      ((isAffineOpen_top _).primeIdealOf ⟨x, trivial⟩).asIdeal.primeCompl_le_nonZeroDivisors
  have hdim' : topologicalKrullDim C.normalization ≤ 1 :=
    (C.topologicalKrullDim_normalization q).trans_le hdim
  have : IsRegular C.normalization := IsRegular.of_isIntegrallyClosed_stalk
    (fun y => ⟨inferInstance, C.fromSpecFunctionField.isIntegrallyClosed_stalk_normalization
      hK y⟩) hdim'
  have : Smooth (C.fromNormalization ≫ q) := smooth_of_isRegular _
  obtain ⟨d, hd1, hd⟩ := exists_nat_le_one_of_topologicalKrullDim_le_one hdim'
  obtain ⟨U, hU, hiso⟩ := C.exists_isIso_fromNormalization_restrict q
  exact ⟨d, hd1, inferInstance,
    (smoothOfRelativeDimension_iff_topologicalKrullDim_eq _ d).mpr hd, U, U.isOpen.dense hU,
    hiso⟩

/-- **The generic curve model over a perfect field.** A scheme of finite type and of dimension at
most one over a perfect field `E` has a generic curve model datum: the normalizations of the
irreducible components of `X_red` (smooth since `E` is perfect, `lemma-proper-smooth-model--1`),
which are isomorphisms over a dense open; a dense open of a curve has finite complement. -/
theorem isGenericCurveModelData_of_perfectField {E : Type u} [Field E] [PerfectField E]
    {X : Scheme.{u}} (g : X ⟶ Spec (.of E)) [LocallyOfFiniteType g] [QuasiCompact g]
    (hdim : topologicalKrullDim X ≤ 1) : IsGenericCurveModelData g := by
  classical
  obtain ⟨hred, hci, hsurj, -⟩ :=
    reduction_isReduced_isClosedImmersion_isSurjective_isUniversalHomeomorphism X
  set R := X.nilradical.subscheme
  set r := X.nilradical.subschemeι
  have hr : IsHomeomorph r := isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨r.isEmbedding, r.surjective⟩
  set q := r ≫ g
  have : IsNoetherian R := isNoetherian_of_locallyOfFiniteType q
  have hdimR : topologicalKrullDim R ≤ 1 := (IsHomeomorph.topologicalKrullDim_eq _ hr).trans_le hdim
  obtain ⟨n, C, ι, hC, hinj, hcover⟩ := exists_integral_component_cover (X := R)
  have (i : Fin n) : IsIntegral (C i) := (hC i).1
  have hm (i : Fin n) : ∃ d : ℕ, d ≤ 1 ∧ IsFinite (C i).fromNormalization ∧
      SmoothOfRelativeDimension d ((C i).fromNormalization ≫ ι i ≫ q) ∧
      ∃ U : (C i).Opens, Dense (U : Set (C i)) ∧ IsIso ((C i).fromNormalization ∣_ U) := by
    have : IsIntegral (C i) := (hC i).1
    have : IsClosedImmersion (ι i) := (hC i).2.1
    exact exists_smoothOfRelativeDimension_fromNormalization (C i) (ι i ≫ q)
      (((ι i).isClosedEmbedding.isInducing.topologicalKrullDim_le).trans hdimR)
  choose d hd1 hfin hsm hU using hm
  have (i : Fin n) : IsClosedImmersion (ι i) := (hC i).2.1
  obtain ⟨U, hUd, hUiso⟩ := exists_dense_open_isIso_component_modifications R n C ι
    (fun i => ⟨(hC i).1, (hC i).2.1, (hC i).2.2⟩) hinj hcover (fun i ↦ (C i).normalization)
    (fun i ↦ (C i).fromNormalization) hU
  set νR := Sigma.desc (fun i ↦ (C i).fromNormalization ≫ ι i)
  have : IsFinite νR := inferInstance
  have hνRs : Surjective νR := by
    have hsub : (U : Set R) ⊆ Set.range νR := by
      intro x hx
      obtain ⟨y, hy⟩ := (νR ∣_ U).surjective ⟨x, hx⟩
      refine ⟨(νR ⁻¹ᵁ U).ι y, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← morphismRestrict_ι, Scheme.Hom.comp_apply, hy]
      rfl
    have h := (hUd.mono hsub).closure_eq
    rw [νR.isClosedMap.isClosed_range.closure_eq] at h
    exact ⟨fun x ↦ by rw [← Set.mem_range, h]; exact Set.mem_univ x⟩
  let Y : ULift.{u} (Fin n) → Scheme.{u} := fun a ↦ (C a.down).normalization
  let ν : ∀ a, Y a ⟶ X := fun a ↦ (C a.down).fromNormalization ≫ ι a.down ≫ r
  let eσ : ∐ Y ≅ ∐ (fun i ↦ (C i).normalization) :=
    Sigma.whiskerEquiv (f := Y) (g := fun i ↦ (C i).normalization) Equiv.ulift
      (fun _ ↦ Iso.refl _)
  have heσ : Sigma.desc ν = eσ.hom ≫ νR ≫ r := by
    ext a
    simp [eσ, ν, νR]
    rfl
  let W : X.Opens := ⟨r '' U, hr.isOpenMap _ U.isOpen⟩
  have hWU : r ⁻¹ᵁ W = U := by
    ext x
    exact hr.injective.mem_set_image
  have hUc : (U : Set R)ᶜ.Finite :=
    finite_compl_of_dense_of_topologicalKrullDim_le_one hdimR hUd U.isOpen
  refine ⟨ULift.{u} (Fin n), inferInstance, Y, ν, fun a ↦ d a.down, W, fun a ↦ ?_,
    fun a ↦ ⟨hd1 a.down, ?_⟩, ?_, ?_, ?_⟩
  · have := hfin a.down
    infer_instance
  · simpa [ν, q, Category.assoc] using hsm a.down
  · rw [heσ]
    infer_instance
  · rw [heσ, morphismRestrict_comp, morphismRestrict_comp]
    have : IsIso (νR ∣_ (r ⁻¹ᵁ W)) := Scheme.Hom.isIso_restrict_of_le hWU.le hUiso
    infer_instance
  · refine (hUc.image r).subset ?_
    intro x hx
    obtain ⟨y, rfl⟩ := r.surjective x
    exact ⟨y, fun hy ↦ hx ⟨y, hy, rfl⟩, rfl⟩

/-- **The generic curve model after a purely inseparable extension.** Let `X` be of finite type,
quasi-separated and of dimension at most one over a field `K`. There is a finite purely
inseparable extension `L/K` such that the base change `X_L` has a generic curve model datum.
The datum exists over the perfect closure of `K`
(`AlgebraicGeometry.isGenericCurveModelData_of_perfectField`); it is defined over a finite
subextension (finite presentation), and its properties descend along the faithfully flat
extension of the perfect closure. -/
theorem exists_isPurelyInseparable_isGenericCurveModelData (K : Type u) [Field K]
    {X : Scheme.{u}} (g : X ⟶ Spec (.of K)) [LocallyOfFiniteType g] [QuasiCompact g]
    [QuasiSeparated g] (hdim : topologicalKrullDim X ≤ 1) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
      (_ : IsPurelyInseparable K L) (YL : Scheme.{u}) (a : YL ⟶ X) (b : YL ⟶ Spec (.of L)),
      IsPullback a b g (Spec.map (CommRingCat.ofHom (algebraMap K L))) ∧
      IsGenericCurveModelData b := by
  classical
  let E := perfectClosure K (AlgebraicClosure K)
  let D := (IntermediateField.subextDiagram K E).op ⋙ Scheme.Spec
  let c := subextSpecCone K E
  have hc : IsLimit c := isLimitSubextSpecCone K E
  have : ∀ {i j : (IntermediateField.FiniteSubext K E)ᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f) :=
    fun f ↦ isAffineHom_of_isAffine (X := Spec _) (Y := Spec _) _
  let i₀ : (IntermediateField.FiniteSubext K E)ᵒᵖ := Opposite.op ⟨⊥, inferInstance⟩
  let e : Spec (.of K) ≅ D.obj i₀ := Scheme.Spec.mapIso
    (RingEquiv.toCommRingCatIso (IntermediateField.botEquiv K E).toRingEquiv).op
  set p : X ⟶ D.obj i₀ := g ≫ e.hom
  set gE : pullback p (c.π.app i₀) ⟶ Spec (.of E) := pullback.snd p (c.π.app i₀)
  have hdimE : topologicalKrullDim (pullback p (c.π.app i₀) : Scheme.{u}) ≤ 1 := by
    rw [topologicalKrullDim_pullback_eq_of_field (k := i₀.unop.1) p (c.π.app i₀)]
    exact hdim
  obtain ⟨ι, _, Y, ν, d, W, hfin, hsm, hsurj, hci, hWfin⟩ :=
    isGenericCurveModelData_of_perfectField gE hdimE
  have := Fintype.ofFinite ι
  -- the base changed system `X ×_K L`, with limit `X_E`
  let Db := baseChangeDiagram D p
  let cb := baseChangeCone D c p
  have hcb : IsLimit cb := isLimitBaseChangeCone D c p hc
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace g
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated g
  have : IsLocallyNoetherian (pullback p (c.π.app i₀)) :=
    LocallyOfFiniteType.isLocallyNoetherian gE
  have : CompactSpace ↥(pullback p (c.π.app i₀)) := QuasiCompact.compactSpace_of_compactSpace gE
  have : IsNoetherian (pullback p (c.π.app i₀)) := {}
  have : TopologicalSpace.NoetherianSpace cb.pt :=
    inferInstanceAs (TopologicalSpace.NoetherianSpace ↥(pullback p (c.π.app i₀)))
  -- descend the `νₐ` and `W` to stages
  have hex (a : ι) : ∃ (j : Over i₀) (Y' : Scheme.{u}) (p' : Y' ⟶ Db.obj j) (h : Y a ⟶ Y'),
      IsPullback h (ν a) p' (cb.π.app j) := by
    have := (IsFinite.locallyOfFinitePresentation_of_isLocallyNoetherian (ν a)).1
    obtain ⟨j, Y', p', -, -, -, h, H⟩ := Scheme.exists_isPullback_of_finitePresentation hcb (ν a)
    exact ⟨j, Y', p', h, H⟩
  choose j₀ Y₀ p₀ h₀ H₀ using hex
  obtain ⟨jW, OW, -, hOW⟩ := exists_preimage_eq Db cb hcb W
    (TopologicalSpace.NoetherianSpace.isCompact _)
  obtain ⟨k, hk⟩ := IsCofiltered.inf_objs_exists (insert jW (Finset.univ.image j₀))
  let fW : k ⟶ jW := (hk (Finset.mem_insert_self _ _)).some
  let fa (a : ι) : k ⟶ j₀ a :=
    (hk (Finset.mem_insert_of_mem (Finset.mem_image_of_mem j₀ (Finset.mem_univ a)))).some
  let Y' (a : ι) : Scheme.{u} := pullback (p₀ a) (Db.map (fa a))
  let p' (a : ι) : Y' a ⟶ Db.obj k := pullback.snd _ _
  let h' (a : ι) : Y a ⟶ Y' a := isPullbackLift Db cb (fa a) (H₀ a)
  have H (a : ι) : IsPullback (h' a) (ν a) (p' a) (cb.π.app k) :=
    isPullback_isPullbackLift (fa a) (H₀ a)
  let Wk : (Db.obj k).Opens := Db.map fW ⁻¹ᵁ OW
  have hWk : cb.π.app k ⁻¹ᵁ Wk = W := by
    rw [← Scheme.Hom.comp_preimage, cb.w fW, hOW]
  -- the stage `k` is a finite purely inseparable extension `L`
  let L := k.left.unop.1
  have hD : D.map k.hom = Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ e.hom := by
    change Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext x
    obtain ⟨y, rfl⟩ := (IntermediateField.botEquiv K E).symm.surjective x
    apply Subtype.ext
    simp only [Functor.op_obj, Functor.op_map, Quiver.Hom.unop_op, IntermediateField.botEquiv_symm,
      Iso.op_hom, RingEquiv.toCommRingCatIso_hom, AlgEquiv.toRingEquiv_toRingHom,
      CommRingCat.hom_comp, ConcreteCategory.hom_ofHom, RingHom.coe_comp, RingHom.coe_coe,
      Function.comp_apply, SetLike.coe_eq_coe]
    erw [IntermediateField.botEquiv_def]
    rfl
  have hcπ := surjective_inf_flat_inf_quasiCompact_Spec_map_algebraMap L E
  have hcbπ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
      (cb.π.app k) :=
    MorphismProperty.of_isPullback (isPullback_baseChangeCone_π D c p k).flip hcπ
  have : Surjective (cb.π.app k) := hcbπ.1.1
  have := IsFinite.descendsAlong_surjective_inf_flat_inf_quasicompact
  have := IsClosedImmersion.descendsAlong_surjective_inf_flat_inf_quasicompact
  have hsq (a : ι) := (H a).paste_vert (isPullback_baseChangeCone_π D c p k)
  -- the sum of the descended morphisms
  have Hσ := isPullback_sigmaDesc p' ν h' (cb.π.app k) H
  refine ⟨L, inferInstance, inferInstance, k.left.unop.2,
    IsPurelyInseparable.tower_bot K L E, pullback p (D.map k.hom), pullback.fst _ _,
    pullback.snd _ _, ?_, ι, inferInstance, Y', p', d, Wk, fun a ↦ ?_, fun a ↦ ⟨(hsm a).1, ?_⟩,
    ?_, ?_, ?_⟩
  · refine (IsPullback.of_hasPullback p (D.map k.hom)).of_iso (Iso.refl _) (Iso.refl _)
      (Iso.refl _) e.symm (by simp) (by simp) (by simp [p]) (by simp [hD])
  · have := hfin a
    exact MorphismProperty.of_isPullback_of_descendsAlong (P := @IsFinite)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (H a).flip hcbπ inferInstance
  · have := (hsm a).2
    exact MorphismProperty.of_isPullback_of_descendsAlong
      (P := @SmoothOfRelativeDimension (d a)) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      (hsq a).flip hcπ inferInstance
  · have : Surjective (Limits.Sigma.map h' ≫ Sigma.desc p') := by
      rw [Hσ.w]
      exact MorphismProperty.comp_mem @Surjective _ _ hsurj hcbπ.1.1
    exact ⟨fun x ↦ ⟨_, ((Limits.Sigma.map h' ≫ Sigma.desc p').surjective x).choose_spec⟩⟩
  · obtain ⟨a', -, Ha'⟩ := AlgebraicGeometry.IsPullback.exists_isPullback_morphismRestrict Hσ Wk
    have hci' : IsClosedImmersion (Sigma.desc ν ∣_ (cb.π.app k ⁻¹ᵁ Wk)) :=
      Scheme.Hom.restrict_of_le _ _ hWk.le hci
    have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
        (cb.π.app k ∣_ Wk) := by
      obtain ⟨⟨h₁, h₂⟩, h₃⟩ := hcbπ
      exact ⟨⟨IsZariskiLocalAtTarget.restrict h₁ Wk, inferInstance⟩, inferInstance⟩
    exact MorphismProperty.of_isPullback_of_descendsAlong (P := @IsClosedImmersion)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) Ha'.flip hQ hci'
  · refine (hWfin.image (cb.π.app k)).subset ?_
    intro x hx
    obtain ⟨y, rfl⟩ := (cb.π.app k).surjective x
    refine ⟨y, fun hy ↦ hx ?_, rfl⟩
    rw [← hWk] at hy
    exact hy

end AlgebraicGeometry
