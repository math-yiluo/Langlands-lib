/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
public import WeilConjectures.AlgebraicGeometry.FieldExtensionDescent
public import WeilConjectures.AlgebraicGeometry.FieldExtensionLimit
public import WeilConjectures.AlgebraicGeometry.GenericFiber.SpreadingOut
public import WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism

/-!
# Generic smoothness over a perfect field

Let `Y` be a scheme locally of finite type over a perfect field `E`. The smooth locus of the
reduction `Y_red ⟶ Spec E` is dense (`Scheme.Hom.dense_smoothLocus_of_perfectField`), so `Y`
has a dense open `W` whose reduction is smooth over `E`.

## Main statements

- `AlgebraicGeometry.exists_dense_isClosedImmersion_smooth_of_perfectField`
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- **Generic smoothness over a perfect field.** Let `g : Y ⟶ Spec E` be locally of finite
type, `E` a perfect field. There are a dense open `W ⊆ Y` and a surjective closed immersion
`z : Z ⟶ W` with `Z` smooth over `E` (namely `Z = W_red`). -/
theorem exists_dense_isClosedImmersion_smooth_of_perfectField {E : Type u} [Field E]
    [PerfectField E] {Y : Scheme.{u}} (g : Y ⟶ Spec (.of E)) [LocallyOfFiniteType g] :
    ∃ (W : Y.Opens) (Z : Scheme.{u}) (z : Z ⟶ W.toScheme),
      Dense (W : Set Y) ∧ IsClosedImmersion z ∧ Surjective z ∧ Smooth (z ≫ W.ι ≫ g) := by
  obtain ⟨hred, -, hsurj, -⟩ :=
    reduction_isReduced_isClosedImmersion_isSurjective_isUniversalHomeomorphism Y
  have := hred
  set r := Y.nilradical.subschemeι
  have hr : IsHomeomorph r.base := isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨r.isEmbedding, r.surjective⟩
  set O := (r ≫ g).smoothLocus
  have hO : Dense (O : Set Y.nilradical.subscheme) := (r ≫ g).dense_smoothLocus_of_perfectField
  let W : Y.Opens := ⟨r.base '' O, hr.isOpenMap _ O.isOpen⟩
  have hWO : r ⁻¹ᵁ W = O := by
    ext x
    exact hr.injective.mem_set_image
  refine ⟨W, O.toScheme, (Y.nilradical.subscheme.isoOfEq hWO).inv ≫ r ∣_ W, ?_, ?_, ?_, ?_⟩
  · exact hr.surjective.denseRange.dense_image hr.continuous hO
  · infer_instance
  · have : Surjective (r ∣_ W) := IsZariskiLocalAtTarget.restrict hsurj W
    infer_instance
  · rw [Category.assoc, morphismRestrict_ι_assoc, Scheme.isoOfEq_inv_ι_assoc]
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
    ext x
    simp

/-- **Generic smoothness after a finite purely inseparable extension.** Let
`g : Y ⟶ Spec K` be of finite type. There are a finite purely inseparable extension `L / K`,
the base change `Y_L = Y ×_K L` (given by a cartesian square), a dense open `W ⊆ Y_L` and a
surjective closed immersion `Z ⟶ W` with `Z` smooth over `L`.

Over the perfect closure `E` of `K` this is generic smoothness
(`AlgebraicGeometry.exists_dense_isClosedImmersion_smooth_of_perfectField`); the data descend to
a finite subextension of the algebraic extension `E / K`
(`AlgebraicGeometry.exists_open_isClosedImmersion_of_isLimit`), where smoothness holds by fpqc
descent along `Spec E ⟶ Spec L`. -/
theorem exists_isPurelyInseparable_dense_isClosedImmersion_smooth (K : Type u) [Field K]
    {Y : Scheme.{u}} (g : Y ⟶ Spec (.of K)) [LocallyOfFiniteType g] [QuasiCompact g] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
      (_ : IsPurelyInseparable K L) (YL : Scheme.{u}) (a : YL ⟶ Y) (b : YL ⟶ Spec (.of L))
      (W : YL.Opens) (Z : Scheme.{u}) (z : Z ⟶ W.toScheme),
      IsPullback a b g (Spec.map (CommRingCat.ofHom (algebraMap K L))) ∧
      Dense (W : Set YL) ∧ IsClosedImmersion z ∧ Surjective z ∧ Smooth (z ≫ W.ι ≫ b) := by
  let E := perfectClosure K (AlgebraicClosure K)
  let D := (IntermediateField.subextDiagram K E).op ⋙ Scheme.Spec
  let c := subextSpecCone K E
  have hc : IsLimit c := isLimitSubextSpecCone K E
  have : ∀ {i j : (IntermediateField.FiniteSubext K E)ᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f) :=
    fun f ↦
    isAffineHom_of_isAffine (X := Spec _) (Y := Spec _) _
  have : ∀ i : (IntermediateField.FiniteSubext K E)ᵒᵖ, IsNoetherian (D.obj i) := fun i ↦
    inferInstanceAs (IsNoetherian (Spec (.of i.unop.1)))
  let i₀ : (IntermediateField.FiniteSubext K E)ᵒᵖ := Opposite.op ⟨⊥, inferInstance⟩
  let e : Spec (.of K) ≅ D.obj i₀ := Scheme.Spec.mapIso
    (RingEquiv.toCommRingCatIso (IntermediateField.botEquiv K E).toRingEquiv).op
  set p : Y ⟶ D.obj i₀ := g ≫ e.hom
  set gE : pullback p (c.π.app i₀) ⟶ Spec (.of E) := pullback.snd p (c.π.app i₀)
  obtain ⟨W, Z, z, hWd, hz₁, hz₂, hz₃⟩ := exists_dense_isClosedImmersion_smooth_of_perfectField gE
  have : IsLocallyNoetherian (pullback p (c.π.app i₀)) :=
    LocallyOfFiniteType.isLocallyNoetherian gE
  have : CompactSpace ↥(pullback p (c.π.app i₀)) :=
    QuasiCompact.compactSpace_of_compactSpace gE
  have : IsNoetherian (pullback p (c.π.app i₀)) := {}
  have hWc : IsCompact (SetLike.coe W) := TopologicalSpace.NoetherianSpace.isCompact _
  obtain ⟨j, f, Wj, Zj, zj, s, hzj₁, hzj₂, hpre, hs⟩ :=
    exists_open_isClosedImmersion_of_isLimit hc p W hWc z
  have hD : D.map f = Spec.map (CommRingCat.ofHom (algebraMap K j.unop.1)) ≫ e.hom := by
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
  have hcπ := surjective_inf_flat_inf_quasiCompact_Spec_map_algebraMap j.unop.1 E
  refine ⟨j.unop.1, inferInstance, inferInstance, j.unop.2,
    IsPurelyInseparable.tower_bot K j.unop.1 E, pullback p (D.map f), pullback.fst _ _,
    pullback.snd _ _, Wj, Zj, zj, ?_, ?_, hzj₁, hzj₂, ?_⟩
  · refine (IsPullback.of_hasPullback p (D.map f)).of_iso (Iso.refl _) (Iso.refl _)
      (Iso.refl _) e.symm (by simp) (by simp) (by simp [p]) (by simp [hD])
  · let t := pullback.map p (c.π.app i₀) p (D.map f) (𝟙 Y) (c.π.app j) (𝟙 _) (by simp)
      (by rw [Category.comp_id, c.w f])
    have ht : IsPullback t gE (pullback.snd p (D.map f)) (c.π.app j) :=
      isPullback_baseChangeCone_π D c p (Over.mk f)
    have : Surjective t := MorphismProperty.of_isPullback ht.flip hcπ.1.1
    refine Dense.mono ?_ (t.surjective.denseRange.dense_image t.continuous hWd)
    rintro _ ⟨x, hx, rfl⟩
    rw [← hpre] at hx
    exact hx
  · exact MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hs.flip hcπ hz₃

end AlgebraicGeometry
