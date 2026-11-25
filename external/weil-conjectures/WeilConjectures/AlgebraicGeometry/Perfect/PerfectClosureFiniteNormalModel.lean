/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

import WeilConjectures.AlgebraicGeometry.Reduced.ReducedAlgebraicNormalizationFieldChange
import WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism
import WeilConjectures.AlgebraicGeometry.FieldExtensionLimit
import WeilConjectures.AlgebraicGeometry.FieldExtensionFpqcCover
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-!
# A finite normal model over a finite part of a perfect closure

## References

* Stacks Project, Varieties, Tag 0BXT, proof through the dense-open descent
* Stacks Project, Varieties, Tag 0BXT, proof, and Limits, Tags 01ZM, 01ZO, 01Z4 and 01ZP
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem normal_stalks_of_iso {A B : Scheme.{u}} (e : A ≅ B)
    (hA : ∀ z : A, IsDomain (A.presheaf.stalk z) ∧
      IsIntegrallyClosed (A.presheaf.stalk z)) :
    ∀ z : B, IsDomain (B.presheaf.stalk z) ∧
      IsIntegrallyClosed (B.presheaf.stalk z) := by
  intro z
  obtain ⟨hd, hi⟩ := hA (e.inv z)
  have : IsDomain (A.presheaf.stalk (e.inv z)) := hd
  have : IsIntegrallyClosed (A.presheaf.stalk (e.inv z)) := hi
  let es := (asIso (e.inv.stalkMap z)).commRingCatIsoToRingEquiv
  exact ⟨es.symm.toMulEquiv.isDomain, IsIntegrallyClosed.of_equiv es⟩

private theorem dense_of_dense_preimage {A B : Scheme.{u}} (f : A ⟶ B)
    (U : B.Opens) (hU : Dense (f ⁻¹ᵁ U : Set A)) [Surjective f] :
    Dense (U : Set B) := by
  have h := f.surjective.denseRange.dense_image f.continuous hU
  exact h.mono (by rintro _ ⟨x, hx, rfl⟩; exact hx)

private theorem restrict_pullback {Z Y ZL YL : Scheme.{u}} {a : ZL ⟶ Z}
    {γL : ZL ⟶ YL} {γ : Z ⟶ Y} {b : YL ⟶ Y} (H : IsPullback a γL γ b) (W : Y.Opens) :
    ∃ a' : (γL ⁻¹ᵁ (b ⁻¹ᵁ W)).toScheme ⟶ (γ ⁻¹ᵁ W).toScheme,
      a' ≫ (γ ⁻¹ᵁ W).ι = (γL ⁻¹ᵁ (b ⁻¹ᵁ W)).ι ≫ a ∧
      IsPullback a' (γL ∣_ (b ⁻¹ᵁ W)) (γ ∣_ W) (b ∣_ W) := by
  have hr : Set.range ((γL ⁻¹ᵁ (b ⁻¹ᵁ W)).ι ≫ a) ⊆ Set.range (γ ⁻¹ᵁ W).ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    change γ (a ((γL ⁻¹ᵁ (b ⁻¹ᵁ W)).ι x)) ∈ W
    rw [← Scheme.Hom.comp_apply, H.w, Scheme.Hom.comp_apply]
    exact x.2
  refine ⟨IsOpenImmersion.lift (γ ⁻¹ᵁ W).ι _ hr, IsOpenImmersion.lift_fac _ _ _, ?_⟩
  refine IsPullback.of_right ?_ ?_ (isPullback_morphismRestrict γ W).flip
  · rw [IsOpenImmersion.lift_fac, morphismRestrict_ι]
    exact (isPullback_morphismRestrict γL (b ⁻¹ᵁ W)).flip.paste_horiz H
  · rw [← cancel_mono W.ι, Category.assoc, Category.assoc, morphismRestrict_ι,
      IsOpenImmersion.lift_fac_assoc, morphismRestrict_ι, morphismRestrict_ι_assoc,
      Category.assoc, H.w]

/-- A finite normal model of perfect-closure normalization, with a dense closed-immersion
locus on both source and target. -/
theorem exists_perfectClosure_finite_normal_model
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    [IsPurelyInseparable k K] [PerfectField K]
    (X : Scheme.{u}) (q : X ⟶ Spec (.of k))
    [LocallyOfFiniteType q] [QuasiCompact q] :
    ∃ E : IntermediateField k K, Module.Finite k E ∧
      ∃ (Y : Scheme.{u})
        (f : Y ⟶ pullback q (Spec.map (CommRingCat.ofHom (algebraMap k E))))
        (U : (pullback q (Spec.map (CommRingCat.ofHom (algebraMap k E)))).Opens),
        IsFinite f ∧ Surjective f ∧
        Dense (Set.range U.ι) ∧
        Dense (f ⁻¹ᵁ U : Set Y) ∧ IsClosedImmersion (f ∣_ U) ∧
        ∀ z : (pullback
            (f ≫ pullback.snd q (Spec.map (CommRingCat.ofHom (algebraMap k E))))
            (Spec.map (CommRingCat.ofHom (algebraMap E K))) : Scheme.{u}),
          IsDomain ((pullback
            (f ≫ pullback.snd q (Spec.map (CommRingCat.ofHom (algebraMap k E))))
            (Spec.map (CommRingCat.ofHom (algebraMap E K)))).presheaf.stalk z) ∧
          IsIntegrallyClosed ((pullback
            (f ≫ pullback.snd q (Spec.map (CommRingCat.ofHom (algebraMap k E))))
            (Spec.map (CommRingCat.ofHom (algebraMap E K)))).presheaf.stalk z) := by
  classical
  let D := (IntermediateField.subextDiagram k K).op ⋙ Scheme.Spec
  let c := subextSpecCone k K
  have hc : IsLimit c := isLimitSubextSpecCone k K
  have : ∀ {i j : (IntermediateField.FiniteSubext k K)ᵒᵖ}
      (f : i ⟶ j), IsAffineHom (D.map f) := fun f ↦
    isAffineHom_of_isAffine (X := Spec _) (Y := Spec _) _
  let i₀ : (IntermediateField.FiniteSubext k K)ᵒᵖ := .op ⟨⊥, inferInstance⟩
  let e : Spec (.of k) ≅ D.obj i₀ := Scheme.Spec.mapIso
    (RingEquiv.toCommRingCatIso (IntermediateField.botEquiv k K).toRingEquiv).op
  let p : X ⟶ D.obj i₀ := q ≫ e.hom
  let T := pullback p (c.π.app i₀)
  let g : T ⟶ Spec (.of K) := pullback.snd _ _
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian g
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace g
  have : IsNoetherian T := ⟨⟩
  obtain ⟨hred, hredci, hreds, -⟩ :=
    reduction_isReduced_isClosedImmersion_isSurjective_isUniversalHomeomorphism T
  let R := T.nilradical.subscheme
  let r : R ⟶ T := T.nilradical.subschemeι
  have hr : IsHomeomorph r := isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨r.isEmbedding, r.surjective⟩
  obtain ⟨hfin, hsurj, ⟨V, -, hVd, hVi⟩, -⟩ :=
    reduced_algebraic_normalization_field_change R (r ≫ g)
  have : IsFinite R.fromReducedNormalization := hfin
  have : Surjective R.fromReducedNormalization := hsurj
  let N := R.reducedNormalization
  let ν : N ⟶ T := R.fromReducedNormalization ≫ r
  have : IsFinite ν := inferInstance
  have : Surjective ν := inferInstance
  let W : T.Opens := ⟨r '' V, hr.isOpenMap _ V.isOpen⟩
  have hWV : r ⁻¹ᵁ W = V := by
    ext x
    exact hr.injective.mem_set_image
  have hWd : Dense (W : Set T) :=
    r.surjective.denseRange.dense_image r.continuous hVd
  have hNd : Dense (ν ⁻¹ᵁ W : Set N) := by
    change Dense ((R.fromReducedNormalization ≫ r) ⁻¹ᵁ W : Set N)
    rw [Scheme.Hom.comp_preimage, hWV]
    exact dense_preimage_normalization R (r ≫ g) V hVd
  have hWci : IsClosedImmersion (ν ∣_ W) := by
    dsimp only [ν]
    rw [morphismRestrict_comp]
    have : IsIso (R.fromReducedNormalization ∣_ (r ⁻¹ᵁ W)) := hWV.symm ▸ hVi
    infer_instance
  have : LocallyOfFinitePresentation ν :=
    (IsFinite.locallyOfFinitePresentation_of_isLocallyNoetherian ν).1
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace q
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian q
  let Db := baseChangeDiagram D p
  let cb := baseChangeCone D c p
  have hcb : IsLimit cb := isLimitBaseChangeCone D c p hc
  have : TopologicalSpace.NoetherianSpace cb.pt :=
    inferInstanceAs (TopologicalSpace.NoetherianSpace T)
  obtain ⟨j, Y₀, f₀, hf₀, hqc₀, hqs₀, h₀, H₀⟩ :=
    Scheme.exists_isPullback_of_finitePresentation hcb ν
  obtain ⟨jW, OW, -, hOW⟩ := exists_preimage_eq Db cb hcb W
    (TopologicalSpace.NoetherianSpace.isCompact _)
  obtain ⟨j', a, b, -⟩ := IsCofilteredOrEmpty.cone_objs j jW
  let Y := pullback f₀ (Db.map a)
  let f : Y ⟶ Db.obj j' := pullback.snd _ _
  let h : N ⟶ Y := isPullbackLift Db cb a H₀
  have H : IsPullback h ν f (cb.π.app j') := isPullback_isPullbackLift a H₀
  let U₀ : (Db.obj j').Opens := Db.map b ⁻¹ᵁ OW
  have hU₀ : cb.π.app j' ⁻¹ᵁ U₀ = W := by
    rw [← Scheme.Hom.comp_preimage, cb.w b, hOW]
  let E := j'.left.unop.1
  have hD : D.map j'.hom = Spec.map (CommRingCat.ofHom (algebraMap k E)) ≫ e.hom := by
    change Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext x
    obtain ⟨y, rfl⟩ := (IntermediateField.botEquiv k K).symm.surjective x
    apply Subtype.ext
    simp only [Functor.op_obj, Functor.op_map, Quiver.Hom.unop_op, IntermediateField.botEquiv_symm,
      Iso.op_hom, RingEquiv.toCommRingCatIso_hom, AlgEquiv.toRingEquiv_toRingHom,
      CommRingCat.hom_comp, ConcreteCategory.hom_ofHom, RingHom.coe_comp, RingHom.coe_coe,
      Function.comp_apply, SetLike.coe_eq_coe]
    erw [IntermediateField.botEquiv_def]
    rfl
  have hcπ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
      (Spec.map (CommRingCat.ofHom (algebraMap E K))) := by
    obtain ⟨hflat, hsurj, hqc, -⟩ := fpqcCover_specMap_algebraMap_of_field (k := E) (K := K)
    exact ⟨⟨hsurj, hflat⟩, hqc⟩
  have hcbπ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
      (cb.π.app j') :=
    MorphismProperty.of_isPullback (isPullback_baseChangeCone_π D c p j').flip hcπ
  have : Surjective (cb.π.app j') := hcbπ.1.1
  have := IsFinite.descendsAlong_surjective_inf_flat_inf_quasicompact
  have := IsClosedImmersion.descendsAlong_surjective_inf_flat_inf_quasicompact
  have hf : IsFinite f := MorphismProperty.of_isPullback_of_descendsAlong
    (P := @IsFinite) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) H.flip hcbπ inferInstance
  have hs : Surjective f := by
    refine ⟨fun x ↦ ?_⟩
    obtain ⟨t, rfl⟩ := (cb.π.app j').surjective x
    obtain ⟨n, rfl⟩ := ν.surjective t
    exact ⟨h n, congrArg (fun a : N ⟶ Db.obj j' ↦ a n) H.w⟩
  have hUd : Dense (U₀ : Set (Db.obj j')) :=
    dense_of_dense_preimage (cb.π.app j') U₀ (hU₀.symm ▸ hWd)
  have hhQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) h :=
    MorphismProperty.of_isPullback H.flip hcbπ
  have : Surjective h := hhQ.1.1
  have hYd : Dense (f ⁻¹ᵁ U₀ : Set Y) := by
    apply dense_of_dense_preimage h
    rw [← Scheme.Hom.comp_preimage, H.w, Scheme.Hom.comp_preimage, hU₀]
    exact hNd
  have hci : IsClosedImmersion (f ∣_ U₀) := by
    have : Flat (cb.π.app j') := hcbπ.1.2
    have : QuasiCompact (cb.π.app j') := hcbπ.2
    obtain ⟨a', -, Ha'⟩ := restrict_pullback H U₀
    have hci' : IsClosedImmersion (ν ∣_ (cb.π.app j' ⁻¹ᵁ U₀)) :=
      hU₀.symm ▸ hWci
    have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
        (cb.π.app j' ∣_ U₀) :=
      ⟨⟨IsZariskiLocalAtTarget.restrict hcbπ.1.1 U₀, inferInstance⟩, inferInstance⟩
    exact MorphismProperty.of_isPullback_of_descendsAlong (P := @IsClosedImmersion)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) Ha'.flip hQ hci'
  let B := pullback q (Spec.map (CommRingCat.ofHom (algebraMap k E)))
  have HB : IsPullback (pullback.fst p (D.map j'.hom))
      (pullback.snd p (D.map j'.hom)) q
      (Spec.map (CommRingCat.ofHom (algebraMap k E))) := by
    refine (IsPullback.of_hasPullback p (D.map j'.hom)).of_iso (Iso.refl _) (Iso.refl _)
      (Iso.refl _) e.symm (by simp) (by simp) (by simp [p]) (by simp [hD])
  let eB : Db.obj j' ≅ B := HB.isoPullback
  let fB : Y ⟶ B := f ≫ eB.hom
  let U : B.Opens := eB.hom ''ᵁ U₀
  have hUU : eB.hom ⁻¹ᵁ U = U₀ := Scheme.Hom.preimage_image_eq _ _
  have heB : eB.hom ≫ pullback.snd q
      (Spec.map (CommRingCat.ofHom (algebraMap k E))) = pullback.snd p (D.map j'.hom) :=
    HB.isoPullback_hom_snd
  have HN : IsPullback h (ν ≫ g)
      (fB ≫ pullback.snd q (Spec.map (CommRingCat.ofHom (algebraMap k E))))
      (Spec.map (CommRingCat.ofHom (algebraMap E K))) := by
    dsimp only [fB]
    simp only [Category.assoc, heB]
    exact H.paste_vert (isPullback_baseChangeCone_π D c p j')
  refine ⟨E, j'.left.unop.2, Y, fB, U, inferInstance, inferInstance, ?_, ?_, ?_, ?_⟩
  · simpa only [Scheme.Opens.range_ι, U, Scheme.Hom.coe_image] using
      eB.hom.surjective.denseRange.dense_image eB.hom.continuous hUd
  · change Dense ((f ≫ eB.hom) ⁻¹ᵁ U : Set Y)
    rwa [Scheme.Hom.comp_preimage, hUU]
  · dsimp only [fB]
    rw [morphismRestrict_comp]
    have : IsClosedImmersion (f ∣_ (eB.hom ⁻¹ᵁ U)) := hUU.symm ▸ hci
    infer_instance
  · exact normal_stalks_of_iso HN.isoPullback (normal_normalization R)

end AlgebraicGeometry
