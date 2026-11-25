/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.RingTheory.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.CategoryTheory.Filtered.Final
import WeilConjectures.AlgebraicGeometry.Affine.Limit.AffineLimitFibreDimensionBound

/-!
# Quasi-finiteness descends for a finitely presented affine model

The tensor products are expressed as pushouts in `CommRingCat`. The canonical map
from the left factor is `pushout.inl`; `CommRingCat.pushoutCoconeIsColimit` identifies
this pushout and map with the algebra tensor product and its left inclusion.

## References

* Stacks Project, Limits, in Situation 081D, specialized to affine schemes
* Stacks Project, Limits, Tag 094M in Situation 081D
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem locallyQuasiFinite_of_isQuasiFinite
    {X Y : Scheme.{u}} {f : X ⟶ Y} (hf : Scheme.Hom.IsQuasiFinite f) :
    LocallyQuasiFinite f := by
  let := hf.1
  apply locallyQuasiFinite_iff_isDiscrete_preimage_singleton.mpr
  intro y
  refine ⟨discreteTopology_iff_isOpen_singleton.mpr ?_⟩
  rintro ⟨x, hx⟩
  have hx' : f x = y := hx
  subst y
  simpa only [Set.image_singleton, Scheme.Hom.asFiber, Homeomorph.apply_symm_apply] using
    (f.fiberHomeo (f x)).isOpenMap _ (hf.2.2 x)

private theorem fibre_dimension_le_zero_of_isQuasiFinite
    {R S : CommRingCat.{u}} (f : R ⟶ S) (hf : Scheme.Hom.IsQuasiFinite (Spec.map f))
    (p : Ideal R) [p.IsPrime] :
    topologicalKrullDim
      ↥(pullback (Spec.map f)
        (Spec.map (CommRingCat.ofHom (algebraMap R p.ResidueField))) : Scheme.{u}) ≤ 0 := by
  have := locallyQuasiFinite_of_isQuasiFinite hf
  have : IsLocallyArtinian
      (pullback (Spec.map f)
        (Spec.map (CommRingCat.ofHom (algebraMap R p.ResidueField)))) :=
    .of_locallyQuasiFinite (pullback.snd _ _)
  exact topologicalKrullDim_zero_of_discreteTopology _

private theorem isQuasiFinite_of_fibre_dimension_le_zero
    {R S : CommRingCat.{u}} (f : R ⟶ S) (hft : f.hom.FiniteType)
    (hbound : ∀ (p : Ideal R) [p.IsPrime],
      topologicalKrullDim
        ↥(pullback (Spec.map f)
          (Spec.map (CommRingCat.ofHom (algebraMap R p.ResidueField))) : Scheme.{u}) ≤ 0) :
    Scheme.Hom.IsQuasiFinite (Spec.map f) := by
  have : LocallyOfFiniteType (Spec.map f) := HasRingHomProperty.Spec_iff.mpr hft
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro x
  let p : Spec R := Spec.map f x
  let e : (Spec.map f).fiber p ≅
      pullback (Spec.map f)
        (Spec.map (CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField))) :=
    asIso (pullback.map _ _ _ _ (𝟙 _) (Spec.map (Scheme.Spec.residueFieldIso R p).inv)
      (𝟙 _) (by simp) (by
        simp [Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]))
  have hd : topologicalKrullDim ((Spec.map f).fiber p) ≤ 0 := by
    rw [e.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq]
    exact hbound p.asIdeal
  have : LocallyOfFiniteType ((Spec.map f).fiberToSpecResidueField p) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _))
  have : IsLocallyNoetherian ((Spec.map f).fiber p) :=
    LocallyOfFiniteType.isLocallyNoetherian ((Spec.map f).fiberToSpecResidueField p)
  have : IsLocallyArtinian ((Spec.map f).fiber p) :=
    .of_topologicalKrullDim_le_zero hd
  exact isOpen_discrete _

/-- Quasi-finiteness of the limit affine base change descends to a stage at least `i₀`. -/
theorem descend_isQuasiFinite_affine
    {I : Type u} [PartialOrder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (A : I ⥤ CommRingCat.{u}) (c : Cocone A) (hc : IsColimit c)
    (i₀ : I) (B₀ : CommRingCat.{u}) (b₀ : A.obj i₀ ⟶ B₀)
    (hfp : b₀.hom.FinitePresentation)
    (hqf : Scheme.Hom.IsQuasiFinite (Spec.map (pushout.inl (c.ι.app i₀) b₀))) :
    ∃ (i : I) (hi : i₀ ≤ i),
      Scheme.Hom.IsQuasiFinite (Spec.map (pushout.inl (A.map (homOfLE hi)) b₀)) := by
  classical
  let J := {i : I // i₀ ≤ i}
  let j₀ : J := ⟨i₀, le_rfl⟩
  let : Nonempty J := ⟨j₀⟩
  let : IsDirected J (· ≤ ·) := ⟨fun i j ↦ by
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i.val j.val
    exact ⟨⟨k, i.property.trans hik⟩, hik, hjk⟩⟩
  let F : J ⥤ I :=
    { obj := Subtype.val
      map := fun f ↦ homOfLE (leOfHom f) }
  have : F.Final := Functor.final_of_exists_of_isFiltered F (fun i ↦ by
    obtain ⟨j, hij, h₀j⟩ := exists_ge_ge i i₀
    exact ⟨⟨j, h₀j⟩, ⟨homOfLE hij⟩⟩)
    (fun {_ j} s t ↦ ⟨j, 𝟙 _, Subsingleton.elim _ _⟩)
  let A' := F ⋙ A
  let c' : Cocone A' := c.whisker F
  have hc' : IsColimit c' := (Functor.Final.isColimitWhiskerEquiv F c).symm hc
  let a (j : J) : A.obj i₀ ⟶ A'.obj j := A.map (homOfLE j.property)
  have ha {i j : J} (f : i ⟶ j) : a i ≫ A'.map f = a j := by
    dsimp [a, A', F]
    rw [← A.map_comp]
    rfl
  have hac (j : J) : a j ≫ c'.ι.app j = c.ι.app i₀ := c.w _
  let B : J ⥤ CommRingCat.{u} :=
    { obj := fun j ↦ pushout (a j) b₀
      map := fun {i j} f ↦ pushout.desc
        (A'.map f ≫ pushout.inl (a j) b₀) (pushout.inr (a j) b₀) (by
          rw [← Category.assoc, ha, pushout.condition])
      map_id := by
        intro j
        apply pushout.hom_ext <;> simp
      map_comp := by
        intro i j k f g
        apply pushout.hom_ext <;> simp [Category.assoc] }
  let φ : A' ⟶ B :=
    { app := fun j ↦ pushout.inl (a j) b₀
      naturality := by intro i j f; simp [B] }
  let d : Cocone B :=
    { pt := pushout (c.ι.app i₀) b₀
      ι :=
        { app := fun j ↦ pushout.desc
            (c'.ι.app j ≫ pushout.inl (c.ι.app i₀) b₀)
            (pushout.inr (c.ι.app i₀) b₀) (by
              rw [← Category.assoc, hac, pushout.condition])
          naturality := by
            intro i j f
            apply pushout.hom_ext <;> simp [B, Category.assoc] } }
  have hd : IsColimit d := by
    refine { desc := ?_, fac := ?_, uniq := ?_ }
    · intro s
      let t : Cocone A' :=
        { pt := s.pt
          ι :=
            { app := fun j ↦ φ.app j ≫ s.ι.app j
              naturality := by
                intro i j f
                rw [← Category.assoc, φ.naturality, Category.assoc, s.w]
                simp } }
      refine pushout.desc (hc'.desc t) (pushout.inr (a j₀) b₀ ≫ s.ι.app j₀) ?_
      have h := hc'.fac t j₀
      change c.ι.app i₀ ≫ hc'.desc t = _ at h
      rw [h]
      dsimp [t, φ]
      rw [← Category.assoc, ← pushout.condition]
      simp [a, j₀]
    · intro s j
      apply pushout.hom_ext
      · simp [d, φ, Category.assoc]
      · have h := s.w (homOfLE (show j₀ ≤ j from j.property))
        have h' := congrArg (fun f ↦ pushout.inr (a j₀) b₀ ≫ f) h
        simpa [B, Category.assoc, d] using h'.symm
    · intro s m hm
      apply pushout.hom_ext
      · apply hc'.hom_ext
        intro j
        have h := congrArg (fun f ↦ pushout.inl (a j) b₀ ≫ f) (hm j)
        simpa [d, Category.assoc] using h
      · have h := congrArg (fun f ↦ pushout.inr (a j₀) b₀ ≫ f) (hm j₀)
        simpa [d, Category.assoc] using h
  have hfinite (j : J) : (φ.app j).hom.FiniteType :=
    RingHom.finiteType_isStableUnderBaseChange.pushout_inl
      RingHom.finiteType_respectsIso (a j) b₀ (RingHom.FiniteType.of_finitePresentation hfp)
  have hsurj (i j : J) (hij : i ≤ j) :
      Function.Surjective
        (pushout.desc (φ.app j) (B.map (homOfLE hij))
          (φ.naturality (homOfLE hij))).hom := by
    have hpush : IsPushout (φ.app i) (A'.map (homOfLE hij))
        (B.map (homOfLE hij)) (φ.app j) := by
      apply IsPushout.of_top (t := (IsPushout.of_hasPushout (a i) b₀).flip)
        (p := (φ.naturality _).symm)
      simpa [B, φ, ha] using (IsPushout.of_hasPushout (a j) b₀).flip
    have heq : pushout.desc (φ.app j) (B.map (homOfLE hij))
        (φ.naturality (homOfLE hij)) = hpush.flip.isoPushout.inv := by
      apply pushout.hom_ext <;> simp
    rw [heq]
    exact (ConcreteCategory.bijective_of_isIso _).2
  let eA : colimit A' ≅ c'.pt := (colimit.isColimit A').coconePointUniqueUpToIso hc'
  let eB : colimit B ≅ d.pt := (colimit.isColimit B).coconePointUniqueUpToIso hd
  have heq : colimMap φ ≫ eB.hom = eA.hom ≫ pushout.inl (c.ι.app i₀) b₀ := by
    apply colimit.hom_ext
    intro j
    simp [eA, eB, φ, d]
  have heqSpec : Spec.map (colimMap φ) =
      Spec.map eB.inv ≫ Spec.map (pushout.inl (c.ι.app i₀) b₀) ≫ Spec.map eA.hom := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← heq]
    simp
  have hloc := locallyQuasiFinite_of_isQuasiFinite hqf
  have hlft := hqf.1
  have hloclim : LocallyQuasiFinite (Spec.map (colimMap φ)) := by
    rw [heqSpec]
    infer_instance
  have hlftlim : LocallyOfFiniteType (Spec.map (colimMap φ)) := by
    rw [heqSpec]
    infer_instance
  have hqflim : Scheme.Hom.IsQuasiFinite (Spec.map (colimMap φ)) :=
    ⟨hlftlim, inferInstance, fun x ↦
      Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mp
        ((Spec.map (colimMap φ)).quasiFiniteAt x)⟩
  obtain ⟨j, hj⟩ := exists_stage_fibre_dimension_le A' B φ hfinite hsurj 0
    (fun p _ ↦ fibre_dimension_le_zero_of_isQuasiFinite _ hqflim p)
  exact ⟨j.val, j.property, isQuasiFinite_of_fibre_dimension_le_zero _ (hfinite j) hj⟩

end AlgebraicGeometry
