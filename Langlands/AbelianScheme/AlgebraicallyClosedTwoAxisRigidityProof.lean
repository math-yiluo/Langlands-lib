/-
Adapted from Mathlib/AlgebraicGeometry/Group/Abelian.lean.
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Original authors: Andrew Yang, Christian Merten.
Adaptation: Worker 423, with the proof route suggested by Worker 334.
-/
import Langlands.AbelianScheme.AlgebraicallyClosedTwoAxisRigidityStatement
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Proof of two-axis rigidity over an algebraically closed field -/

universe u

open CategoryTheory Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory

namespace Langlands.AbelianScheme

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The published two-axis rigidity proposition holds in every universe. -/
theorem algebraicallyClosedTwoAxisRigidity : AlgebraicallyClosedTwoAxisRigidity.{u} := by
  intro K _ _ A H hA hAA hH hHft a b g ha hb
  have := hA
  have := hAA
  have := hH
  have := hHft
  let S := Spec (CommRingCat.of K)
  let point : S := IsLocalRing.closedPoint K
  have hpoint : IsClosed {point} := isClosed_discrete _
  have : IsClosedImmersion a.left :=
    isClosedImmersion_of_comp_eq_id A.hom a.left (by simp)
  have : Nonempty A.left := ⟨a.left point⟩
  have : IsProper (A ⊗ A).hom := by dsimp; infer_instance
  have : IsProper (g.left ≫ H.hom) := by rw [Over.w]; infer_instance
  have : JacobsonSpace (A ⊗ A).left :=
    LocallyOfFiniteType.jacobsonSpace (Y := Spec _) (A ⊗ A).hom
  have : Surjective A.hom :=
    ⟨Function.surjective_to_subsingleton (α := A.left) (β := Spec _) _⟩
  have : IsProper (fst A A).left := by dsimp; infer_instance
  have : Surjective (fst A A).left := by dsimp; infer_instance
  have : IsSeparated (fst A H).left := by dsimp; infer_instance
  have : LocallyOfFiniteType (fst A H).left := by dsimp; infer_instance
  have : IsClosedImmersion ((lift a b).left ≫ (fst A H).left) := by
    simpa using inferInstanceAs (IsClosedImmersion a.left)
  have : IsClosedImmersion (lift a b).left :=
    .of_comp _ (g := (fst A H).left)
  let γ : A ⊗ A ⟶ A ⊗ H := lift (fst A A) g
  have : IsProper (γ.left ≫ (fst A H).left) := by simpa [γ]
  have : IsProper γ.left := .of_comp _ (fst A H).left
  apply Over.OverMorphism.ext
  -- The first axis equation makes the image over the pointed first coordinate a singleton.
  have hsingle :
      γ.left '' ((fst A A).left ⁻¹' {a.left point}) ⊆ {(lift a b).left point} := by
    rw [Set.image_subset_iff, ← Set.sdiff_eq_empty, ← Set.not_nonempty_iff_eq_empty]
    intro hbad
    obtain ⟨c₀, ⟨hc₁, hc₂⟩, hc₃⟩ := nonempty_inter_closedPoints hbad <| by
      rw [Set.sdiff_eq_compl_inter, ← Set.image_singleton, ← Set.image_singleton]
      refine (IsOpen.isLocallyClosed ?_).inter (IsClosed.isLocallyClosed ?_)
      · exact (((lift a b).left.isClosedMap _ hpoint).preimage γ.left.continuous).isOpen_compl
      · exact (a.left.isClosedMap _ hpoint).preimage (fst A A).left.continuous
    obtain ⟨⟨c, hc⟩, e⟩ := (pointEquivClosedPoint (A ⊗ A).hom).surjective ⟨c₀, hc₃⟩
    obtain rfl : c point = c₀ := congr(($e).1)
    let fc : 𝟙_ (Over S) ⟶ 𝟙_ (Over S) ⊗ A :=
      lift (𝟙 _) (Over.homMk c hc ≫ snd A A)
    have hca : c ≫ pullback.fst A.hom A.hom = a.left :=
      ext_of_apply_closedPoint_eq A.hom (by simpa) (by simp) (by simpa)
    have hfactor : c = fc.left ≫ (a ▷ A).left := by
      dsimp
      ext <;> simp [fc, S, hca]
    have haxis : fc ≫ (a ▷ A) ≫ γ = lift a b := by
      ext1 <;> simp [fc, γ, S, ha]
    exact hc₂ <| by
      simp [hfactor, haxis, ← Scheme.Hom.comp_apply, Category.assoc, ← Over.comp_left]
  -- Zariski Main gives finite fibre images over an open neighborhood of the pointed value.
  obtain ⟨U, haU, hfinite⟩ :=
    exists_finite_imageι_comp_morphismRestrict_of_finite_image_preimage
      γ.left (fst A H).left (a.left point) (by
        dsimp [-Scheme.Hom.comp_base, γ]
        simp only [pullback.lift_fst]
        exact (Set.finite_singleton _).subset hsingle)
  have hfib (x : U) :
      ((pullback.fst A.hom H.hom) ⁻¹' {x.1} ∩ Set.range ⇑γ.left).Finite := by
    refine ((((γ.left.imageι ≫ (fst A H).left) ∣_ U).finite_preimage_singleton x).image
      (Scheme.Opens.ι _ ≫ γ.left.imageι)).subset ?_
    have hx : U.ι ⁻¹' {x.1} = {x} := by ext; simp
    rw [← hx, ← Set.preimage_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base,
      morphismRestrict_ι, ← Category.assoc, Scheme.Hom.comp_base (_ ≫ _) (fst A H).left,
      TopCat.coe_comp, Set.preimage_comp, Set.image_preimage_eq_inter_range]
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
    dsimp
    rw [Set.image_preimage_eq_inter_range, Scheme.IdealSheafData.range_subschemeι,
      Scheme.Hom.support_ker, ← Set.inter_assoc, ← Set.preimage_inter,
      Set.singleton_inter_of_mem x.2, IsClosed.closure_eq
        (by exact γ.left.isClosedMap.isClosed_range)]
  -- On a dense open, irreducibility and the second axis identify the image of every closed point.
  refine ext_of_apply_eq H.hom _
    ((fst A A).left ⁻¹ᵁ U).isOpen.isLocallyClosed
    (((fst A A).left ⁻¹ᵁ U).isOpen.dense ?_) ?_ ?_
  · exact .preimage ⟨_, haU⟩ (fst A A).left.surjective
  · intro y hyU hy
    have hx : IsClosed {(fst A A).left y} := by
      simpa using (fst A A).left.isClosedMap _ hy
    let x : 𝟙_ _ ⟶ A :=
      Over.homMk (pointOfClosedPoint A.hom _ hx) (by simp)
    let ya : (A ⊗ A).left :=
      (fst A A ≫ (ρ_ A).inv ≫ A ◁ a).left y
    have heq : γ.left y = γ.left ya := by
      refine subsingleton_image_closure_of_finite_of_isPreirreducible
        (hx.preimage (fst A A).left.continuous).isLocallyClosed ?_ γ.left.continuous
        γ.left.isClosedMap
        ((hfib ⟨_, hyU⟩).subset (Set.image_subset_iff.mpr fun _ ↦ by
          simp [← Scheme.Hom.comp_apply, -Scheme.Hom.comp_base, γ])) ?_ ?_
      · let α : A ⊗ A ⟶ A ⊗ A := toUnit _ ≫ x ⊗ₘ 𝟙 _
        convert!
          ((IrreducibleSpace.isIrreducible_univ _).image α.left
            α.left.continuous.continuousOn).isPreirreducible
        rw [Over.tensorHom_left]
        simp [Set.range_comp, Scheme.Pullback.range_map, x]
      · exact ⟨y, subset_closure (by simp), rfl⟩
      · refine ⟨ya, subset_closure ?_, rfl⟩
        simp [ya, ← Scheme.Hom.comp_apply, -Scheme.Hom.comp_base]
    convert! congr((snd A H).left $heq) using 1
    · simp [γ, ← Scheme.Hom.comp_apply]
    · simp only [ya, γ, ← Scheme.Hom.comp_apply, ← Over.comp_left]
      have hconst :
          fst A A ≫ (ρ_ A).inv ≫ (A ◁ a) ≫ g = toUnit (A ⊗ A) ≫ b := by
        rw [hb]
        simp
      simpa using (congrArg (fun f : A ⊗ A ⟶ H => f.left y) hconst).symm
  · simp

end Langlands.AbelianScheme
