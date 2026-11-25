/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.HigherDirectImageTransitions
import WeilConjectures.AlgebraicGeometry.HigherDirectImageColimitComparisonEpi
import WeilConjectures.AlgebraicGeometry.HigherDirectImageOverCoherence
import WeilConjectures.AlgebraicGeometry.HigherDirectImageAffineClassVanishing
import WeilConjectures.AlgebraicGeometry.EtaleSectionColimitRepresentative
import Mathlib.AlgebraicGeometry.Sites.AffineEtale

/-! # Descent of affine higher-image sections

Source: Stacks Project, Tags 09Z1, 03Q8 and 0738.
(blueprint: sbc-lem-higher-image-affine-class-descent).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- Every section of the limit higher image on an affine etale object descends.
Source: Stacks Project, Tag 09Z1, proof; Tag 0738(4).
(blueprint: sbc-lem-higher-image-affine-class-descent).

Proof:
1. Construct the opposite-indexed diagram K with canonical higher-image transitions
   and the cocone B with the limit higher image as its point. The transition
   coherence theorem proves the functor laws and the cone equations prove naturality.
2. Let ψ be the comparison from the sheaf colimit of K to B.pt. On an affine etale
   object, any section of colimit K has a stage representative by the filtered
   sheaf-colimit representative theorem. If ψ kills it, the existing affine
   eventual-vanishing theorem kills that representative at a later stage.
   The colimit relation then makes the original section zero. Thus ψ is monic
   on every affine etale object. Restriction to the dense affine etale site is
   an equivalence, so it reflects this pointwise monomorphism back to sheaves.
3. The local-surjectivity comparison theorem makes ψ epic. Module sheaves are
   abelian, hence balanced, so ψ is an isomorphism. Transport the colimit universal
   property across ψ: B is a colimit cocone with precisely its canonical legs.
4. Apply the filtered sheaf-colimit representative theorem again, now to B and
   the given section on V. Its finite-cover gluing argument produces one stage
   section. Unop its index; the cocone leg is definitionally the required
   higherDirectImageOverMap. This includes negative degrees and empty V. -/
theorem exists_higher_image_affine_class_rep
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Over W)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f).left]
    [∀ i, QuasiCompact ((D.obj i).hom ≫ k)]
    [∀ i, QuasiSeparated ((D.obj i).hom ≫ k)]
    (c : Cone D) (hc : IsLimit ((Over.forget W).mapCone c))
    [QuasiCompact (c.pt.hom ≫ k)] [QuasiSeparated (c.pt.hom ≫ k)]
    (V : S.Etale) [IsAffine V.left]
    (x : (higherDirectImage Λ (c.pt.hom ≫ k) q
      (((c.pt.hom)^*[ModuleCat.{u + 1} Λ]).obj G)).obj.obj (op V)) :
    ∃ (i : I) (y : (higherDirectImage Λ ((D.obj i).hom ≫ k) q
      ((((D.obj i).hom)^*[ModuleCat.{u + 1} Λ]).obj G)).obj.obj (op V)),
      ((higherDirectImageOverMap Λ k G q (c.π.app i)).hom.app (op V)) y = x := by
  classical
  let t := fun {U V : Over W} (φ : U ⟶ V) ↦ higherDirectImageOverMap Λ k G q φ
  obtain ⟨hid, hcomp⟩ := higher_image_over_transition_coherence Λ k G q
  let K : Iᵒᵖ ⥤ Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
    { obj := fun i ↦ higherDirectImage Λ ((D.obj i.unop).hom ≫ k) q
        ((((D.obj i.unop).hom)^*[ModuleCat.{u + 1} Λ]).obj G)
      map := fun f ↦ t (D.map f.unop)
      map_id := fun i ↦ by
        change t (D.map (𝟙 i.unop)) = 𝟙 _
        rw [D.map_id]
        exact hid _
      map_comp := fun f g ↦ by
        change t (D.map (g.unop ≫ f.unop)) = t (D.map f.unop) ≫ t (D.map g.unop)
        rw [D.map_comp]
        exact hcomp _ _ }
  let B : Cocone K :=
    { pt := higherDirectImage Λ (c.pt.hom ≫ k) q
        (((c.pt.hom)^*[ModuleCat.{u + 1} Λ]).obj G)
      ι :=
        { app := fun i ↦ t (c.π.app i.unop)
          naturality := fun i j f ↦ by
            change t (D.map f.unop) ≫ t (c.π.app j.unop) = t (c.π.app i.unop) ≫ 𝟙 _
            rw [← hcomp, c.w, Category.comp_id] } }
  let ψ := colimit.desc K B
  -- Eventual vanishing at stages proves injectivity of the comparison on the affine basis.
  have hmono (U : S.Etale) [IsAffine U.left] : Mono (ψ.hom.app (op U)) := by
    apply (ModuleCat.mono_iff_injective _).2
    apply (injective_iff_map_eq_zero _).2
    intro z hz
    obtain ⟨i, y, hy⟩ := etale_section_colimit_representative S Λ U Iᵒᵖ K
      (colimit.cocone K) (colimit.isColimit K) z
    have hψ : (ψ.hom.app (op U)) (((colimit.ι K i).hom.app (op U)) y) =
        ((B.ι.app i).hom.app (op U)) y := by
      exact congrArg (fun a ↦ (a.hom.app (op U)) y) (colimit.ι_desc B i)
    rw [← hy] at hz
    change (ψ.hom.app (op U)) (((colimit.ι K i).hom.app (op U)) y) = 0 at hz
    rw [hψ] at hz
    obtain ⟨j, f, hf⟩ := exists_higher_image_affine_class_eq_zero Λ k G q D c hc U
      i.unop y hz
    have hw := congrArg (fun a ↦ (a.hom.app (op U)) y) (colimit.w K f.op)
    change ((colimit.ι K (op j)).hom.app (op U))
      (((higherDirectImageOverMap Λ k G q (D.map f)).hom.app (op U)) y) =
        ((colimit.ι K i).hom.app (op U)) y at hw
    rw [hf, map_zero] at hw
    exact hy.symm.trans hw.symm
  -- Restriction to the dense affine etale site reflects monomorphisms.
  let R := (Scheme.AffineEtale.Spec S).sheafPushforwardContinuous
    (ModuleCat.{u + 1} Λ) (Scheme.AffineEtale.topology S) S.smallEtaleTopology
  have : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
    ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}
  have : R.IsEquivalence :=
    Functor.isEquivalence_of_isOneHypercoverDense.{u} (Scheme.AffineEtale.Spec S)
      (Scheme.AffineEtale.topology S) S.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let P := sheafToPresheaf (Scheme.AffineEtale.topology S) (ModuleCat.{u + 1} Λ)
  have : Mono (P.map (R.map ψ)) := by
    have hm : ∀ U, Mono ((P.map (R.map ψ)).app U) := by
      intro U
      have : IsAffine ((Scheme.AffineEtale.Spec S).obj U.unop).left := by
        rw [Scheme.AffineEtale.Spec_obj_left]
        infer_instance
      exact hmono ((Scheme.AffineEtale.Spec S).obj U.unop)
    exact NatTrans.mono_of_mono_app _
  have : Mono (R.map ψ) :=
    @Functor.mono_of_mono_map _ _ _ _ P
      (Functor.reflectsMonomorphisms_of_faithful P) _ _ _ inferInstance
  have : Mono ψ := @Functor.mono_of_mono_map _ _ _ _ R
    (Functor.reflectsMonomorphisms_of_faithful R) _ _ _ inferInstance
  have : Epi ψ := epi_higher_image_colimit_comparison Λ k G q D c hc K
    (fun _ ↦ Iso.refl _) B (Iso.refl _) (fun _ ↦ by
      simp only [B, t, Iso.refl_hom, Iso.refl_inv, Category.id_comp]
      exact (Category.comp_id _).symm)
  have : IsIso ψ := isIso_of_mono_of_epi ψ
  have : IsIso ((colimit.isColimit K).desc B) := ‹IsIso ψ›
  have hB : IsColimit B := (colimit.isColimit K).ofPointIso
  obtain ⟨i, y, hy⟩ := etale_section_colimit_representative S Λ V Iᵒᵖ K B hB x
  exact ⟨i.unop, y, hy⟩

end AlgebraicGeometry.Etale
