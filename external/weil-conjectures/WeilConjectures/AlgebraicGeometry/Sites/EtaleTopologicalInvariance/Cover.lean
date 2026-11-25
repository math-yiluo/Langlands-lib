/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Collecting étale neighbourhoods into a single affine étale scheme

Given a morphism `f : X ⟶ Y` and an étale `g : U ⟶ X` with `U` quasi-compact, suppose that
every point `u : U` lies in the image of some `X`-morphism `W ×_Y X ⟶ U` with `W ⟶ Y` étale and
`W` affine. Then, taking a finite disjoint union of such `W`, there is a single affine étale
`W ⟶ Y` and a surjective `X`-morphism `W ×_Y X ⟶ U`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {X Y U : Scheme.{u}} (f : X ⟶ Y) (g : U ⟶ X) [Etale g]

omit [Etale g] in
/-- A finite family of `X`-morphisms `Wᵢ ×_Y X ⟶ U` with jointly surjective images can be
assembled into a single `X`-morphism `(∐ Wᵢ) ×_Y X ⟶ U` which is surjective. -/
lemma exists_sigma_hom_of_forall {n : ℕ} (W : Fin n → Scheme.{u}) (p : ∀ i, W i ⟶ Y)
    (h : ∀ i, pullback (p i) f ⟶ U) (hg : ∀ i, h i ≫ g = pullback.snd (p i) f)
    (hsurj : ∀ u : U, ∃ i, u ∈ Set.range (h i)) :
    ∃ h' : pullback (Sigma.desc p) f ⟶ U, h' ≫ g = pullback.snd (Sigma.desc p) f ∧
      Function.Surjective h' := by
  let p' : ∐ W ⟶ Y := Sigma.desc p
  let q : pullback p' f ⟶ ∐ W := pullback.fst p' f
  -- the components `(∐ W) ×_Y X ⊇ Wᵢ ×_Y X`
  let e (i : Fin n) : pullback q (Sigma.ι W i) ≅ pullback (p i) f :=
    pullbackSymmetry _ _ ≪≫ pullbackRightPullbackFstIso p' f (Sigma.ι W i) ≪≫
      pullback.congrHom (by simp [p']) rfl
  have he (i : Fin n) : (e i).hom ≫ pullback.snd (p i) f = pullback.fst q (Sigma.ι W i) ≫
      pullback.snd p' f := by
    simp only [e, q, Iso.trans_hom, Category.assoc, pullback.congrHom_hom, pullback.lift_snd,
      pullbackRightPullbackFstIso_hom_snd, Category.comp_id, pullbackSymmetry_hom_comp_snd_assoc]
  have hiso : IsIso (Sigma.desc ((fun _ ↦ pullback.fst _ _) :
      (i : Fin n) → pullback q (Sigma.ι W i) ⟶ _)) :=
    FinitaryPreExtensive.isIso_sigmaDesc_fst (Sigma.ι W) q
      (by rw [show Sigma.desc (Sigma.ι W) = 𝟙 _ from Sigma.hom_ext _ _ (by simp)]; infer_instance)
  refine ⟨inv (Sigma.desc fun i ↦ pullback.fst q (Sigma.ι W i)) ≫
    Sigma.desc (fun i ↦ (e i).hom ≫ h i), ?_, ?_⟩
  · rw [Category.assoc, IsIso.inv_comp_eq]
    apply Sigma.hom_ext
    intro i
    simp only [colimit.ι_desc_assoc, Cofan.mk_ι_app, Category.assoc, hg, he]
    rfl
  · intro u
    obtain ⟨i, x, rfl⟩ := hsurj u
    refine ⟨(Sigma.desc fun i ↦ pullback.fst q (Sigma.ι W i))
      (Sigma.ι (fun i ↦ pullback q (Sigma.ι W i)) i ((e i).inv x)), ?_⟩
    have : Sigma.ι (fun i ↦ pullback q (Sigma.ι W i)) i ≫
        (Sigma.desc fun i ↦ pullback.fst q (Sigma.ι W i)) ≫
        inv (Sigma.desc fun i ↦ pullback.fst q (Sigma.ι W i)) ≫
        Sigma.desc (fun i ↦ (e i).hom ≫ h i) = (e i).hom ≫ h i := by
      rw [IsIso.hom_inv_id_assoc, colimit.ι_desc]
      rfl
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, this, Scheme.Hom.comp_apply,
      ← Scheme.Hom.comp_apply (e i).inv (e i).hom, Iso.inv_hom_id]
    rfl

/-- If every point of the quasi-compact scheme `U` lies in the image of an `X`-morphism
`W ×_Y X ⟶ U` for some affine étale `W ⟶ Y`, then there is a single affine étale `W ⟶ Y` and
a surjective `X`-morphism `W ×_Y X ⟶ U`. -/
lemma exists_etale_surjective_of_forall [CompactSpace U]
    (H : ∀ u : U, ∃ (W : Scheme.{u}) (_ : IsAffine W) (p : W ⟶ Y) (_ : Etale p)
      (h : pullback p f ⟶ U), h ≫ g = pullback.snd p f ∧ u ∈ Set.range h) :
    ∃ (W : Scheme.{u}) (_ : IsAffine W) (p : W ⟶ Y) (_ : Etale p) (h : pullback p f ⟶ U),
      h ≫ g = pullback.snd p f ∧ Function.Surjective h := by
  choose W hW p hp h hhg hu using H
  have hopen (u : U) : IsOpen (Set.range (h u)) := by
    have : Etale (h u ≫ g) := by rw [hhg]; infer_instance
    have : Etale (h u) := Etale.of_comp (h u) g
    exact (h u).isOpenMap.isOpen_range
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun u ↦ Set.range (h u)) hopen
    (fun u _ ↦ Set.mem_iUnion.mpr ⟨u, hu u⟩)
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin t
  obtain ⟨h', hh'g, hh'⟩ := exists_sigma_hom_of_forall f g (fun i ↦ W (e.symm i))
    (fun i ↦ p (e.symm i)) (fun i ↦ h (e.symm i)) (fun i ↦ hhg _) (fun u ↦ by
      obtain ⟨v, hv, hu⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ u))
      exact ⟨e ⟨v, hv⟩, by rw [Equiv.symm_apply_apply]; exact hu⟩)
  refine ⟨∐ fun i ↦ W (e.symm i), inferInstance, Sigma.desc fun i ↦ p (e.symm i), ?_, h', hh'g,
    hh'⟩
  exact IsZariskiLocalAtSource.sigmaDesc fun i ↦ hp _

end AlgebraicGeometry
