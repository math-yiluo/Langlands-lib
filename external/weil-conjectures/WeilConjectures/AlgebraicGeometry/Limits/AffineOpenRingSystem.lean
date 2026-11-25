/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Coordinate rings of an affine open over a directed inverse system

## References

* Stacks Project, Limits, Tags 01YX and 01YW
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- An affine open and its inverse images have compatible spectrum presentations over
an upper-tail coordinate-ring diagram, including its colimit. -/
theorem exists_affineOpen_ringSystem_of_isLimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (W : (D.obj (op i₀)).Opens) (hW : IsAffineOpen W) :
    ∃ (F : {i : I // i₀ ≤ i} ⥤ CommRingCat.{u})
      (e0 : W.toScheme ≅ Spec (F.obj ⟨i₀, le_rfl⟩)),
      (∀ i : {i : I // i₀ ≤ i},
        ∃ e : (D.map (homOfLE i.property).op ⁻¹ᵁ W).toScheme ≅ Spec (F.obj i),
          (D.map (homOfLE i.property).op).resLE W _ le_rfl ≫ e0.hom =
            e.hom ≫ Spec.map (F.map (homOfLE i.property))) ∧
      ∃ eL : (c.π.app (op i₀) ⁻¹ᵁ W).toScheme ≅ Spec (colimit F),
        (c.π.app (op i₀)).resLE W _ le_rfl ≫ e0.hom =
          eL.hom ≫ Spec.map (colimit.ι F ⟨i₀, le_rfl⟩) := by
  classical
  let : Nonempty I := ⟨i₀⟩
  let J := {i : I // i₀ ≤ i}
  let o : J := ⟨i₀, le_rfl⟩
  let : Nonempty J := ⟨o⟩
  let : IsDirected J (· ≤ ·) := ⟨fun i j ↦ by
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i.val j.val
    exact ⟨⟨k, i.property.trans hik⟩, hik, hjk⟩⟩
  let K : Jᵒᵖ ⥤ Over (op i₀) :=
    { obj := fun i ↦ Over.mk (homOfLE i.unop.property).op
      map := fun {i j} f ↦ Over.homMk (homOfLE (leOfHom f.unop)).op
        (Subsingleton.elim _ _)
      map_id := by intro i; apply Over.OverMorphism.ext; apply Subsingleton.elim
      map_comp := by intros; apply Over.OverMorphism.ext; apply Subsingleton.elim }
  let : K.Initial := Functor.initial_of_exists_of_isCofiltered K
    (fun i ↦ ⟨op ⟨i.left.unop, leOfHom i.hom.unop⟩,
      ⟨Over.homMk (𝟙 _) (Subsingleton.elim _ _)⟩⟩)
    (fun {_ _} f g ↦ ⟨_, 𝟙 _, by
      apply Over.OverMorphism.ext
      apply Subsingleton.elim⟩)
  let E := K ⋙ opensDiagram D (op i₀) W
  let cE : Cone E := (opensCone D c (op i₀) W).whisker K
  have hE : IsLimit cE :=
    (Functor.Initial.isLimitWhiskerEquiv K _).symm (isLimitOpensCone D c hc (op i₀) W)
  let (i : Jᵒᵖ) : IsAffine (E.obj i) := hW.preimage (D.map (homOfLE i.unop.property).op)
  let : IsAffine cE.pt := Scheme.isAffine_of_isLimit cE hE
  let F : J ⥤ CommRingCat := E.rightOp ⋙ Scheme.Γ
  let (i : J) : IsAffine (E.rightOp.obj i).unop := inferInstanceAs (IsAffine (E.obj (op i)))
  let hΓ := isColimitOfPreserves Scheme.Γ (isColimitCoconeRightOpOfCone E hE)
  let eΓ := hΓ.coconePointUniqueUpToIso (colimit.isColimit F)
  have h₀ : D.map (homOfLE o.property).op ⁻¹ᵁ W = W := by
    have : (homOfLE o.property).op = 𝟙 (op i₀) := Subsingleton.elim _ _
    rw [this, D.map_id]
    rfl
  let q : E.obj (op o) ≅ W.toScheme := (D.obj (op i₀)).isoOfEq h₀
  let e0 : W.toScheme ≅ Spec (F.obj o) := q.symm ≪≫ (E.obj (op o)).isoSpec
  refine ⟨F, e0, ?_, ?_⟩
  · intro i
    refine ⟨(E.obj (op i)).isoSpec, ?_⟩
    have hm : E.map (homOfLE (show o ≤ i from i.property)).op ≫ q.hom =
        (D.map (homOfLE i.property).op).resLE W _ le_rfl := by
      rw [← cancel_mono W.ι]
      simp only [E, Functor.comp_map, opensDiagram_map, K,
        Category.assoc, q, Scheme.isoOfEq_hom_ι, Scheme.Hom.resLE_comp_ι]
      congr 2
    dsimp [e0]
    rw [← hm, Category.assoc, Iso.hom_inv_id_assoc]
    exact (Scheme.isoSpec_hom_naturality (E.map (homOfLE i.property).op)).symm
  · let eL : cE.pt ≅ Spec (colimit F) :=
      cE.pt.isoSpec ≪≫ Scheme.Spec.mapIso eΓ.symm.op
    refine ⟨eL, ?_⟩
    have hm : cE.π.app (op o) ≫ q.hom =
        (c.π.app (op i₀)).resLE W _ le_rfl := by
      rw [← cancel_mono W.ι]
      simp [cE, K, q, o, Scheme.Hom.resLE_comp_ι]
    dsimp [e0, eL]
    rw [← hm, Category.assoc, Iso.hom_inv_id_assoc]
    rw [Category.assoc, ← Spec.map_comp]
    have hι := hΓ.comp_coconePointUniqueUpToIso_inv (colimit.isColimit F) o
    change colimit.ι F o ≫ eΓ.inv = (cE.π.app (op o)).appTop at hι
    change cE.π.app (op o) ≫ (E.obj (op o)).isoSpec.hom =
      cE.pt.isoSpec.hom ≫ Spec.map (colimit.ι F o ≫ eΓ.inv)
    rw [hι]
    exact (Scheme.isoSpec_hom_naturality (X := cE.pt) (Y := E.obj (op o))
      (cE.π.app (op o))).symm

end AlgebraicGeometry
