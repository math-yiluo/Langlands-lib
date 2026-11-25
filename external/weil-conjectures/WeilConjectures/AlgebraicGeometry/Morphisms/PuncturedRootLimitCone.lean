/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization


public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMapExtension
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Auxiliary limit statements for punctured root charts

## References

* Stacks Project, Tags 0BSK, 05N9 and 01YW
* Stacks Project, Tag 03Q9
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The pointed etale neighbourhoods give a ring-colimit presentation over the base. -/
theorem pointed_etale_ring_colimit
    (R : CommRingCat.{u})
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (barY : Spec (.of Ω) ⟶ Spec R)
    (y : Spec R) (hy : ∀ x : Spec (.of Ω), barY x = y)
    (b : R ⟶ strictHenselization barY)
    (hb : Spec.map b = strictLocalizationToBase barY) :
    ∃ (I : Type u) (cat : Category.{u} I), letI := cat
      ∃ (_ : IsCofiltered I) (F : Iᵒᵖ ⥤ CommRingCat.{u}) (c : Cocone F)
        (a : (Functor.const Iᵒᵖ).obj R ⟶ F)
        (e : c.pt ≅ strictHenselization barY),
        Nonempty (IsColimit c) ∧
        (∀ j, a.app j ≫ c.ι.app j ≫ e.hom = b) ∧
        ∀ j, Etale (Spec.map (a.app j)) ∧
          ∃ z : Spec (F.obj j), (Spec.map (a.app j)) z = y := by
  classical
  let I := SmallModel.{u} (strictHenselizationNeighbourhoods barY)
  let F := strictHenselizationAffineDiagram barY
  let c := smallStrictHenselizationCocone barY
  let N := (equivSmallModel.{u} (strictHenselizationNeighbourhoods barY)).inverse
  let k (j : I) : Spec (F.obj (Opposite.op j)) ⟶ Spec R :=
    Spec.map (ΓSpecIso (N.obj j).1.left.unop).inv ≫
      ((AffineEtale.Spec (Spec R)).obj (N.obj j).1).hom
  let a : (Functor.const Iᵒᵖ).obj R ⟶ F :=
    { app := fun j ↦ Spec.preimage (k j.unop)
      naturality := by
        intro i j h
        apply Spec.map_injective
        change Spec.map (Spec.preimage (k j.unop)) =
          Spec.map (Spec.preimage (k i.unop) ≫ F.map h)
        simp only [Spec.map_comp, Spec.map_preimage]
        let g := (N.map h.unop).1.left.unop
        have hg := congrArg Spec.map (ΓSpecIso_inv_naturality g)
        simp only [Spec.map_comp] at hg
        have hw := (N.map h.unop).1.w
        change Spec.map (ΓSpecIso (N.obj j.unop).1.left.unop).inv ≫
          ((AffineEtale.Spec (Spec R)).obj (N.obj j.unop).1).hom =
            Spec.map (Spec.map g).appTop ≫
              Spec.map (ΓSpecIso (N.obj i.unop).1.left.unop).inv ≫
                ((AffineEtale.Spec (Spec R)).obj (N.obj i.unop).1).hom
        rw [← Category.assoc, ← hg, Category.assoc]
        congr 1
        simpa using hw.symm }
  refine ⟨I, inferInstance, (strictHenselizationAffineProperties barY).2.1, F, c, a,
    Iso.refl _, ⟨isColimitSmallStrictHenselizationCocone barY⟩, ?_, ?_⟩
  · intro j
    apply Spec.map_injective
    change Spec.map (Spec.preimage (k j.unop) ≫ c.ι.app j ≫ 𝟙 _) = Spec.map b
    simp only [Category.comp_id, Spec.map_comp, Spec.map_preimage]
    change (strictHenselizationAffineCone barY).π.app (Opposite.op j) ≫ k j.unop = Spec.map b
    rw [hb]
    exact strictHenselizationStructuralMap_eq barY j.unop
  · intro j
    have hk : Spec.map (a.app j) = k j.unop := Spec.map_preimage _
    rw [hk]
    have : Etale (k j.unop) := by
      dsimp [k]
      infer_instance
    refine ⟨this, ?_⟩
    let lift := (N.obj j.unop).2
    let e := Scheme.Spec.mapIso (ΓSpecIso (N.obj j.unop).1.left.unop).op
    let x : Spec (.of Ω) := ⟨⊥, Ideal.isPrime_bot⟩
    refine ⟨(lift.left ≫ e.hom) x, ?_⟩
    have hw := Over.w lift
    have he : e.hom ≫ Spec.map (ΓSpecIso (N.obj j.unop).1.left.unop).inv = 𝟙 _ := by
      exact e.hom_inv_id
    have hh : (lift.left ≫ e.hom) ≫ k j.unop = barY := by
      dsimp [k]
      rw [Category.assoc, ← Category.assoc e.hom, he]
      simpa using hw
    change (k j.unop) ((lift.left ≫ e.hom) x) = y
    exact (congrArg (fun m ↦ m x) hh).trans (hy x)

end AlgebraicGeometry.Scheme
