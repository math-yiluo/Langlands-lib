/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition

/-! # Compatible stalk ring coordinates for an open restricted pullback square

Source: Stacks Project, Tag 0098, and Mathlib's open stalk-map identities.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
namespace AlgebraicGeometry
open SingleComplexBaseChange
private theorem open_stalk_square
    {X X' : Scheme.{u}} (k : X' ⟶ X)
    (U : X.Opens) (U' : X'.Opens) (j : U'.toScheme ⟶ U.toScheme)
    (hj : j ≫ U.ι = U'.ι ≫ k) (z : U'.toScheme)
    (hx : (j z).val = k z.val) :
    (U.stalkIso (j z)).hom ≫ (X.presheaf.stalkCongr (.of_eq hx)).hom ≫
        k.stalkMap z.val = j.stalkMap z ≫ (U'.stalkIso z).hom := by
  apply (cancel_mono (U'.stalkIso z).inv).1
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have h := Scheme.Hom.stalkMap_congr_hom _ _ hj z
  rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp] at h
  erw [Scheme.Opens.stalkIso_inv, ← h, ← Scheme.Opens.stalkIso_inv]
  simp

private theorem stalkIso_congr
    {Y : Scheme.{u}} (U : Y.Opens) {x y : U.toScheme} (h : x = y) :
    (U.toScheme.presheaf.stalkCongr (.of_eq h)).hom ≫ (U.stalkIso y).hom =
      (U.stalkIso x).hom ≫
        (Y.presheaf.stalkCongr (.of_eq (congrArg Subtype.val h))).hom := by
  subst y
  simp [TopCat.Presheaf.stalkCongr]

/-- The four stalk rings of a restricted pullback square have compatible
coordinates in the ambient square, pinned at the input and output points.

Proof: let hx be the equality (j z).val = g' z.val induced by hj. Let hs
be the induced base-point equality and hs' the point equality for f' restricted
to V'. Compose each open-inclusion stalk isomorphism with the corresponding
stalkCongr to get the four ring equivalences. For f, apply the stalk-map identity
of its restriction square, followed by stalk-map naturality along hx. For g,
first use the point equality supplied by sq0, commute the base open stalk iso
past that stalkCongr, and apply the restriction square for g and naturality
along hs'. Composing stalkSpecializes proves both base-ring compatibilities.
The square hj proves the A-to-C compatibility, and the restriction square of
f' proves the B-to-C compatibility. The two defining restrictions of tensorMap
identify these latter maps with the two displayed tensor algebra maps.
The input and output normalizations follow directly from their construction.
This uses no derived objects, flatness or nonzero-ring assumptions.
Source: Mathlib Scheme.Opens.stalkIso, Scheme.Hom.stalkMap_comp,
Scheme.Hom.stalkMap_congr_hom and stalkMap_congr; Stacks Project, Tag 0098.
(blueprint: lem-pc-open-ordinary-tensor-stalk-ring-coordinates). -/
theorem exists_openOrdinaryTensor_stalk_ring_coordinates
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    (V : S.Opens) (V' : S'.Opens) (hV' : V' ≤ g ⁻¹ᵁ V)
    (j : (f' ⁻¹ᵁ V').toScheme ⟶ (f ⁻¹ᵁ V).toScheme)
    (hj : j ≫ (f ⁻¹ᵁ V).ι = (f' ⁻¹ᵁ V').ι ≫ g')
    (sq₀ : IsPullback j (f' ∣_ V') (f ∣_ V) (g.resLE V V' hV'))
    (z : (f' ⁻¹ᵁ V').toScheme) :
    let R₀ := R (f ∣_ V) j z
    let A₀ := A j z
    let B₀ := B (f' ∣_ V') z
    let C₀ := C z
    let R₁ := R f g' z.val
    let A₁ := A g' z.val
    let B₁ := B f' z.val
    let C₁ := C z.val
    letI := leftAlgebra (f ∣_ V) j z
    letI := rightAlgebra (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀ z
    letI := (tensorMap (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀ z).toAlgebra
    letI := leftAlgebra f g' z.val
    letI := rightAlgebra f f' g g' sq z.val
    letI := (tensorMap f f' g g' sq z.val).toAlgebra
    ∃ (eR : R₀ ≃+* R₁) (eA : A₀ ≃+* A₁) (eB : B₀ ≃+* B₁) (eC : C₀ ≃+* C₁),
      eA.toRingHom.comp (algebraMap R₀ A₀) = (algebraMap R₁ A₁).comp eR.toRingHom ∧
      eB.toRingHom.comp (algebraMap R₀ B₀) = (algebraMap R₁ B₁).comp eR.toRingHom ∧
      eC.toRingHom.comp ((algebraMap (A₀ ⊗[R₀] B₀) C₀).comp
        (algebraMap A₀ (A₀ ⊗[R₀] B₀))) =
        ((algebraMap (A₁ ⊗[R₁] B₁) C₁).comp
          (algebraMap A₁ (A₁ ⊗[R₁] B₁))).comp eA.toRingHom ∧
      eC.toRingHom.comp ((algebraMap (A₀ ⊗[R₀] B₀) C₀).comp
        Algebra.TensorProduct.includeRight.toRingHom) =
        ((algebraMap (A₁ ⊗[R₁] B₁) C₁).comp
          Algebra.TensorProduct.includeRight.toRingHom).comp eB.toRingHom ∧
      eA.toRingHom =
        (((f ⁻¹ᵁ V).stalkIso (j z)) ≪≫
          X.presheaf.stalkCongr (.of_eq
            (congrArg (fun k : (f' ⁻¹ᵁ V').toScheme ⟶ X => k z) hj))).hom.hom ∧
      eC.toRingHom = ((f' ⁻¹ᵁ V').stalkIso z).hom.hom := by
  let := leftAlgebra (f ∣_ V) j z
  let := rightAlgebra (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀ z
  let := (tensorMap (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀ z).toAlgebra
  let := leftAlgebra f g' z.val
  let := rightAlgebra f f' g g' sq z.val
  let := (tensorMap f f' g g' sq z.val).toAlgebra
  have hx : (j z).val = g' z.val :=
    congrArg (fun k : (f' ⁻¹ᵁ V').toScheme ⟶ X => k z) hj
  have hs : ((f ∣_ V) (j z)).val = f (g' z.val) := by
    simpa using congrArg f hx
  have hs' : ((f' ∣_ V') z).val = f' z.val := by simp
  let a : A j z ≅ A g' z.val :=
    (f ⁻¹ᵁ V).stalkIso (j z) ≪≫ X.presheaf.stalkCongr (.of_eq hx)
  let r : R (f ∣_ V) j z ≅ R f g' z.val :=
    V.stalkIso ((f ∣_ V) (j z)) ≪≫ S.presheaf.stalkCongr (.of_eq hs)
  let b : B (f' ∣_ V') z ≅ B f' z.val :=
    V'.stalkIso ((f' ∣_ V') z) ≪≫ S'.presheaf.stalkCongr (.of_eq hs')
  let c : C z ≅ C z.val := (f' ⁻¹ᵁ V').stalkIso z
  let eA := a.commRingCatIsoToRingEquiv
  let eR := r.commRingCatIsoToRingEquiv
  let eB := b.commRingCatIsoToRingEquiv
  let eC := c.commRingCatIsoToRingEquiv
  have hRA : (f ∣_ V).stalkMap (j z) ≫ a.hom = r.hom ≫ f.stalkMap (g' z.val) := by
    have hs₀ : ((f ∣_ V) (j z)).val = f (j z).val := by simp
    have h₀ := open_stalk_square f V (f ⁻¹ᵁ V) (f ∣_ V)
      (morphismRestrict_ι f V) (j z) hs₀
    have h₁ := Scheme.Hom.stalkMap_congr f f rfl (j z).val (g' z.val) hx
    dsimp only [a, r, Iso.trans_hom]
    erw [← Category.assoc, ← h₀, Category.assoc, Category.assoc, h₁]
    simp only [TopCat.Presheaf.stalkCongr_hom, Category.assoc,
      TopCat.Presheaf.stalkSpecializes_comp_assoc]
  have hRB : ((V.toScheme.presheaf.stalkCongr (.of_eq
      (congrArg (fun k : (f' ⁻¹ᵁ V').toScheme ⟶ V.toScheme => k z) sq₀.w))).hom ≫
      (g.resLE V V' hV').stalkMap ((f' ∣_ V') z)) ≫ b.hom =
      r.hom ≫ (S.presheaf.stalkCongr (.of_eq
        (congrArg (fun k : X' ⟶ S => k z.val) sq.w))).hom ≫
        g.stalkMap (f' z.val) := by
    have hp : (f ∣_ V) (j z) = (g.resLE V V' hV') ((f' ∣_ V') z) :=
      congrArg (fun k : (f' ⁻¹ᵁ V').toScheme ⟶ V.toScheme => k z) sq₀.w
    have hg : ((g.resLE V V' hV') ((f' ∣_ V') z)).val =
        g ((f' ∣_ V') z).val := by simp
    have h₀ := open_stalk_square g V V' (g.resLE V V' hV')
      (Scheme.Hom.resLE_comp_ι g hV') ((f' ∣_ V') z) hg
    have h₁ := Scheme.Hom.stalkMap_congr g g rfl ((f' ∣_ V') z).val (f' z.val) hs'
    have h₂ := stalkIso_congr V hp
    dsimp only [b, r, Iso.trans_hom]
    erw [Category.assoc, ← Category.assoc ((g.resLE V V' hV').stalkMap _), ← h₀]
    simp only [Category.assoc]
    erw [h₁, ← Category.assoc _ (V.stalkIso _).hom, h₂]
    simp only [TopCat.Presheaf.stalkCongr_hom, Category.assoc,
      TopCat.Presheaf.stalkSpecializes_comp_assoc]
  have hCA := open_stalk_square g' (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') j hj z hx
  have hCB := open_stalk_square f' V' (f' ⁻¹ᵁ V') (f' ∣_ V')
    (morphismRestrict_ι f' V') z hs'
  refine ⟨eR, eA, eB, eC, ?_, ?_, ?_, ?_, rfl, rfl⟩
  · exact congrArg (fun h => h.hom) hRA
  · exact congrArg (fun h => h.hom) hRB
  · have hc₀ := (Classical.choose_spec
      (exists_tensorMap (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀ z)).1
    have hc₁ := (Classical.choose_spec (exists_tensorMap f f' g g' sq z.val)).1
    change (tensorMap (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀ z).comp
      (algebraMap (A j z) ((A j z) ⊗[R (f ∣_ V) j z] (B (f' ∣_ V') z))) = _ at hc₀
    change (tensorMap f f' g g' sq z.val).comp
      (algebraMap (A g' z.val) ((A g' z.val) ⊗[R f g' z.val] (B f' z.val))) = _ at hc₁
    change eC.toRingHom.comp
      ((tensorMap (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀ z).comp
        (algebraMap (A j z) ((A j z) ⊗[R (f ∣_ V) j z] (B (f' ∣_ V') z)))) =
      ((tensorMap f f' g g' sq z.val).comp
        (algebraMap (A g' z.val) ((A g' z.val) ⊗[R f g' z.val] (B f' z.val)))).comp
          eA.toRingHom
    rw [hc₀, hc₁]
    exact congrArg (fun h => h.hom) hCA.symm
  · have hc₀ := (Classical.choose_spec
      (exists_tensorMap (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀ z)).2
    have hc₁ := (Classical.choose_spec (exists_tensorMap f f' g g' sq z.val)).2
    change (tensorMap (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀ z).comp
      Algebra.TensorProduct.includeRight.toRingHom = _ at hc₀
    change (tensorMap f f' g g' sq z.val).comp
      Algebra.TensorProduct.includeRight.toRingHom = _ at hc₁
    change eC.toRingHom.comp
      ((tensorMap (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀ z).comp
        Algebra.TensorProduct.includeRight.toRingHom) =
      ((tensorMap f f' g g' sq z.val).comp
        Algebra.TensorProduct.includeRight.toRingHom).comp eB.toRingHom
    rw [hc₀, hc₁]
    exact congrArg (fun h => h.hom) hCB.symm

end AlgebraicGeometry
