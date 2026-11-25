/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectionRestriction.ProjectionExactTensorCore
import all WeilConjectures.AlgebraicGeometry.ProjectionRestriction.ProjectionExactTensorCore
import all WeilConjectures.AlgebraicGeometry.ProjectionRestriction.RingedProjectionTensorShifts

/-! Signed shift verification for exact tensor descent.

## References

* Stacks 07A4 and 0FNH
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.privateModule false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Scheme.ProjectionRestriction

variable {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
  [EssentiallySmall.{u + 1} C] [EssentiallySmall.{u + 1} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {R : Sheaf J CommRingCat.{u + 1}} {S : Sheaf K CommRingCat.{u + 1}}

namespace ExactTensor
attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [local semireducible] ObjectProperty.hasShift ObjectProperty.commShiftι
attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors

-- Elaborating the representative diagram involves many large composite functor expressions.
private theorem fixedSecond_resolving (o : Data R S)
    (a : TensorModel R) (b : TensorModel S) [sa : TensorShifts a] [sb : TensorShifts b]
    (mu : OrdinaryTensor o) (t : TensorComparison o.pullback o.leftModel a b mu.iso)
    (Q : (resolving R).FullSubcategory) :
    NatTrans.CommShift
      (fixedSecond a.functor b.functor o.left t.comparison.hom (DerivedCategory.Q.obj Q.obj))
      ℤ := by
  let := resolving_stable a
  let := resolving_stable b
  let := resolving_essSurj (R := R)
  let := o.coproducts
  let i := (resolving R).ι
  let q := i ⋙ DerivedCategory.Q
  let LC := o.pullback.mapHomologicalComplex (.up ℤ)
  let j := i ⋙ LC
  let TR₀ := ((tensor R).map₂CochainComplex).obj Q.obj
  let TR₁ := (Functor.curry.obj a.functor).obj (DerivedCategory.Q.obj Q.obj)
  let TS₀ := ((tensor S).map₂CochainComplex).obj (LC.obj Q.obj)
  let TS₂ := (Functor.curry.obj b.functor).obj (o.left.obj (DerivedCategory.Q.obj Q.obj))
  let TS₄ := (Functor.curry.obj b.functor).obj (DerivedCategory.Q.obj (LC.obj Q.obj))
  let τ := fixedSecond a.functor b.functor o.left t.comparison.hom (DerivedCategory.Q.obj Q.obj)
  let eps := o.factors
  let c := chainComparison o mu
  let chi : TR₀ ⋙ LC ≅ LC ⋙ TS₀ := c.app Q.obj
  have : NatTrans.CommShift chi.hom ℤ := by
    exact HomologicalComplex.commShift_mapBifunctorComparisonNatTrans_app
      (ordinaryComparison o mu).hom Q.obj
  let beta : TS₂ ≅ TS₄ :=
    (Functor.curry.obj b.functor).mapIso (eps.app Q.obj)
  have : NatTrans.CommShift beta.hom ℤ := by
    dsimp only [beta, Functor.mapIso_hom, Iso.app_hom]
    infer_instance
  let rR := Functor.associator i TR₀ DerivedCategory.Q ≪≫ representativeSecond a Q
  have : NatTrans.CommShift rR.hom ℤ := by
    have := representativeSecond_shift a Q
    dsimp [rR]
    infer_instance
  let Q' : (resolving S).FullSubcategory := ⟨LC.obj Q.obj, t.preserves _ Q.property⟩
  let rS := representativeSecond b Q' ≪≫
    Functor.associator (resolving S).ι DerivedCategory.Q TS₄
  have : NatTrans.CommShift rS.hom ℤ := by
    have := representativeSecond_shift b Q'
    dsimp [rS]
    infer_instance
  let hj : ∀ X, resolving S (j.obj X) := fun X ↦ t.preserves X.obj X.property
  let s := reindexIso (resolving S) (TS₀ ⋙ DerivedCategory.Q)
    (DerivedCategory.Q ⋙ TS₄) rS j hj
  have : NatTrans.CommShift s.hom ℤ := reindexIso_shift _ _ _ _ _ _
  let ee : q ⋙ o.left ≅ j ⋙ DerivedCategory.Q :=
    Functor.associator i DerivedCategory.Q o.left ≪≫
      Functor.isoWhiskerLeft i eps ≪≫ (Functor.associator i LC DerivedCategory.Q).symm
  have : NatTrans.CommShift ee.hom ℤ := by dsimp [ee]; infer_instance
  let r₁ := Functor.isoWhiskerRight rR o.left ≪≫ Functor.associator q TR₁ o.left
  let r₂ := (Functor.associator q o.left TS₂).symm ≪≫
    Functor.isoWhiskerRight ee TS₂ ≪≫ Functor.isoWhiskerLeft (j ⋙ DerivedCategory.Q) beta ≪≫
      Functor.associator j DerivedCategory.Q TS₄
  let w₀ := Functor.associator (i ⋙ TR₀) DerivedCategory.Q o.left ≪≫
    Functor.isoWhiskerLeft (i ⋙ TR₀) eps ≪≫
    (Functor.associator (i ⋙ TR₀) LC DerivedCategory.Q).symm
  have : NatTrans.CommShift w₀.hom ℤ := by dsimp [w₀]; infer_instance
  let w₁ := Functor.isoWhiskerRight (Functor.associator i TR₀ LC) DerivedCategory.Q ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft i chi) DerivedCategory.Q ≪≫
    Functor.isoWhiskerRight (Functor.associator i LC TS₀).symm DerivedCategory.Q
  have : NatTrans.CommShift w₁.hom ℤ := by dsimp [w₁]; infer_instance
  let w₂ := Functor.associator j TS₀ DerivedCategory.Q ≪≫ s
  have : NatTrans.CommShift w₂.hom ℤ := by dsimp [w₂]; infer_instance
  let w := w₀ ≪≫ w₁ ≪≫ w₂
  have : NatTrans.CommShift r₁.hom ℤ := by dsimp [r₁]; infer_instance
  have : NatTrans.CommShift r₂.hom ℤ := by dsimp [r₂]; infer_instance
  have : NatTrans.CommShift w.hom ℤ := by dsimp [w]; infer_instance
  have hh : NatTrans.CommShift (Functor.whiskerLeft q τ) ℤ := by
    apply shift_of_diagram q o.left TR₁ TS₂ τ _ _ r₁ r₂ w.hom
    apply NatTrans.ext
    funext A
    have hb : TS₂.map (eps.hom.app A.obj) ≫
        beta.hom.app (DerivedCategory.Q.obj (LC.obj A.obj)) =
        b.functor.map (Prod.mkHom (eps.hom.app Q.obj) (eps.hom.app A.obj)) := by
      change b.functor.map (Prod.mkHom (𝟙 _) _) ≫
        b.functor.map (Prod.mkHom _ (𝟙 _)) = _
      rw [← b.functor.map_comp]
      congr 1
      ext <;> simp
    have hn := representative_square o a b mu t Q.obj A.obj Q.property A.property
    simp only [Functor.comp_obj, ObjectProperty.ι_obj, Functor.curry_obj_obj_obj,
      representativeSecond, Functor.isoWhiskerRight_trans, Iso.trans_assoc, Iso.trans_hom,
      Functor.isoWhiskerRight_hom, fixedSecond, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
      Iso.app_hom, Category.assoc, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.associator_hom_app, CategoryTheory.Functor.map_id,
      NatIso.ofComponents_hom_app, Functor.whiskerLeft_app, Functor.associator_inv_app,
      Functor.curry_obj_obj_map, Bifunctor.map_id, Category.comp_id,
      Category.id_comp, reindexIso_hom_app, i, TR₀, j, TS₄, q, TR₁, r₁, rR, TS₂, τ, r₂, ee, eps,
      beta, w, TS₀, w₁, chi, c, w₂, s, rS, Q', w₀]
    erw [Category.id_comp, Category.id_comp, hb]
    exact hn
  exact NatTrans.CommShift.of_whiskerLeft τ q
    (fun X ↦ ⟨q.objPreimage X, (q.objObjPreimageIso X).inv, inferInstance⟩)

private theorem fixedSecond_global (o : Data R S)
    (a : TensorModel R) (b : TensorModel S) [sa : TensorShifts a] [sb : TensorShifts b]
    (mu : OrdinaryTensor o) (t : TensorComparison o.pullback o.leftModel a b mu.iso)
    (M : Der R) : NatTrans.CommShift
      (fixedSecond a.functor b.functor o.left t.comparison.hom M) ℤ := by
  let := resolving_essSurj (R := R)
  let q := (resolving R).ι ⋙ DerivedCategory.Q
  let A := q.objPreimage M
  let e := q.objObjPreimageIso M
  have : NatTrans.CommShift
      (fixedSecond a.functor b.functor o.left t.comparison.hom (q.obj A)) ℤ :=
    fixedSecond_resolving o a b mu t A
  let e₁ := Functor.isoWhiskerRight ((Functor.curry.obj a.functor).mapIso e) o.left
  let e₂ := Functor.isoWhiskerLeft o.left
    ((Functor.curry.obj b.functor).mapIso (o.left.mapIso e))
  have : NatTrans.CommShift e₁.hom ℤ := by dsimp [e₁]; infer_instance
  have : NatTrans.CommShift e₂.hom ℤ := by dsimp [e₂]; infer_instance
  have ht : fixedSecond a.functor b.functor o.left t.comparison.hom M =
      e₁.inv ≫ fixedSecond a.functor b.functor o.left t.comparison.hom (q.obj A) ≫
        e₂.hom := by
    apply (cancel_epi e₁.hom).1
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    apply NatTrans.ext
    funext N
    exact (fixedFirst a.functor b.functor o.left t.comparison.hom N).naturality e.hom
  rw [ht]
  infer_instance

/-- The second signed shift square for the descended tensor comparison. -/
theorem exactTensorComparison_shiftSecond (L : Mod R ⥤ Mod S) [L.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesColimitsOfSize.{0, 0} L]
    (a : TensorModel R) (b : TensorModel S) [sa : TensorShifts a] [sb : TensorShifts b]
    (mu : ∀ M N : Mod R, L.obj (((tensor R).obj M).obj N) ≅
      ((tensor S).obj (L.obj M)).obj (L.obj N))
    (hn : ∀ {M M' N N' : Mod R} (f : M ⟶ M') (g : N ⟶ N'),
      L.map (((tensor R).map f).app N ≫ ((tensor R).obj M').map g) ≫
        (mu M' N').hom =
      (mu M N).hom ≫ (((tensor S).map (L.map f)).app (L.obj N) ≫
        ((tensor S).obj (L.obj M')).map (L.map g)))
    (t : TensorComparison L (exactTensorModel L) a b mu) :
    ∀ (M N : Der R) (n : ℤ),
      t.comparison.hom.app (M, N⟦n⟧) ≫
        b.functor.map (Prod.mkHom (𝟙 _) ((L.mapDerivedCategory.commShiftIso n).hom.app N)) ≫
        (((Functor.curry.obj b.functor).obj (L.mapDerivedCategory.obj M)).commShiftIso n).hom.app
          (L.mapDerivedCategory.obj N) =
      L.mapDerivedCategory.map
          ((((Functor.curry.obj a.functor).obj M).commShiftIso n).hom.app N) ≫
        (L.mapDerivedCategory.commShiftIso n).hom.app (a.functor.obj (M, N)) ≫
        (shiftFunctor (Der S) n).map (t.comparison.hom.app (M, N)) := by
  let o : Data R S := ⟨L⟩
  let m : OrdinaryTensor o := ⟨mu, hn⟩
  intro M N n
  have := fixedSecond_global o a b m t M
  convert (NatTrans.shift_app_comm
    (fixedSecond a.functor b.functor o.left t.comparison.hom M) n N).symm using 1
  all_goals simp only [Functor.commShiftIso_comp_hom_app, fixedSecond, Functor.comp_obj,
    Functor.curry_obj_obj_map, Category.assoc]
  all_goals rfl

end ExactTensor
end AlgebraicGeometry.Scheme.ProjectionRestriction
