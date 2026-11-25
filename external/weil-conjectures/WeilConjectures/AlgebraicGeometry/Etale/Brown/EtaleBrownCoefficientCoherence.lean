/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.EtaleSystemBrownConstruction
import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleInverseTensorCoherence
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Canonical Brown coefficient projection coherence
Source: Zheng, Construction 5.15 and (5.16.2), printed pp. 34--35.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits SheafOfModules
namespace AlgebraicGeometry
attribute [instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived
-- The whiskering calculation of ExactScalarMatePasting, kept local so that the
-- proof needs only the generic mate API and no derived-localization machinery.
private theorem mate_whisker_normalized
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    {F F' : A ⥤ C} {G G' : B ⥤ D}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (t : TwoSquare F L₁ L₂ G)
    (f : F' ⟶ F) (g : G ⟶ G') :
    (mateEquiv a₁ a₂ ((t.whiskerTop f).whiskerBottom g)) =
      Functor.whiskerLeft R₁ f ≫ (mateEquiv a₁ a₂ t) ≫ Functor.whiskerRight g R₂ := by
  ext N
  simp only [mateEquiv_apply, TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
    Functor.comp_obj, Category.id_comp, Functor.map_comp, Category.assoc]
  rw [← a₂.unit_naturality_assoc]
  simp only [Functor.comp_map]
  have hg := congrArg R₂.map (g.naturality (a₁.counit.app N))
  simp only [R₂.map_comp] at hg
  rw [← reassoc_of% hg]
  simp

private theorem inverse_square_iff
    {C : Type*} [Category C] {W X Y Z : C} (i : W ≅ X) (j : Y ≅ Z)
    (f : W ⟶ Y) (g : X ⟶ Z) :
    (f ≫ j.hom = i.hom ≫ g) ↔ (i.inv ≫ f = g ≫ j.inv) := by
  constructor
  · intro h
    apply (Iso.inv_comp_eq i).mpr
    simpa only [Category.assoc] using (Iso.eq_comp_inv j).mpr h
  · intro h
    apply (Iso.eq_comp_inv j).mp
    simpa only [Category.assoc] using (Iso.inv_comp_eq i).mp h

section Mates
universe a₀ a₁ a₂ b₀ b₁ b₂ v₀ v₁ v₂ w₀ w₁ w₂
variable {A₀ : Type a₀} {A₁ : Type a₁} {A₂ : Type a₂}
  {B₀ : Type b₀} {B₁ : Type b₁} {B₂ : Type b₂}
  [Category.{v₀} A₀] [Category.{v₁} A₁] [Category.{v₂} A₂]
  [Category.{w₀} B₀] [Category.{w₁} B₁] [Category.{w₂} B₂]
  {L₀ : A₀ ⥤ B₀} {R₀ : B₀ ⥤ A₀} {L₁ : A₁ ⥤ B₁} {R₁ : B₁ ⥤ A₁}
  {L₂ : A₂ ⥤ B₂} {R₂ : B₂ ⥤ A₂}

private theorem mate_comp_iff
    (a₀ : L₀ ⊣ R₀) (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    {U₁ : A₀ ⥤ A₁} {U₂ : A₁ ⥤ A₂} {U₃ : A₀ ⥤ A₂}
    {V₁ : B₀ ⥤ B₁} {V₂ : B₁ ⥤ B₂} {V₃ : B₀ ⥤ B₂}
    (α₁ : TwoSquare U₁ L₀ L₁ V₁) (α₂ : TwoSquare U₂ L₁ L₂ V₂)
    (α₃ : TwoSquare U₃ L₀ L₂ V₃)
    (cU : U₁ ⋙ U₂ ≅ U₃) (cV : V₁ ⋙ V₂ ≅ V₃) :
    (∀ P, L₂.map (cU.hom.app P) ≫ α₃.app P =
      α₂.app (U₁.obj P) ≫ V₂.map (α₁.app P) ≫ cV.hom.app (L₀.obj P)) ↔
    (∀ Q, cU.hom.app (R₀.obj Q) ≫ (mateEquiv a₀ a₂ α₃).app Q =
      U₂.map ((mateEquiv a₀ a₁ α₁).app Q) ≫
        (mateEquiv a₁ a₂ α₂).app (V₁.obj Q) ≫ R₂.map (cV.hom.app Q)) := by
  let α := ((TwoSquare.hComp α₁ α₂).whiskerTop cU.inv).whiskerBottom cV.hom
  have hm : mateEquiv a₀ a₂ α =
      Functor.whiskerLeft R₀ cU.inv ≫
        (TwoSquare.vComp (mateEquiv a₀ a₁ α₁) (mateEquiv a₁ a₂ α₂)) ≫
        Functor.whiskerRight cV.hom R₂ := by
    rw [mate_whisker_normalized, mateEquiv_vcomp]
  have hleft : (∀ P, L₂.map (cU.hom.app P) ≫ α₃.app P =
      α₂.app (U₁.obj P) ≫ V₂.map (α₁.app P) ≫ cV.hom.app (L₀.obj P)) ↔ α₃ = α := by
    constructor
    · intro h
      ext P
      apply (cancel_epi (L₂.map (cU.hom.app P))).mp
      simpa [α, TwoSquare.hComp, TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
        ← L₂.map_comp, Category.assoc] using h P
    · intro h P
      rw [h]
      simp [α, TwoSquare.hComp, TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
        Category.assoc]
  rw [hleft]
  constructor
  · intro h Q
    have he := congrArg (fun t ↦ (mateEquiv a₀ a₂ t).app Q) h
    rw [hm] at he
    rw [he]
    simp [TwoSquare.vComp, Category.assoc]
  · intro h
    apply (mateEquiv a₀ a₂).injective
    ext Q
    rw [hm]
    apply (cancel_epi (cU.hom.app (R₀.obj Q))).mp
    simpa [TwoSquare.vComp, Category.assoc] using h Q

private theorem mate_unit_iff
    (a : L₀ ⊣ R₀) {U : A₀ ⥤ A₀} {V : B₀ ⥤ B₀}
    (α : TwoSquare U L₀ L₀ V) (cU : U ≅ 𝟭 _) (cV : V ≅ 𝟭 _) :
    (∀ P, α.app P ≫ cV.hom.app (L₀.obj P) = L₀.map (cU.hom.app P)) ↔
    (∀ Q, (mateEquiv a a α).app Q ≫ R₀.map (cV.hom.app Q) =
      cU.hom.app (R₀.obj Q)) := by
  let β := ((TwoSquare.hId L₀).whiskerTop cU.hom).whiskerBottom cV.inv
  have hm : mateEquiv a a β =
      Functor.whiskerLeft R₀ cU.hom ≫ Functor.whiskerRight cV.inv R₀ := by
    rw [mate_whisker_normalized]
    have hid : mateEquiv a a (TwoSquare.hId L₀) = TwoSquare.vId R₀ := by
      ext Q
      simp [mateEquiv_apply, TwoSquare.hId, TwoSquare.vId]
    rw [hid]
    ext Q
    simp [TwoSquare.vId]
  have hleft : (∀ P, α.app P ≫ cV.hom.app (L₀.obj P) =
      L₀.map (cU.hom.app P)) ↔ α = β := by
    constructor
    · intro h
      ext P
      apply (cancel_mono (cV.hom.app (L₀.obj P))).mp
      simpa [β, TwoSquare.hId, TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
        Category.assoc] using h P
    · intro h P
      rw [h]
      simp [β, TwoSquare.hId, TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
        Category.assoc]
  rw [hleft]
  constructor
  · intro h Q
    have he := congrArg (fun t ↦ (mateEquiv a a t).app Q) h
    rw [hm] at he
    rw [he]
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Category.assoc, ← R₀.map_comp, Iso.inv_hom_id_app]
    simp only [R₀.map_id]
    exact Category.comp_id _
  · intro h
    apply (mateEquiv a a).injective
    ext Q
    rw [hm]
    apply (cancel_mono (R₀.map (cV.hom.app Q))).mp
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Category.assoc, ← R₀.map_comp, Iso.inv_hom_id_app]
    simp only [R₀.map_id]
    exact (h Q).trans (Category.comp_id _).symm

end Mates

variable {O : Type (u + 1)} [CommRing O] {t : O}
  {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
  {S : StrictEtaleCompactSupport O t c}
  (B : StrictEtaleBrownConstruction O t c S)

private theorem projection_hom {m n : ℕ} (h : m ≤ n)
    (P : DerivedCategory (strictEtaleLevel X O t n)) :
    (B.projection h).hom.app P =
      (S.properDerived.level m).direct.map ((B.openProjection h).hom.app P) ≫
        (B.properProjection h).hom.app ((S.levelDerivedOpen n).obj P) := by
  rw [B.projection_def]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Category.id_comp, Category.comp_id]
  exact Category.id_comp _

/-- The inverse coefficient projection respects the canonical tensor unit and associator.
Source: Zheng, Construction 5.15 and (5.16.2), printed pp. 34--35
(blueprint: lem-pur-etale-brown-coefficient-coherence).

Proof: apply normalized inverse-image tensor coherence to the proper and open
inverse-image factors. Mates preserve the unit and composition squares: this is
proved below from mate pasting, whiskering and cancellation of the scalar
comparison isomorphisms. The recorded proper and open mate equations identify
these mates with the respective coefficient projections. Expand projection_def,
substitute the two factor equations and use naturality of the proper projection
to paste the factors. No boundedness or quotient-flatness assumption is used. -/
theorem etaleBrownCoefficientCoherence :
    (∀ (n : ℕ) P,
      (B.projection (Nat.le_refl n)).hom.app P ≫
        (S.PY.derivedUnit n).hom.app ((S.levelFunctor n).obj P) =
      (S.levelFunctor n).map ((S.PX.derivedUnit n).hom.app P)) ∧
    (∀ {r m n : ℕ} (h₁ : m ≤ r) (h₂ : n ≤ m) P,
      (S.levelFunctor n).map ((S.PX.derivedAssoc h₁ h₂).hom.app P) ≫
        (B.projection (h₂.trans h₁)).hom.app P =
      (B.projection h₂).hom.app ((S.PX.scalar h₁).derived.obj P) ≫
        (S.PY.scalar h₂).derived.map ((B.projection h₁).hom.app P) ≫
        (S.PY.derivedAssoc h₁ h₂).hom.app ((S.levelFunctor r).obj P)) := by
  obtain ⟨hpU, hpA⟩ := strictEtaleInverseTensorCoherence c.g S.PY S.PZ
    S.properImage S.properDerived
  obtain ⟨hoU, hoA⟩ := strictEtaleInverseTensorCoherence c.i S.PZ S.PX
    S.openImage S.openDerived
  have properMate {m n : ℕ} (h : m ≤ n) :
      mateEquiv (S.properDerived.level n).adjunction (S.properDerived.level m).adjunction
        (S.properDerived.derivedTensor h).hom = (B.properProjection h).inv :=
    (B.properMate h).symm
  have openMate {m n : ℕ} (h : m ≤ n) :
      mateEquiv (S.levelDerivedOpenAdjunction n) (S.levelDerivedOpenAdjunction m)
        (B.openProjection h).hom = (S.openDerived.derivedTensor h).inv := B.openMate h
  have properUnit (n : ℕ) P :
      (B.properProjection (Nat.le_refl n)).hom.app P ≫
        (S.PY.derivedUnit n).hom.app ((S.properDerived.level n).direct.obj P) =
      (S.properDerived.level n).direct.map ((S.PZ.derivedUnit n).hom.app P) := by
    have hm := (mate_unit_iff (S.properDerived.level n).adjunction
      (S.properDerived.derivedTensor (Nat.le_refl n)).hom
      (S.PY.derivedUnit n) (S.PZ.derivedUnit n)).mp (hpU n) P
    rw [properMate] at hm
    apply (cancel_epi ((B.properProjection (Nat.le_refl n)).inv.app P)).mp
    simpa only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp] using hm.symm
  have properAssoc {r m n : ℕ} (h₁ : m ≤ r) (h₂ : n ≤ m) P :
      (S.properDerived.level n).direct.map ((S.PZ.derivedAssoc h₁ h₂).hom.app P) ≫
        (B.properProjection (h₂.trans h₁)).hom.app P =
      (B.properProjection h₂).hom.app ((S.PZ.scalar h₁).derived.obj P) ≫
        (S.PY.scalar h₂).derived.map ((B.properProjection h₁).hom.app P) ≫
        (S.PY.derivedAssoc h₁ h₂).hom.app ((S.properDerived.level r).direct.obj P) := by
    have hm := (mate_comp_iff (S.properDerived.level r).adjunction
      (S.properDerived.level m).adjunction (S.properDerived.level n).adjunction
      (S.properDerived.derivedTensor h₁).hom (S.properDerived.derivedTensor h₂).hom
      (S.properDerived.derivedTensor (h₂.trans h₁)).hom
      (S.PY.derivedAssoc h₁ h₂) (S.PZ.derivedAssoc h₁ h₂)).mp (hpA h₁ h₂) P
    rw [properMate, properMate, properMate] at hm
    let p := (B.properProjection h₂).app ((S.PZ.scalar h₁).derived.obj P) ≪≫
      (S.PY.scalar h₂).derived.mapIso ((B.properProjection h₁).app P)
    have hh : p.inv ≫
        (S.properDerived.level n).direct.map ((S.PZ.derivedAssoc h₁ h₂).hom.app P) =
        (S.PY.derivedAssoc h₁ h₂).hom.app ((S.properDerived.level r).direct.obj P) ≫
          (B.properProjection (h₂.trans h₁)).inv.app P := by
      simpa only [p, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Category.assoc]
        using hm.symm
    have hs := (inverse_square_iff p ((B.properProjection (h₂.trans h₁)).app P)
      _ _).mpr hh
    simpa only [p, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Category.assoc] using hs
  have openUnit (n : ℕ) P :
      (B.openProjection (Nat.le_refl n)).hom.app P ≫
        (S.PZ.derivedUnit n).hom.app ((S.levelDerivedOpen n).obj P) =
      (S.levelDerivedOpen n).map ((S.PX.derivedUnit n).hom.app P) := by
    apply (mate_unit_iff (S.levelDerivedOpenAdjunction n)
      (B.openProjection (Nat.le_refl n)).hom
      (S.PX.derivedUnit n) (S.PZ.derivedUnit n)).mpr ?_ P
    intro Q
    rw [openMate]
    apply (cancel_epi ((S.openDerived.derivedTensor (Nat.le_refl n)).hom.app Q)).mp
    simpa only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp] using (hoU n Q).symm
  have openAssoc {r m n : ℕ} (h₁ : m ≤ r) (h₂ : n ≤ m) P :
      (S.levelDerivedOpen n).map ((S.PX.derivedAssoc h₁ h₂).hom.app P) ≫
        (B.openProjection (h₂.trans h₁)).hom.app P =
      (B.openProjection h₂).hom.app ((S.PX.scalar h₁).derived.obj P) ≫
        (S.PZ.scalar h₂).derived.map ((B.openProjection h₁).hom.app P) ≫
        (S.PZ.derivedAssoc h₁ h₂).hom.app ((S.levelDerivedOpen r).obj P) := by
    apply (mate_comp_iff (S.levelDerivedOpenAdjunction r)
      (S.levelDerivedOpenAdjunction m) (S.levelDerivedOpenAdjunction n)
      (B.openProjection h₁).hom (B.openProjection h₂).hom
      (B.openProjection (h₂.trans h₁)).hom
      (S.PX.derivedAssoc h₁ h₂) (S.PZ.derivedAssoc h₁ h₂)).mpr ?_ P
    intro Q
    rw [openMate, openMate, openMate]
    let p := (S.openDerived.derivedTensor h₂).app ((S.PZ.scalar h₁).derived.obj Q) ≪≫
      (S.PX.scalar h₂).derived.mapIso ((S.openDerived.derivedTensor h₁).app Q)
    have hh : (S.openDerived.level n).inverse.map
        ((S.PZ.derivedAssoc h₁ h₂).hom.app Q) ≫
          ((S.openDerived.derivedTensor (h₂.trans h₁)).app Q).hom =
        p.hom ≫ (S.PX.derivedAssoc h₁ h₂).hom.app
          ((S.openDerived.level r).inverse.obj Q) := by
      simpa only [p, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Category.assoc]
        using hoA h₁ h₂ Q
    have hs := (inverse_square_iff p ((S.openDerived.derivedTensor (h₂.trans h₁)).app Q)
      _ _).mp hh
    simpa only [p, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Category.assoc]
      using hs.symm
  constructor
  · intro n P
    simp only [projection_hom, StrictEtaleCompactSupport.levelFunctor, Functor.comp_obj,
      Functor.comp_map, Category.assoc]
    rw [properUnit, ← Functor.map_comp, openUnit]
  · intro r m n h₁ h₂ P
    simp only [projection_hom, StrictEtaleCompactSupport.levelFunctor, Functor.comp_obj,
      Functor.comp_map, Functor.map_comp, Category.assoc]
    rw [← (S.properDerived.level n).direct.map_comp_assoc, openAssoc]
    simp only [Functor.map_comp, Category.assoc]
    rw [properAssoc]
    have hn := (B.properProjection h₂).hom.naturality ((B.openProjection h₁).hom.app P)
    dsimp only [Functor.comp_map, Functor.comp_obj] at hn
    rw [reassoc_of% hn]

end AlgebraicGeometry
