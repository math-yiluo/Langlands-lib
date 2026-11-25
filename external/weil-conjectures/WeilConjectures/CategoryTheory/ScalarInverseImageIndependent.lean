/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod

/-! # Scalar extension and inverse image on independently sized sites

Source: Stacks Project, Modules on Sites, Tags 03D2 and 03EL.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
universe u uC vC uD vD
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open SheafOfModules.GeometricConstruction
namespace SheafOfModules.ScalarIndependent
set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096

private abbrev ringSheaf {C : Type uC} [Category.{vC} C]
    [EssentiallySmall.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) : Sheaf J RingCat.{u} :=
  (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R
private abbrev underlying {C : Type uC} [Category.{vC} C]
    [EssentiallySmall.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) :
    SheafOfModules.{u} (ringSheaf R) ⥤ Sheaf J (Type u) :=
  toSheaf.{u} (ringSheaf R) ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})
private abbrev restriction {C : Type uC} [Category.{vC} C]
    [EssentiallySmall.{u} C] {J : GrothendieckTopology C}
    {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S) :
    SheafOfModules.{u} (ringSheaf S) ⥤ SheafOfModules.{u} (ringSheaf R) :=
  restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map a)

private noncomputable abbrev sheafBinaryProduct
    {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
    (X Y : Sheaf J (Type u)) : HasBinaryProduct X Y := inferInstance

attribute [local instance] sheafBinaryProduct

private noncomputable def productInverse
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (V : Sheaf K (Type u) ⥤ Sheaf J (Type u)) [PreservesLimits V]
    (X Y : Sheaf K (Type u)) : V.obj X ⨯ V.obj Y ⟶ V.obj (X ⨯ Y) :=
  (PreservesLimitPair.iso V X Y).inv

private theorem productInverse_eq
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (V : Sheaf K (Type u) ⥤ Sheaf J (Type u)) [PreservesLimits V]
    (X Y : Sheaf K (Type u)) : productInverse V X Y = inv (prodComparison V X Y) := by
  apply (cancel_mono (prodComparison V X Y)).mp
  change (PreservesLimitPair.iso V X Y).inv ≫ prodComparison V X Y = _
  rw [IsIso.inv_hom_id]
  simpa only [PreservesLimitPair.iso_hom] using (PreservesLimitPair.iso V X Y).inv_hom_id

attribute [local irreducible] productInverse

private theorem towerAdjunction
    {C D : Type*} [Category* C] [Category* D] (L : C ⥤ D) (R : D ⥤ C)
    (B : ∀ X Y, (L.obj X ⟶ Y) ≃ (X ⟶ R.obj Y))
    (hL : ∀ {X X'} (a : X ⟶ X') Y f, B X Y (L.map a ≫ f) = a ≫ B X' Y f)
    (hR : ∀ X {Y Y'} f (b : Y ⟶ Y'), B X Y' (f ≫ b) = B X Y f ≫ R.map b) :
    ∃ adj : L ⊣ R, adj.homEquiv = B := by
  refine ⟨Adjunction.mkOfHomEquiv
    { homEquiv := B
      homEquiv_naturality_left_symm := ?_
      homEquiv_naturality_right := fun f b ↦ hR _ f b },
    Adjunction.mkOfHomEquiv_homEquiv _⟩
  intro X X' Y a f
  apply (B X Y).injective
  rw [Equiv.apply_symm_apply, hL, Equiv.apply_symm_apply]

private theorem towerLeftComparison
    {CA CB DA DB : Type*} [Category* CA] [Category* CB] [Category* DA] [Category* DB]
    {TY : CA ⥤ CB} {RY : CB ⥤ CA} (adjY : TY ⊣ RY)
    {TX : DA ⥤ DB} {RX : DB ⥤ DA} (adjX : TX ⊣ RX)
    (L : CA ⥤ DA) (LB : CB ⥤ DB) (P : DB ⥤ CB)
    (BA : ∀ M H, (L.obj M ⟶ RX.obj H) ≃ (M ⟶ RY.obj (P.obj H)))
    (BB : ∀ N H, (LB.obj N ⟶ H) ≃ (N ⟶ P.obj H))
    (hAL : ∀ {M N} (a : M ⟶ N) H f, BA M H (L.map a ≫ f) = a ≫ BA N H f)
    (hAR : ∀ M {H H'} f (b : H ⟶ H'),
      BA M H' (f ≫ RX.map b) = BA M H f ≫ RY.map (P.map b))
    (hBL : ∀ {M N} (a : M ⟶ N) H f, BB M H (LB.map a ≫ f) = a ≫ BB N H f)
    (hBR : ∀ M {H H'} f (b : H ⟶ H'), BB M H' (f ≫ b) = BB M H f ≫ P.map b) :
    ∃ e : TY ⋙ LB ≅ L ⋙ TX, ∀ M,
      adjY.homEquiv M (P.obj (TX.obj (L.obj M)))
        (BB (TY.obj M) (TX.obj (L.obj M)) (e.hom.app M)) =
      BA M (TX.obj (L.obj M)) (adjX.unit.app (L.obj M)) := by
  obtain ⟨aB, haB⟩ := towerAdjunction LB P BB hBL hBR
  let ER : ∀ M H, ((L ⋙ TX).obj M ⟶ H) ≃ (M ⟶ (P ⋙ RY).obj H) :=
    fun M H ↦ (adjX.homEquiv (L.obj M) H).trans (BA M H)
  have hERL {M N} (a : M ⟶ N) H (f : (L ⋙ TX).obj N ⟶ H) :
      ER M H ((L ⋙ TX).map a ≫ f) = a ≫ ER N H f := by
    change BA M H (adjX.homEquiv _ _ (TX.map (L.map a) ≫ f)) = _
    rw [adjX.homEquiv_naturality_left, hAL]
    rfl
  have hERR M {H H'} (f : (L ⋙ TX).obj M ⟶ H) (b : H ⟶ H') :
      ER M H' (f ≫ b) = ER M H f ≫ (P ⋙ RY).map b := by
    change BA M H' (adjX.homEquiv _ _ (f ≫ b)) = _
    rw [adjX.homEquiv_naturality_right, hAR]
    rfl
  obtain ⟨aR, haR⟩ := towerAdjunction (L ⋙ TX) (P ⋙ RY) ER hERL hERR
  let aL := adjY.comp aB
  refine ⟨aL.leftAdjointUniq aR, ?_⟩
  intro M
  have h := aL.homEquiv_leftAdjointUniq_hom_app aR M
  rw [← aR.homEquiv_id, haR] at h
  dsimp only [aL] at h
  rw [Adjunction.comp_homEquiv, haB] at h
  change adjY.homEquiv _ _ (BB _ _ ((aL.leftAdjointUniq aR).hom.app M)) =
    BA M _ (adjX.homEquiv _ _ (𝟙 _)) at h
  simpa only [Adjunction.homEquiv_id, Functor.comp_obj] using h

/- Elementary operation graphs, used directly without the general tensor or
K-flat pullback constructions. Source: the operation-transport calculations in
RingedToposKFlatPullback and RingedTopoiInverseImageTensorPairingIsIso. -/

private theorem binary_of_graph
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    {X Y Z : Sheaf J (Type u)} {A B E : Sheaf K (Type u)}
    (dX : F.obj X ⟶ A) (dY : F.obj Y ⟶ B) (dZ : F.obj Z ⟶ E)
    (a : X ⨯ Y ⟶ Z) (b : A ⨯ B ⟶ E)
    (op : ∀ U, X.obj.obj U → Y.obj.obj U → Z.obj.obj U)
    (op' : ∀ V, A.obj.obj V → B.obj.obj V → E.obj.obj V)
    (hs : ∀ U p, a.hom.app U p =
      op U ((prod.fst : X ⨯ Y ⟶ X).hom.app U p)
        ((prod.snd : X ⨯ Y ⟶ Y).hom.app U p))
    (ht : ∀ V p, b.hom.app V p =
      op' V ((prod.fst : A ⨯ B ⟶ A).hom.app V p)
        ((prod.snd : A ⨯ B ⟶ B).hom.app V p))
    (hgraph : ∀ (T : Sheaf J (Type u)) (x : T ⟶ X) (y : T ⟶ Y) (z : T ⟶ Z),
      (∀ U p, z.hom.app U p = op U (x.hom.app U p) (y.hom.app U p)) →
      ∀ V p, (F.map z ≫ dZ).hom.app V p =
        op' V ((F.map x ≫ dX).hom.app V p) ((F.map y ≫ dY).hom.app V p)) :
    F.map a ≫ dZ = prodComparison F X Y ≫ prod.map dX dY ≫ b := by
  have h₁ : prodComparison F X Y ≫ prod.map dX dY ≫ prod.fst =
      F.map prod.fst ≫ dX := by simp only [prod.map_fst, prodComparison_fst_assoc]
  have h₂ : prodComparison F X Y ≫ prod.map dX dY ≫ prod.snd =
      F.map prod.snd ≫ dY := by simp only [prod.map_snd, prodComparison_snd_assoc]
  ext V p
  have h := hgraph (X ⨯ Y) prod.fst prod.snd a hs V p
  change (F.map a ≫ dZ).hom.app V p = b.hom.app V
    ((prodComparison F X Y ≫ prod.map dX dY).hom.app V p)
  rw [ht]
  have hh₁ := congrArg (fun k ↦ k.hom.app V p) h₁
  have hh₂ := congrArg (fun k ↦ k.hom.app V p) h₂
  change (prod.fst : A ⨯ B ⟶ A).hom.app V
    ((prodComparison F X Y ≫ prod.map dX dY).hom.app V p) = _ at hh₁
  change (prod.snd : A ⨯ B ⟶ B).hom.app V
    ((prodComparison F X Y ≫ prod.map dX dY).hom.app V p) = _ at hh₂
  rw [hh₁, hh₂]
  exact h

private noncomputable def radd
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) := fromProd (rset R) (rset R) ≫ ringAdd R

private noncomputable def rmul
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) := fromProd (rset R) (rset R) ≫ ringMul R

private noncomputable def madd
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (M : SheafOfModules.{u} (base R)) :=
  fromProd ((mset R).obj M) ((mset R).obj M) ≫ addition R M
private noncomputable def msmul
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (M : SheafOfModules.{u} (base R)) :=
  fromProd (rset R) ((mset R).obj M) ≫ action R M

private theorem towerAddSpec
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (M : SheafOfModules.{u} (ringSheaf R)) :
    addSpec M (madd R M) := by
  intro W x
  rfl

private theorem towerSMulSpec
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (M : SheafOfModules.{u} (ringSheaf R)) :
    smulSpec M (msmul R M) := by
  intro W x
  rfl

private theorem ringOperations
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (R : Sheaf J CommRingCat.{u}) (RI : Sheaf K CommRingCat.{u})
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u)) [PreservesFiniteLimits F]
    (I : AlgebraicInverseImage F R RI) :
    F.map (radd R) =
      prodComparison F (GeometricConstruction.rset R) (GeometricConstruction.rset R) ≫
        prod.map I.ringUnderlying.hom I.ringUnderlying.hom ≫ radd RI ≫
          I.ringUnderlying.inv ∧
    F.map (rmul R) =
      prodComparison F (GeometricConstruction.rset R) (GeometricConstruction.rset R) ≫
        prod.map I.ringUnderlying.hom I.ringUnderlying.hom ≫ rmul RI ≫
          I.ringUnderlying.inv := by
  constructor
  · apply (cancel_mono I.ringUnderlying.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact binary_of_graph F I.ringUnderlying.hom I.ringUnderlying.hom
      I.ringUnderlying.hom (radd R) (radd RI)
      (fun U x y ↦ @Add.add (R.obj.obj U) inferInstance x y)
      (fun U x y ↦ @Add.add (RI.obj.obj U) inferInstance x y)
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
      (fun T x y z hz U t ↦ I.ringAdd T x y z hz U t)
  · apply (cancel_mono I.ringUnderlying.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact binary_of_graph F I.ringUnderlying.hom I.ringUnderlying.hom
      I.ringUnderlying.hom (rmul R) (rmul RI)
      (fun U x y ↦ @Mul.mul (R.obj.obj U) inferInstance x y)
      (fun U x y ↦ @Mul.mul (RI.obj.obj U) inferInstance x y)
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
      (fun T x y z hz U t ↦ I.ringMul T x y z hz U t)

attribute [local irreducible] mateIsoEquiv restrictHomEquiv

-- Elaborating the operation-preserving Hom equivalence has many dependent objects.
set_option Elab.async false in
private theorem scalarHomEquivIndependent
{SY : Type uC} {SX : Type uD} [Category.{vC} SY] [Category.{vD} SX]
  [EssentiallySmall.{u} SY] [EssentiallySmall.{u} SX]
  {JY : GrothendieckTopology SY} {JX : GrothendieckTopology SX}
  {AY BY : Sheaf JY CommRingCat.{u}} {AX BX : Sheaf JX CommRingCat.{u}}
  (F : Sheaf JY (Type u) ⥤ Sheaf JX (Type u))
  (V : Sheaf JX (Type u) ⥤ Sheaf JY (Type u))
  (adj : F ⊣ V) [PreservesFiniteLimits F] [PreservesLimits V]
  [PreservesFiniteProducts V]
  (IA : AlgebraicInverseImage F AY AX)
  (P : SheafOfModules.{u} (ringSheaf BX) ⥤ SheafOfModules.{u} (ringSheaf BY))
  (eP : P ⋙ underlying BY ≅ underlying BX ⋙ V)
  (eB : F.obj ((sheafCompose JY (CategoryTheory.forget CommRingCat.{u})).obj BY) ≅
    (sheafCompose JX (CategoryTheory.forget CommRingCat.{u})).obj BX)
  (aY : AY ⟶ BY) (aX : AX ⟶ BX)
  (ha : F.map ((sheafCompose JY (CategoryTheory.forget CommRingCat.{u})).map aY) ≫
    eB.hom = IA.ringUnderlying.hom ≫
      (sheafCompose JX (CategoryTheory.forget CommRingCat.{u})).map aX)
  (hOps : ∀ H : SheafOfModules.{u} (ringSheaf BX),
    madd BY (P.obj H) ≫ eP.hom.app H =
      prod.map (C := Sheaf JY (Type u)) (eP.hom.app H) (eP.hom.app H) ≫
        productInverse V ((underlying BX).obj H) ((underlying BX).obj H) ≫
          V.map (madd BX H) ∧
    msmul BY (P.obj H) ≫ eP.hom.app H =
      prod.map (C := Sheaf JY (Type u))
        (adj.homEquiv (rset BY) (rset BX) eB.hom) (eP.hom.app H) ≫
        productInverse V (rset BX) ((underlying BX).obj H) ≫
          V.map (msmul BX H)) :
    ∃ B : ∀ (M : SheafOfModules.{u} (ringSheaf AY))
        (H : SheafOfModules.{u} (ringSheaf BX)), (IA.modules.obj M ⟶ (restriction aX).obj H) ≃
        (M ⟶ (restriction aY).obj (P.obj H)),
      (∀ (M : SheafOfModules.{u} (ringSheaf AY))
        (H : SheafOfModules.{u} (ringSheaf BX))
        (f : IA.modules.obj M ⟶ (restriction aX).obj H),
        (underlying AY).map (B M H f) ≫ eP.hom.app H =
        adj.homEquiv ((underlying AY).obj M) ((underlying BX).obj H)
          (IA.moduleUnderlying.inv.app M ≫ (underlying AX).map f)) ∧
      (∀ {M N : SheafOfModules.{u} (ringSheaf AY)} (a : M ⟶ N)
        (H : SheafOfModules.{u} (ringSheaf BX))
        (f : IA.modules.obj N ⟶ (restriction aX).obj H),
        B M H (IA.modules.map a ≫ f) = a ≫ B N H f) ∧
      (∀ (M : SheafOfModules.{u} (ringSheaf AY))
        {H H' : SheafOfModules.{u} (ringSheaf BX)}
        (f : IA.modules.obj M ⟶ (restriction aX).obj H) (b : H ⟶ H'),
        B M H' (f ≫ (restriction aX).map b) =
          B M H f ≫ (restriction aY).map (P.map b)) := by
  simp only [productInverse_eq] at hOps
  let E : ∀ (M : SheafOfModules.{u} (ringSheaf AY))
      (H : SheafOfModules.{u} (ringSheaf BX)),
      ((underlying AX).obj (IA.modules.obj M) ⟶ (underlying BX).obj H) ≃
        ((underlying AY).obj M ⟶ (underlying BY).obj (P.obj H)) :=
    fun M H ↦ mateIsoEquiv adj (IA.moduleUnderlying.app M) (eP.app H)
  have hImage M H (α : (underlying AX).obj (IA.modules.obj M) ⟶
      (underlying BX).obj H) :
      (∃ f : IA.modules.obj M ⟶ (restriction aX).obj H, (underlying AX).map f = α) ↔
        ∃ g : M ⟶ (restriction aY).obj (P.obj H), (underlying AY).map g = E M H α := by
    have hLA : F.map (madd AY M) =
        prodComparison F ((underlying AY).obj M) ((underlying AY).obj M) ≫
          prod.map (IA.moduleUnderlying.inv.app M) (IA.moduleUnderlying.inv.app M) ≫
            madd AX (IA.modules.obj M) ≫ IA.moduleUnderlying.hom.app M := by
      apply (cancel_mono (IA.moduleUnderlying.inv.app M)).mp
      simp only [Category.assoc, Iso.hom_inv_id_app]
      exact binary_of_graph F (IA.moduleUnderlying.inv.app M)
        (IA.moduleUnderlying.inv.app M) (IA.moduleUnderlying.inv.app M)
        (madd AY M) (madd AX (IA.modules.obj M))
        (fun U x y ↦ @Add.add (M.val.obj U) inferInstance x y)
        (fun U x y ↦ @Add.add ((IA.modules.obj M).val.obj U) inferInstance x y)
        (towerAddSpec AY M) (towerAddSpec AX (IA.modules.obj M))
        (fun T x y z hz U t ↦ IA.moduleAdd M T x y z hz U t)
    have hLS : F.map (msmul AY M) =
        prodComparison F (GeometricConstruction.rset AY) ((underlying AY).obj M) ≫
          prod.map IA.ringUnderlying.hom (IA.moduleUnderlying.inv.app M) ≫
            msmul AX (IA.modules.obj M) ≫ IA.moduleUnderlying.hom.app M := by
      apply (cancel_mono (IA.moduleUnderlying.inv.app M)).mp
      simp only [Category.assoc, Iso.hom_inv_id_app]
      exact binary_of_graph F IA.ringUnderlying.hom (IA.moduleUnderlying.inv.app M)
        (IA.moduleUnderlying.inv.app M) (msmul AY M) (msmul AX (IA.modules.obj M))
        (fun U x y ↦ @SMul.smul (AY.obj.obj U) (M.val.obj U) inferInstance x y)
        (fun U x y ↦ @SMul.smul (AX.obj.obj U) ((IA.modules.obj M).val.obj U)
          inferInstance x y)
        (towerSMulSpec AY M) (towerSMulSpec AX (IA.modules.obj M))
        (fun T a x z hz U t ↦ IA.moduleSMul M T a x z hz U t)
    have hm : adj.homEquiv _ _ (IA.moduleUnderlying.inv.app M ≫ α) =
        E M H α ≫ eP.hom.app H :=
      by exact mateIsoEquiv_equation adj (IA.moduleUnderlying.app M) (eP.app H) α
    have hAdd := binary_mate_iso_iff adj
      (IA.moduleUnderlying.app M) (IA.moduleUnderlying.app M) (IA.moduleUnderlying.app M)
      (eP.hom.app H) (eP.hom.app H) (eP.app H)
      (madd AY M) (madd AX (IA.modules.obj M)) (madd BX H) (madd BY (P.obj H))
      hLA (hOps H).1 α α α (E M H α) (E M H α) (E M H α) hm hm hm
    have hr : adj.homEquiv _ _ (IA.ringUnderlying.hom ≫
        (sheafCompose JX (CategoryTheory.forget CommRingCat.{u})).map aX) =
        (sheafCompose JY (CategoryTheory.forget CommRingCat.{u})).map aY ≫
          adj.homEquiv _ _ eB.hom := by
      rw [← ha, adj.homEquiv_naturality_left]
    have hSmul := binary_mate_iso_iff adj IA.ringUnderlying.symm
      (IA.moduleUnderlying.app M) (IA.moduleUnderlying.app M)
      (adj.homEquiv _ _ eB.hom) (eP.hom.app H) (eP.app H)
      (msmul AY M) (msmul AX (IA.modules.obj M)) (msmul BX H) (msmul BY (P.obj H))
      hLS (hOps H).2
      ((sheafCompose JX (CategoryTheory.forget CommRingCat.{u})).map aX) α α
      ((sheafCompose JY (CategoryTheory.forget CommRingCat.{u})).map aY)
      (E M H α) (E M H α) hr hm hm
    have hX := linear_iff aX (IA.modules.obj M) H
      (madd AX (IA.modules.obj M)) (madd BX H)
      (msmul AX (IA.modules.obj M)) (msmul BX H)
      (towerAddSpec AX (IA.modules.obj M)) (towerAddSpec BX H)
      (towerSMulSpec AX (IA.modules.obj M)) (towerSMulSpec BX H) α
    have hY := linear_iff aY M (P.obj H) (madd AY M) (madd BY (P.obj H))
      (msmul AY M) (msmul BY (P.obj H))
      (towerAddSpec AY M) (towerAddSpec BY (P.obj H))
      (towerSMulSpec AY M) (towerSMulSpec BY (P.obj H)) (E M H α)
    constructor
    · intro h
      obtain ⟨ha, hs⟩ := hX.mp h
      exact hY.mpr ⟨hAdd.mp ha, hSmul.mp hs⟩
    · intro h
      obtain ⟨ha, hs⟩ := hY.mp h
      exact hX.mpr ⟨hAdd.mpr ha, hSmul.mpr hs⟩
  obtain ⟨B, hB⟩ : ∃ B : ∀ M H,
      (IA.modules.obj M ⟶ (restriction aX).obj H) ≃
        (M ⟶ (restriction aY).obj (P.obj H)),
      ∀ M H f, (underlying AY).map (B M H f) ≫ eP.hom.app H =
        adj.homEquiv ((underlying AY).obj M) ((underlying BX).obj H)
          (IA.moduleUnderlying.inv.app M ≫ (underlying AX).map f) := by
    refine ⟨fun M H ↦ restrictHomEquiv (underlying AX) (underlying AY)
      (E M H) (hImage M H), ?_⟩
    intro M H f
    rw [restrictHomEquiv_map]
    exact (mateIsoEquiv_equation adj (IA.moduleUnderlying.app M) (eP.app H) _).symm
  refine ⟨B, hB, ?_, ?_⟩
  · intro M N a H f
    apply (underlying AY).map_injective
    apply (cancel_mono (eP.hom.app H)).mp
    have hn := IA.moduleUnderlying.inv.naturality a
    have hp : IA.moduleUnderlying.inv.app M ≫ (underlying AX).map (IA.modules.map a ≫ f) =
        F.map ((underlying AY).map a) ≫ IA.moduleUnderlying.inv.app N ≫
          (underlying AX).map f := by
      erw [(underlying AX).map_comp, ← Category.assoc, ← hn, Category.assoc]
    calc
      _ = adj.homEquiv ((underlying AY).obj M) ((underlying BX).obj H)
          (IA.moduleUnderlying.inv.app M ≫ (underlying AX).map (IA.modules.map a ≫ f)) :=
        hB M H (IA.modules.map a ≫ f)
      _ = adj.homEquiv ((underlying AY).obj M) ((underlying BX).obj H)
          (F.map ((underlying AY).map a) ≫
          IA.moduleUnderlying.inv.app N ≫ (underlying AX).map f) :=
        congrArg (adj.homEquiv ((underlying AY).obj M) ((underlying BX).obj H)) hp
      _ = (underlying AY).map a ≫
          adj.homEquiv ((underlying AY).obj N) ((underlying BX).obj H)
          (IA.moduleUnderlying.inv.app N ≫ (underlying AX).map f) :=
        adj.homEquiv_naturality_left _ _
      _ = (underlying AY).map a ≫ (underlying AY).map (B N H f) ≫ eP.hom.app H :=
        congrArg (fun k ↦ (underlying AY).map a ≫ k) (hB N H f).symm
      _ = _ := (Category.assoc _ _ _).symm.trans
        (congrArg (fun k ↦ k ≫ eP.hom.app H)
          ((underlying AY).map_comp a (B N H f)).symm)
  · intro M H H' f b
    apply (underlying AY).map_injective
    apply (cancel_mono (eP.hom.app H')).mp
    have hp : IA.moduleUnderlying.inv.app M ≫
        (underlying AX).map (f ≫ (restriction aX).map b) =
        (IA.moduleUnderlying.inv.app M ≫ (underlying AX).map f) ≫
          (underlying BX).map b := by
      change IA.moduleUnderlying.inv.app M ≫
        ((underlying AX).map f ≫ (underlying BX).map b) = _
      exact (Category.assoc _ _ _).symm
    calc
      _ = adj.homEquiv ((underlying AY).obj M) ((underlying BX).obj H')
          (IA.moduleUnderlying.inv.app M ≫
          (underlying AX).map (f ≫ (restriction aX).map b)) :=
        hB M H' (f ≫ (restriction aX).map b)
      _ = adj.homEquiv ((underlying AY).obj M) ((underlying BX).obj H')
          ((IA.moduleUnderlying.inv.app M ≫ (underlying AX).map f) ≫
          (underlying BX).map b) :=
        congrArg (adj.homEquiv ((underlying AY).obj M) ((underlying BX).obj H')) hp
      _ = adj.homEquiv ((underlying AY).obj M) ((underlying BX).obj H)
          (IA.moduleUnderlying.inv.app M ≫ (underlying AX).map f) ≫
          V.map ((underlying BX).map b) := adj.homEquiv_naturality_right _ _
      _ = ((underlying AY).map (B M H f) ≫ eP.hom.app H) ≫
          V.map ((underlying BX).map b) :=
        congrArg (fun k ↦ k ≫ V.map ((underlying BX).map b)) (hB M H f).symm
      _ = (underlying AY).map (B M H f) ≫
          ((underlying BY).map (P.map b) ≫ eP.hom.app H') := by
        exact (Category.assoc _ _ _).trans
          (congrArg (fun k ↦ (underlying AY).map (B M H f) ≫ k)
            (eP.hom.naturality b).symm)
      _ = _ := by
        change (underlying AY).map (B M H f) ≫
          ((underlying AY).map ((restriction aY).map (P.map b)) ≫ eP.hom.app H') = _
        exact (Category.assoc _ _ _).symm.trans
          (congrArg (fun k ↦ k ≫ eP.hom.app H')
            ((underlying AY).map_comp (B M H f) ((restriction aY).map (P.map b))).symm)

attribute [local irreducible] madd msmul
set_option backward.isDefEq.respectTransparency false
private theorem directData
{SY : Type uC} {SX : Type uD} [Category.{vC} SY] [Category.{vD} SX]
  [EssentiallySmall.{u} SY] [EssentiallySmall.{u} SX]
  {JY : GrothendieckTopology SY} {JX : GrothendieckTopology SX}
  {BY : Sheaf JY CommRingCat.{u}} {BX : Sheaf JX CommRingCat.{u}}
  (F : Sheaf JY (Type u) ⥤ Sheaf JX (Type u))
  (V : Sheaf JX (Type u) ⥤ Sheaf JY (Type u))
  (adj : F ⊣ V) [PreservesFiniteLimits F]
  (IB : AlgebraicInverseImage F BY BX) :
    letI : PreservesLimits V := adj.rightAdjoint_preservesLimits
    ∃ (P : SheafOfModules.{u} (ringSheaf BX) ⥤ SheafOfModules.{u} (ringSheaf BY))
      (eP : P ⋙ underlying BY ≅ underlying BX ⋙ V),
      ∀ H : SheafOfModules.{u} (ringSheaf BX),
      madd BY (P.obj H) ≫ eP.hom.app H =
        prod.map (eP.hom.app H) (eP.hom.app H) ≫
          productInverse V ((underlying BX).obj H) ((underlying BX).obj H) ≫
            V.map (madd BX H) ∧
      msmul BY (P.obj H) ≫ eP.hom.app H =
        prod.map (adj.homEquiv _ _ IB.ringUnderlying.hom) (eP.hom.app H) ≫
          productInverse V (rset BX) ((underlying BX).obj H) ≫
            V.map (msmul BX H) := by
  let : PreservesLimits V := adj.rightAdjoint_preservesLimits
  let : F.Braided := Functor.Braided.ofChosenFiniteProducts F
  let : V.Braided := Functor.Braided.ofChosenFiniteProducts V
  have hR := ringOperations BY BX F IB
  let eR := IB.ringUnderlying.symm
  have haI := (binary_transport_iff F _ _ eR (ringAdd BY) (ringAdd BX)).1 hR.1
  have hmI := ringIso_isMonHom F BY BX eR
    ((binary_transport_iff F _ _ eR (ringMul BY) (ringMul BX)).1 hR.2)
  let d := adj.homEquiv (rset BY) (rset BX) IB.ringUnderlying.hom
  have haP : ringAdd BY ≫ d = (d ⊗ₘ d) ≫ Functor.LaxMonoidal.μ V _ _ ≫
      V.map (ringAdd BX) := by
    apply adjunct_binary F V adj _ _ _ _ IB.ringUnderlying.hom
    exact binary_inverse F _ _ eR _ _ haI
  have hmP : let := ringMonoid BX
             let := ringMonoid BY
             let := V.monObjObj (rset BX)
             IsMonHom d := by
    let := ringMonoid BY
    let := ringMonoid BX
    let := F.monObjObj (rset BY)
    let : IsMonHom eR.hom := hmI
    let := V.monObjObj (rset BX)
    refine ⟨?_, ?_⟩
    · apply adjunct_constant F V adj _ _ (ringOne BY) (ringOne BX)
        IB.ringUnderlying.hom
      apply (cancel_epi (Functor.LaxMonoidal.ε F)).1
      have hu : (Functor.LaxMonoidal.ε F ≫ F.map (ringOne BY)) ≫ eR.inv =
          ringOne BX := IsMonHom.one_hom eR.inv
      change (Functor.LaxMonoidal.ε F ≫ F.map (ringOne BY)) ≫ eR.inv = _
      rw [hu]
      have hterm : Functor.LaxMonoidal.ε F ≫
          CartesianMonoidalCategory.terminalComparison F = 𝟙 _ :=
        CartesianMonoidalCategory.toUnit_unique _ _
      simp only [← Category.assoc, hterm, Category.id_comp]
    · apply adjunct_binary F V adj _ _ (ringMul BY) (ringMul BX)
        IB.ringUnderlying.hom
      exact binary_inverse F _ _ eR _ _
        ((binary_transport_iff F _ _ eR (ringMul BY) (ringMul BX)).1 hR.2)
  let P := imageFunctor V BX BY d haP hmP
  let eP := imageFunctorUnderlying V BX BY d haP hmP
  refine ⟨P, eP, ?_⟩
  intro H
  simp only [productInverse_eq]
  constructor
  · unfold madd
    have h := imageModule_addition_comparison V BX BY d haP hmP H
    change V.map (fromProd _ _ ≫ addition BX H) = prodComparison V _ _ ≫
      (fromProd _ _ ≫ addition BY (imageModule V BX BY d haP hmP H)) at h
    change (fromProd _ _ ≫ addition BY (P.obj H)) ≫ 𝟙 _ =
      prod.map (𝟙 _) (𝟙 _) ≫ inv (prodComparison V _ _) ≫
        V.map (fromProd _ _ ≫ addition BX H)
    rw [h]
    simp only [Category.comp_id, prod.map_id_id, Category.id_comp,
      IsIso.inv_hom_id_assoc]
    rfl
  · unfold msmul
    dsimp only [P, eP, imageFunctorUnderlying]
    change (fromProd _ _ ≫ action BY (imageModule V BX BY d haP hmP H)) ≫ 𝟙 _ =
        prod.map d (𝟙 _) ≫ inv (prodComparison V _ _) ≫
          V.map (fromProd _ _ ≫ action BX H)
    simpa only [Category.comp_id] using
      imageModule_action_comparison_right V BX BY d haP hmP H

set_option backward.isDefEq.respectTransparency true
-- The unit equation compares two adjunctions and two restriction functors.
/-- Scalar extension commutes with inverse image, with the unit fixed.
Source: Stacks Project, Modules on Sites, Tag 03EL
(auxiliary; not a blueprint node).

Proof: transport the direct-image additive group and action along the set adjunction.
The operation mate equations identify linear maps on its two sides. Composing with
the scalar-extension adjunctions gives two left adjoints to the same right adjoint.
Their unique adjunction comparison is the required isomorphism. Its defining equation
is the stated unit normalization. The two sites may have independent universes. -/
theorem exists_scalarInverseImageIndependent
{SY : Type uC} {SX : Type uD} [Category.{vC} SY] [Category.{vD} SX]
  [EssentiallySmall.{u} SY] [EssentiallySmall.{u} SX]
  {JY : GrothendieckTopology SY} {JX : GrothendieckTopology SX}
  {AY BY : Sheaf JY CommRingCat.{u}} {AX BX : Sheaf JX CommRingCat.{u}}
  (F : Sheaf JY (Type u) ⥤ Sheaf JX (Type u))
  (V : Sheaf JX (Type u) ⥤ Sheaf JY (Type u))
  (adj : F ⊣ V) [PreservesFiniteLimits F]
  (IA : AlgebraicInverseImage F AY AX) (IB : AlgebraicInverseImage F BY BX)
  (aY : AY ⟶ BY) (aX : AX ⟶ BX)
  (ha : F.map ((sheafCompose JY (CategoryTheory.forget CommRingCat.{u})).map aY) ≫
    IB.ringUnderlying.hom = IA.ringUnderlying.hom ≫
      (sheafCompose JX (CategoryTheory.forget CommRingCat.{u})).map aX)
    (TY : SheafOfModules.{u}
        ((sheafCompose JY (forget₂ CommRingCat.{u} RingCat.{u})).obj AY) ⥤
      SheafOfModules.{u}
        ((sheafCompose JY (forget₂ CommRingCat.{u} RingCat.{u})).obj BY))
    (TX : SheafOfModules.{u}
        ((sheafCompose JX (forget₂ CommRingCat.{u} RingCat.{u})).obj AX) ⥤
      SheafOfModules.{u}
        ((sheafCompose JX (forget₂ CommRingCat.{u} RingCat.{u})).obj BX))
    (adjY : TY ⊣ restrictScalars.{u}
      ((sheafCompose JY (forget₂ CommRingCat.{u} RingCat.{u})).map aY))
    (adjX : TX ⊣ restrictScalars.{u}
      ((sheafCompose JX (forget₂ CommRingCat.{u} RingCat.{u})).map aX)) :
    ∃ e : TY ⋙ IB.modules ≅ IA.modules ⋙ TX,
      ∀ M : SheafOfModules.{u}
          ((sheafCompose JY (forget₂ CommRingCat.{u} RingCat.{u})).obj AY),
        F.map ((toSheaf
          ((sheafCompose JY (forget₂ CommRingCat.{u} RingCat.{u})).obj AY) ⋙
            sheafCompose JY (CategoryTheory.forget AddCommGrpCat.{u})).map
              (adjY.unit.app M)) ≫
          IB.moduleUnderlying.inv.app (TY.obj M) ≫
            (toSheaf ((sheafCompose JX (forget₂ CommRingCat.{u} RingCat.{u})).obj BX) ⋙
              sheafCompose JX (CategoryTheory.forget AddCommGrpCat.{u})).map (e.hom.app M) =
          IA.moduleUnderlying.inv.app M ≫
            (toSheaf ((sheafCompose JX (forget₂ CommRingCat.{u} RingCat.{u})).obj AX) ⋙
              sheafCompose JX (CategoryTheory.forget AddCommGrpCat.{u})).map
                (adjX.unit.app (IA.modules.obj M)) := by
  classical
  let : PreservesLimits V := adj.rightAdjoint_preservesLimits
  obtain ⟨P, eP, hOps⟩ := directData F V adj IB
  obtain ⟨BA, hBA, hBAL, hBAR⟩ :=
    scalarHomEquivIndependent F V adj IA P eP IB.ringUnderlying aY aX ha hOps
  obtain ⟨BB, hBB, hBBL, hBBR⟩ :
      ∃ BB : ∀ (M : SheafOfModules.{u} (ringSheaf BY))
          (H : SheafOfModules.{u} (ringSheaf BX)), (IB.modules.obj M ⟶ H) ≃ (M ⟶ P.obj H),
        (∀ M H f, (underlying BY).map (BB M H f) ≫ eP.hom.app H =
          adj.homEquiv _ _ (IB.moduleUnderlying.inv.app M ≫ (underlying BX).map f)) ∧
        (∀ {M N} (a : M ⟶ N) H f,
          BB M H (IB.modules.map a ≫ f) = a ≫ BB N H f) ∧
        (∀ M {H H'} f (b : H ⟶ H'), BB M H' (f ≫ b) = BB M H f ≫ P.map b) := by
    obtain ⟨B, hB, hBL, hBR⟩ :=
      scalarHomEquivIndependent F V adj IB P eP IB.ringUnderlying (𝟙 BY) (𝟙 BX)
        (by simp) hOps
    exact ⟨B, hB, hBL, hBR⟩
  obtain ⟨e, he⟩ := towerLeftComparison adjY adjX
    IA.modules IB.modules P BA BB hBAL hBAR hBBL hBBR
  have hu (M : SheafOfModules.{u} (ringSheaf AY)) :
      F.map (((underlying AY).map (adjY.unit.app M))) ≫
      IB.moduleUnderlying.inv.app (TY.obj M) ≫
        (underlying BX).map (e.hom.app M) =
      IA.moduleUnderlying.inv.app M ≫ ((underlying AX).map (adjX.unit.app (IA.modules.obj M))) := by
    let H : SheafOfModules.{u} (ringSheaf BX) := TX.obj (IA.modules.obj M)
    have h := he M
    have hh := congrArg (fun f ↦ (underlying AY).map f ≫ eP.hom.app H) h
    rw [Adjunction.homEquiv_unit, (underlying AY).map_comp] at hh
    change (((underlying AY).map (adjY.unit.app M)) ≫
      (underlying BY).map (BB (TY.obj M) H (e.hom.app M))) ≫
        eP.hom.app H =
      (underlying AY).map (BA M H (adjX.unit.app (IA.modules.obj M))) ≫
        eP.hom.app H at hh
    apply (adj.homEquiv ((underlying AY).obj M) ((underlying BX).obj H)).injective
    calc
      _ = ((underlying AY).map (adjY.unit.app M)) ≫
          adj.homEquiv ((underlying BY).obj (TY.obj M)) ((underlying BX).obj H)
          (IB.moduleUnderlying.inv.app (TY.obj M) ≫
            (underlying BX).map (e.hom.app M)) := adj.homEquiv_naturality_left _ _
      _ = ((underlying AY).map (adjY.unit.app M)) ≫
          ((underlying BY).map (BB (TY.obj M) H (e.hom.app M)) ≫
            eP.hom.app H) :=
        congrArg (fun k ↦ ((underlying AY).map (adjY.unit.app M)) ≫ k)
          (hBB (TY.obj M) H (e.hom.app M)).symm
      _ = (underlying AY).map
          (BA M H (adjX.unit.app (IA.modules.obj M))) ≫
            eP.hom.app H := (Category.assoc _ _ _).symm.trans hh
      _ = _ := hBA M H (adjX.unit.app (IA.modules.obj M))
  exact ⟨e, hu⟩

end SheafOfModules.ScalarIndependent
