/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImageTensorComparison

/-! # Algebraic presentation of the specified pro-etale module inverse image

Source: Stacks Project, Tags 00YV and 03D2.
(auxiliary; not a blueprint node)
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.ProEtaleTensorComparison
namespace AlgebraicGeometry.Scheme

private theorem inverseImage_map_ext
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {T : Sheaf (ProEt.topology Y) (Type (u + 1))}
    {H : Sheaf (ProEt.topology X) (Type (u + 1))}
    (a b : (AlgebraicGeometry.ProEtale.setPullback f).obj T ⟶ H)
    (h : ∀ (U : Y.ProEtᵒᵖ) (x : T.obj.obj U),
      a.hom.app ((proEtaleBaseChange f).op.obj U)
          (((AlgebraicGeometry.ProEtale.setPullbackAdjunction f).unit.app T).hom.app U x) =
      b.hom.app ((proEtaleBaseChange f).op.obj U)
          (((AlgebraicGeometry.ProEtale.setPullbackAdjunction f).unit.app T).hom.app U x)) :
    a = b := by
  apply ((AlgebraicGeometry.ProEtale.setPullbackAdjunction f).homEquiv T H).injective
  ext U x
  exact h U x

private def binaryMap
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (X Y Z : Sheaf J (Type w))
    (op : ∀ U : Cᵒᵖ, X.obj.obj U → Y.obj.obj U → Z.obj.obj U)
    (hn : ∀ {U V : Cᵒᵖ} (i : U ⟶ V) x y,
      op V (X.obj.map i x) (Y.obj.map i y) = Z.obj.map i (op U x y))
    {T : Sheaf J (Type w)} (a : T ⟶ X) (b : T ⟶ Y) : T ⟶ Z :=
  ⟨{ app := fun U ↦ ↾fun x ↦ op U (a.hom.app U x) (b.hom.app U x)
     naturality := by
       intro U V i
       ext x
       change op V (a.hom.app V (T.obj.map i x)) (b.hom.app V (T.obj.map i x)) = _
       have ha := congrArg (fun q ↦ q x) (a.hom.naturality i)
       have hb := congrArg (fun q ↦ q x) (b.hom.naturality i)
       change a.hom.app V (T.obj.map i x) = X.obj.map i (a.hom.app U x) at ha
       change b.hom.app V (T.obj.map i x) = Y.obj.map i (b.hom.app U x) at hb
       rw [ha, hb]
       exact hn i _ _ }⟩

private theorem transport_binary
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A B C : Sheaf (ProEt.topology Y) (Type (u + 1))}
    {A' B' C' : Sheaf (ProEt.topology X) (Type (u + 1))}
    (eA : (AlgebraicGeometry.ProEtale.setPullback f).obj A ≅ A')
    (eB : (AlgebraicGeometry.ProEtale.setPullback f).obj B ≅ B')
    (eC : (AlgebraicGeometry.ProEtale.setPullback f).obj C ≅ C')
    (op : ∀ U : Y.ProEtᵒᵖ, A.obj.obj U → B.obj.obj U → C.obj.obj U)
    (op' : ∀ V : X.ProEtᵒᵖ, A'.obj.obj V → B'.obj.obj V → C'.obj.obj V)
    (hn : ∀ {U V : X.ProEtᵒᵖ} (i : U ⟶ V) x y,
      op' V (A'.obj.map i x) (B'.obj.map i y) = C'.obj.map i (op' U x y))
    (hu : ∀ (U : Y.ProEtᵒᵖ) x y,
      eC.hom.hom.app ((proEtaleBaseChange f).op.obj U)
          (((AlgebraicGeometry.ProEtale.setPullbackAdjunction f).unit.app C).hom.app U
            (op U x y)) =
      op' ((proEtaleBaseChange f).op.obj U)
        (eA.hom.hom.app ((proEtaleBaseChange f).op.obj U)
          (((AlgebraicGeometry.ProEtale.setPullbackAdjunction f).unit.app A).hom.app U x))
        (eB.hom.hom.app ((proEtaleBaseChange f).op.obj U)
          (((AlgebraicGeometry.ProEtale.setPullbackAdjunction f).unit.app B).hom.app U y)))
    (T : Sheaf (ProEt.topology Y) (Type (u + 1))) (a : T ⟶ A) (b : T ⟶ B) (t : T ⟶ C)
    (ht : ∀ U x, t.hom.app U x = op U (a.hom.app U x) (b.hom.app U x)) :
    ∀ V x,
      eC.hom.hom.app V (((AlgebraicGeometry.ProEtale.setPullback f).map t).hom.app V x) =
      op' V
        (eA.hom.hom.app V (((AlgebraicGeometry.ProEtale.setPullback f).map a).hom.app V x))
        (eB.hom.hom.app V (((AlgebraicGeometry.ProEtale.setPullback f).map b).hom.app V x)) := by
  let L := AlgebraicGeometry.ProEtale.setPullback f
  let eta := (AlgebraicGeometry.ProEtale.setPullbackAdjunction f).unit
  have hh : L.map t ≫ eC.hom =
      binaryMap A' B' C' op' hn (L.map a ≫ eA.hom) (L.map b ≫ eB.hom) := by
    apply inverseImage_map_ext f
    intro U x
    have ha := congrArg (fun q ↦ q.hom.app U x) (eta.naturality a)
    have hb := congrArg (fun q ↦ q.hom.app U x) (eta.naturality b)
    have hc := congrArg (fun q ↦ q.hom.app U x) (eta.naturality t)
    change eC.hom.hom.app _ ((L.map t).hom.app _ (eta.app T |>.hom.app U x)) =
      op' _ (eA.hom.hom.app _ ((L.map a).hom.app _ (eta.app T |>.hom.app U x)))
        (eB.hom.hom.app _ ((L.map b).hom.app _ (eta.app T |>.hom.app U x)))
    change (eta.app A).hom.app U (a.hom.app U x) =
      (L.map a).hom.app _ ((eta.app T).hom.app U x) at ha
    change (eta.app B).hom.app U (b.hom.app U x) =
      (L.map b).hom.app _ ((eta.app T).hom.app U x) at hb
    change (eta.app C).hom.app U (t.hom.app U x) =
      (L.map t).hom.app _ ((eta.app T).hom.app U x) at hc
    rw [← ha, ← hb, ← hc, ht]
    exact hu U _ _
  intro V x
  exact congrArg (fun q ↦ q.hom.app V x) hh

private theorem inverseSection_map {X Y : Scheme.{u}} (f : X ⟶ Y)
    {R : Rings Y} {M N : Modules R} (k : M ⟶ N) (V : Y.ProEt) (m : M.val.obj (op V)) :
    ((inverse f R).map k).val.app (op ((proEtaleBaseChange f).obj V))
        (inverseSection f M V m) = inverseSection f N V (k.val.app (op V) m) := by
  have h := (SheafOfModules.pullbackPushforwardAdjunction
    (proEtaleModelRingUnit f R)).unit.naturality
    ((proEtaleModuleToModel ((sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)).map k)
  exact (congrArg (fun z ↦ z.val.app
    (op ((AsSmall.up : Y.ProEt ⥤ proEtaleSiteModel Y).obj V)) m) h).symm

private theorem inverseSection_add {X Y : Scheme.{u}} (f : X ⟶ Y)
    {R : Rings Y} (M : Modules R) (V : Y.ProEt) (m n : M.val.obj (op V)) :
    inverseSection f M V (m + n) = inverseSection f M V m + inverseSection f M V n := by
  exact (((SheafOfModules.pullbackPushforwardAdjunction (proEtaleModelRingUnit f R)).unit.app
    ((proEtaleModuleToModel ((sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)).obj M)).val.app
        (op ((AsSmall.up : Y.ProEt ⥤ proEtaleSiteModel Y).obj V))).hom.map_add m n

private theorem inverseSection_smul {X Y : Scheme.{u}} (f : X ⟶ Y)
    {R : Rings Y} (M : Modules R) (V : Y.ProEt)
    (r : R.obj.obj (op V)) (m : M.val.obj (op V)) :
    inverseSection f M V (r • m) =
      (((proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app R).hom.app (op V) r) •
        inverseSection f M V m := by
  exact (((SheafOfModules.pullbackPushforwardAdjunction (proEtaleModelRingUnit f R)).unit.app
    ((proEtaleModuleToModel ((sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)).obj M)).val.app
        (op ((AsSmall.up : Y.ProEt ⥤ proEtaleSiteModel Y).obj V))).hom.map_smul r m

private theorem moduleSetsIdentification_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {R : Rings Y} {M N : Modules R} (k : M ⟶ N) :
    (AlgebraicGeometry.ProEtale.setPullback f).map (moduleMapSets k) ≫
        (moduleSetsIdentification f N).hom =
      (moduleSetsIdentification f M).hom ≫ moduleMapSets ((inverse f R).map k) := by
  apply inverseImage_map_ext f
  intro U m
  have hn := congrArg (fun z ↦ z.hom.app U m)
    ((AlgebraicGeometry.ProEtale.setPullbackAdjunction f).unit.naturality (moduleMapSets k))
  change (moduleSetsIdentification f N).hom.hom.app _
      (((AlgebraicGeometry.ProEtale.setPullback f).map (moduleMapSets k)).hom.app _
        (((AlgebraicGeometry.ProEtale.setPullbackAdjunction f).unit.app
          (moduleSets M)).hom.app U m)) = _
  change ((AlgebraicGeometry.ProEtale.setPullbackAdjunction f).unit.app
      (moduleSets N)).hom.app U (k.val.app U m) =
    ((AlgebraicGeometry.ProEtale.setPullback f).map (moduleMapSets k)).hom.app _
      (((AlgebraicGeometry.ProEtale.setPullbackAdjunction f).unit.app
        (moduleSets M)).hom.app U m) at hn
  rw [← hn]
  have hM := (Classical.choose_spec (moduleSetsIdentification_exists f M)).1 U.unop m
  have hN := (Classical.choose_spec (moduleSetsIdentification_exists f N)).1 U.unop
    (k.val.app U m)
  change (moduleSetsIdentification f M).hom.hom.app _ _ = _ at hM
  change (moduleSetsIdentification f N).hom.hom.app _ _ = _ at hN
  change _ = ((inverse f R).map k).val.app _
    ((moduleSetsIdentification f M).hom.hom.app _ _)
  exact hN.trans ((inverseSection_map f k U.unop m).symm.trans
    (congrArg (fun z ↦ ((inverse f R).map k).val.app
      ((proEtaleBaseChange f).op.obj U) z) hM.symm))

/-- The specified module inverse image transports the ring and module operations along
set inverse image.
Source: Stacks Project, Sites, Tag 00YV, and Modules on Sites, Tag 03D2;
the algebraic-structure step in stratum scalar extension.
(auxiliary; not a blueprint node)

Proof: use the existing unit-normalized underlying-set identifications for rings and
modules. The module adjunction unit is natural, so the module identification is natural:
transpose its naturality square through the set adjunction and check on unit sections.
The same method transports every operation graph. Both sides of each graph equation
are sheaf maps out of the inverse image of its test sheaf. Their adjuncts agree because
the ring unit preserves addition, multiplication, zero and one, and the module unit
preserves addition, zero and the scalar action through the ring unit. Set modules to
proEtaleModuleInverseImage itself, so the final functor equality is reflexivity.
This argument includes empty schemes and zero rings and imposes no flatness assumption. -/
theorem proEtaleAlgebraicInverseImage_exists {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :
    ∃ I : SheafOfModules.AlgebraicInverseImage
        (proEtaleSheafInverseImage f (Type (u + 1))) R
        ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R),
      I.modules = proEtaleModuleInverseImage f R := by
  let eR := ringSetsIdentification f R
  let eI : (SheafOfModules.toSheaf ((sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) ⋙
        sheafCompose (ProEt.topology Y) (CategoryTheory.forget AddCommGrpCat.{u + 1})) ⋙
      AlgebraicGeometry.ProEtale.setPullback f ≅
      inverse f R ⋙ (SheafOfModules.toSheaf ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (inverseRing f R)) ⋙
          sheafCompose (ProEt.topology X) (CategoryTheory.forget AddCommGrpCat.{u + 1})) :=
    NatIso.ofComponents (fun M ↦ moduleSetsIdentification f M)
      (fun k ↦ moduleSetsIdentification_naturality f k)
  have hr (U : Y.ProEtᵒᵖ) (r : R.obj.obj U) :
      eR.hom.hom.app ((proEtaleBaseChange f).op.obj U)
        (((AlgebraicGeometry.ProEtale.setPullbackAdjunction f).unit.app
          (ringSets R)).hom.app U r) =
      ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app R).hom.app U r :=
    (Classical.choose_spec (ringSetsIdentification_exists f R)).1 U.unop r
  have hm (M : Modules R) (U : Y.ProEtᵒᵖ) (m : M.val.obj U) :
      (moduleSetsIdentification f M).hom.hom.app ((proEtaleBaseChange f).op.obj U)
        (((AlgebraicGeometry.ProEtale.setPullbackAdjunction f).unit.app
          (moduleSets M)).hom.app U m) = inverseSection f M U.unop m :=
    (Classical.choose_spec (moduleSetsIdentification_exists f M)).1 U.unop m
  refine ⟨{
    ringUnderlying := eR
    modules := inverse f R
    moduleUnderlying := eI.symm
    ringAdd := ?_
    ringMul := ?_
    ringZero := ?_
    ringOne := ?_
    moduleAdd := ?_
    moduleZero := ?_
    moduleSMul := ?_
  }, rfl⟩
  · intro T a b t ht
    exact transport_binary f eR eR eR
      (fun U x y ↦ @Add.add (R.obj.obj U) inferInstance x y)
      (fun V x y ↦ @Add.add ((inverseRing f R).obj.obj V) inferInstance x y)
      (fun i x y ↦ ((inverseRing f R).obj.map i).hom.map_add x y |>.symm)
      (by
        intro U x y
        rw [hr, hr, hr]
        exact (((proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app R).hom.app U).hom.map_add
          x y) T a b t ht
  · intro T a b t ht
    exact transport_binary f eR eR eR
      (fun U x y ↦ @Mul.mul (R.obj.obj U) inferInstance x y)
      (fun V x y ↦ @Mul.mul ((inverseRing f R).obj.obj V) inferInstance x y)
      (fun i x y ↦ ((inverseRing f R).obj.map i).hom.map_mul x y |>.symm)
      (by
        intro U x y
        rw [hr, hr, hr]
        exact (((proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app R).hom.app U).hom.map_mul
          x y) T a b t ht
  · intro T a ha
    exact transport_binary f eR eR eR
      (fun U _ _ ↦ (0 : R.obj.obj U))
      (fun V _ _ ↦ (0 : (inverseRing f R).obj.obj V))
      (fun i _ _ ↦ ((inverseRing f R).obj.map i).hom.map_zero.symm)
      (by
        intro U x y
        rw [hr]
        exact (((proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app R).hom.app U).hom.map_zero)
      T a a a ha
  · intro T a ha
    exact transport_binary f eR eR eR
      (fun U _ _ ↦ (1 : R.obj.obj U))
      (fun V _ _ ↦ (1 : (inverseRing f R).obj.obj V))
      (fun i _ _ ↦ ((inverseRing f R).obj.map i).hom.map_one.symm)
      (by
        intro U x y
        rw [hr]
        exact (((proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app R).hom.app U).hom.map_one)
      T a a a ha
  · intro M T a b t ht
    exact transport_binary f (moduleSetsIdentification f M) (moduleSetsIdentification f M)
      (moduleSetsIdentification f M)
      (fun U x y ↦ @Add.add (M.val.obj U) inferInstance x y)
      (fun V x y ↦ @Add.add (((inverse f R).obj M).val.obj V) inferInstance x y)
      (fun i x y ↦ (((inverse f R).obj M).val.map i).hom.map_add x y |>.symm)
      (by intro U x y; rw [hm, hm, hm]; exact inverseSection_add f M U.unop x y)
      T a b t ht
  · intro M T a ha
    exact transport_binary f (moduleSetsIdentification f M) (moduleSetsIdentification f M)
      (moduleSetsIdentification f M)
      (fun U _ _ ↦ (0 : M.val.obj U))
      (fun V _ _ ↦ (0 : ((inverse f R).obj M).val.obj V))
      (fun i _ _ ↦ (((inverse f R).obj M).val.map i).hom.map_zero.symm)
      (by
        intro U x y
        rw [hm]
        exact (((SheafOfModules.pullbackPushforwardAdjunction
          (proEtaleModelRingUnit f R)).unit.app
            ((proEtaleModuleToModel ((sheafCompose (ProEt.topology Y)
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)).obj M)).val.app
                (op ((AsSmall.up : Y.ProEt ⥤ proEtaleSiteModel Y).obj U.unop))).hom.map_zero)
      T a a a ha
  · intro M T a b t ht
    exact transport_binary f eR (moduleSetsIdentification f M) (moduleSetsIdentification f M)
      (fun U x y ↦ @SMul.smul (R.obj.obj U) (M.val.obj U) inferInstance x y)
      (fun V x y ↦ @SMul.smul ((inverseRing f R).obj.obj V)
        (((inverse f R).obj M).val.obj V) inferInstance x y)
      (fun i x y ↦ (((inverse f R).obj M).val.map_smul i x y).symm)
      (by intro U x y; rw [hm, hr, hm]; exact inverseSection_smul f M U.unop x y)
      T a b t ht

end AlgebraicGeometry.Scheme
