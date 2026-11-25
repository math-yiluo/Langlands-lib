/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.Picard.TwistedDescent
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

public import WeilConjectures.AlgebraicGeometry.DirectedPerfectHomIso

public import WeilConjectures.AlgebraicGeometry.TwoOpenComparisonDiagram


/-! # Types of the prescribed overlap comparisons

Source: Stacks Project, Tags 09RE and 09RF.
(blueprint: def-pc-perfect-overlap-hom-continuity-data).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products

attribute [local instance 2000] openComparisonModuleAbelian openComparisonOverModuleAbelian
  schemeOpenRestriction_additive schemeOpenRestriction_preservesFiniteLimits
  schemeOpenRestriction_preservesFiniteColimits schemeOpenOverlapRestriction_additive
  schemeOpenOverlapRestriction_preservesFiniteLimits
  schemeOpenOverlapRestriction_preservesFiniteColimits

/-- Functorial transports and object comparisons for a simultaneous restriction diagram.
All data is supplied as structure fields; the equations retain the given comparisons.
Source: Stacks Project, Tags 08DW and 0D5S.
(blueprint: def-pc-perfect-overlap-hom-continuity-data). -/
structure TwoOpenTransportData
    {A₀ B₀ A₁ B₁ P₀ Q₀ P₁ Q₁ C : Type*}
    [Category* A₀] [Category* B₀] [Category* A₁] [Category* B₁]
    [Category* P₀] [Category* Q₀] [Category* P₁] [Category* Q₁] [Category* C]
    (D : Type*) (HU : D → A₁ ⥤ P₁) (HV : D → B₁ ⥤ Q₁)
    (FU : A₀ ⥤ A₁) (FV : B₀ ⥤ B₁) (GU : A₀ ⥤ P₀) (GV : B₀ ⥤ Q₀)
    (LU : P₀ ⥤ P₁) (LV : Q₀ ⥤ Q₁)
    (PU : C ⥤ P₀) (PV : C ⥤ Q₀) (RU : C ⥤ P₁) (RV : C ⥤ Q₁)
    (A : A₀) (B : B₀) (E : C)
    (φU : GU.obj A ≅ PU.obj E) (φV : GV.obj B ≅ PV.obj E) where
  d : D
  κU : FU ⋙ HU d ≅ GU ⋙ LU
  κV : FV ⋙ HV d ≅ GV ⋙ LV
  siteU : PU ⋙ LU ≅ RU
  siteV : PV ⋙ LV ≅ RV
  θU : (HU d).obj (FU.obj A) ≅ RU.obj E
  θV : (HV d).obj (FV.obj B) ≅ RV.obj E
  hθU : θU = κU.app A ≪≫ LU.mapIso φU ≪≫ siteU.app E
  hθV : θV = κV.app B ≪≫ LV.mapIso φV ≪≫ siteV.app E

-- Exact open restriction comparisons need this instance-search budget.
/-- Real comparison data at every later stage, without an overlap transition.
The final fields pin both local identifications to the supplied comparisons.
Source: Stacks Project, Tags 08DW and 0D5S.
(blueprint: def-pc-perfect-overlap-hom-continuity-data). -/
noncomputable def perfectOverlapComparisonDataType
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (i : I) (Z : Scheme.{u}) (t : Z ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation t] [QuasiCompact t] [QuasiSeparated t]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    (j : I) (hij : i ≤ j)
    (hstage : ∀ (U V : (pullback t (Spec.map (R.map (homOfLE hij)))).Opens),
      ∃ k : I, j ≤ k)
    :
    let Yj := pullback t (Spec.map (R.map (homOfLE hij)))
    let X := pullback t (Spec.map (c.ι.app i))
    let gj := baseChangeMap t
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (Spec.map (c.ι.app i)))
      (Over.homMk (Spec.map (c.ι.app j))
        (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)]))
    ∀ (U V : Yj.Opens) (hcover : U ⊔ V = ⊤)
      (hU : IsCompact (U : Set Yj)) (hV : IsCompact (V : Set Yj))
      (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
      (hA : U.toScheme.IsPerfect A) (hB : V.toScheme.IsPerfect B)
      (E : schemeDerivedCategory X),
    let instP : Category (schemeDerivedCategory (gj ⁻¹ᵁ U).toScheme) := inferInstance
    let instQ : Category (schemeDerivedCategory (gj ⁻¹ᵁ V).toScheme) := inferInstance
    let instX : Category (schemeDerivedCategory X) := inferInstance
    let PU : schemeDerivedCategory X ⥤ schemeDerivedCategory (gj ⁻¹ᵁ U).toScheme :=
      (schemeOpenRestriction X (gj ⁻¹ᵁ U)).mapDerivedCategory
    let PV : schemeDerivedCategory X ⥤ schemeDerivedCategory (gj ⁻¹ᵁ V).toScheme :=
      (schemeOpenRestriction X (gj ⁻¹ᵁ V)).mapDerivedCategory
    ∀ (φU : (derivedPullback (gj ∣_ U)).obj A ≅
        PU.obj E)
      (φV : (derivedPullback (gj ∣_ V)).obj B ≅
        PV.obj E),
    ∀ (k : I) (hjk : j ≤ k), Type (max (u + 1) w) := by
  intro Yj X gj U V hcover hU hV A B hA hB E instP instQ instX PU PV φU φV k hjk
  exact
      let g := baseChangeMap t
        (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
        (T' := Over.mk (Spec.map (c.ι.app i)))
        (Over.homMk (Spec.map (c.ι.app k))
          (by dsimp; rw [← Spec.map_comp, c.w (homOfLE (hij.trans hjk))]))
      let Yk := pullback t (Spec.map (R.map (homOfLE (hij.trans hjk))))
      let f := baseChangeMap t
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
        (Over.homMk (Spec.map (R.map (homOfLE hjk)))
          (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
      let U' := f ⁻¹ᵁ U
      let V' := f ⁻¹ᵁ V
      let instY : Category (schemeDerivedCategory Yk) := inferInstance
      let instU : Category (schemeDerivedCategory U'.toScheme) := inferInstance
      let instV : Category (schemeDerivedCategory V'.toScheme) := inferInstance
      let instW : Category (schemeDerivedCategory (U' ⊓ V').toScheme) := inferInstance
      let A' : schemeDerivedCategory U'.toScheme := (derivedPullback (f ∣_ U)).obj A
      let B' : schemeDerivedCategory V'.toScheme := (derivedPullback (f ∣_ V)).obj B
      let SU : schemeDerivedCategory U'.toScheme ⥤
          schemeDerivedCategory (U' ⊓ V').toScheme := (schemeOpenOverlapRestriction Yk
        (homOfLE (show U' ⊓ V' ≤ U' from inf_le_left))).mapDerivedCategory
      let SV : schemeDerivedCategory V'.toScheme ⥤
          schemeDerivedCategory (U' ⊓ V').toScheme := (schemeOpenOverlapRestriction Yk
        (homOfLE (show U' ⊓ V' ≤ V' from inf_le_right))).mapDerivedCategory
      let TU : schemeDerivedCategory Yk ⥤ schemeDerivedCategory U'.toScheme :=
        (schemeOpenRestriction Yk U').mapDerivedCategory
      let TV : schemeDerivedCategory Yk ⥤ schemeDerivedCategory V'.toScheme :=
        (schemeOpenRestriction Yk V').mapDerivedCategory
      let TW : schemeDerivedCategory Yk ⥤ schemeDerivedCategory (U' ⊓ V').toScheme :=
        (schemeOpenRestriction Yk (U' ⊓ V')).mapDerivedCategory
      let αU : TU ⋙ SU ≅ TW := schemeDerivedOpenRestrictionCompIso Yk
        (homOfLE (show U' ⊓ V' ≤ U' from inf_le_left))
      let αV : TV ⋙ SV ≅ TW := schemeDerivedOpenRestrictionCompIso Yk
        (homOfLE (show U' ⊓ V' ≤ V' from inf_le_right))
      let P := gj ⁻¹ᵁ U
      let Q := gj ⁻¹ᵁ V
      let RU := (SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) P).mapDerivedCategory
      let RV := (SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) Q).mapDerivedCategory
      let RW := (SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) (P ⊓ Q)).mapDerivedCategory
      let SP := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE (show P ⊓ Q ≤ P from inf_le_left))).mapDerivedCategory
      let SQ := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE (show P ⊓ Q ≤ Q from inf_le_right))).mapDerivedCategory
      let τU : RU ⋙ SP ≅ RW := Functor.mapDerivedCategoryCompIso _ _ ≪≫
        Functor.mapDerivedCategoryNatIso (SheafOfModules.overFunctorMap.{u}
          (moduleRings X.toRingedSpace) (homOfLE (show P ⊓ Q ≤ P from inf_le_left)))
      let τV : RV ⋙ SQ ≅ RW := Functor.mapDerivedCategoryCompIso _ _ ≪≫
        Functor.mapDerivedCategoryNatIso (SheafOfModules.overFunctorMap.{u}
          (moduleRings X.toRingedSpace) (homOfLE (show P ⊓ Q ≤ Q from inf_le_right)))
      let LU := (Equivalence.inverse
        (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over P))
        (D := SheafOfModules.{u} (moduleRings P.toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv P)).mapDerivedCategory
      let LV := (Equivalence.inverse
        (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over Q))
        (D := SheafOfModules.{u} (moduleRings Q.toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv Q)).mapDerivedCategory
      TwoOpenTransportData (SchemeTwoOpenComparisonDiagram X Yk g U' V' P Q)
        (fun d ↦ d.toDiagram.HU) (fun d ↦ d.toDiagram.HV)
        (derivedPullback (f ∣_ U)) (derivedPullback (f ∣_ V))
        (derivedPullback (gj ∣_ U)) (derivedPullback (gj ∣_ V))
        LU LV PU PV RU RV A B E φU φV

-- Exact open restriction comparisons need this instance-search budget.
/-- The Hom-continuity proposition with dependent stage expressions kept behind an API.
Source: Stacks Project, Tag 09RE.
(blueprint: def-pc-perfect-overlap-hom-continuity-data). -/
noncomputable def perfectOverlapHomContinuityStatement
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (i : I) (Z : Scheme.{u}) (t : Z ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation t] [QuasiCompact t] [QuasiSeparated t]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    (j : I) (hij : i ≤ j)
    (hstage : ∀ (U V : (pullback t (Spec.map (R.map (homOfLE hij)))).Opens),
      ∃ k : I, j ≤ k)
    : Prop :=
    let Yj := pullback t (Spec.map (R.map (homOfLE hij)))
    let X := pullback t (Spec.map (c.ι.app i))
    let gj := baseChangeMap t
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (Spec.map (c.ι.app i)))
      (Over.homMk (Spec.map (c.ι.app j))
        (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)]))
    ∀ (U V : Yj.Opens) (hcover : U ⊔ V = ⊤)
      (hU : IsCompact (U : Set Yj)) (hV : IsCompact (V : Set Yj))
      (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
      (hA : U.toScheme.IsPerfect A) (hB : V.toScheme.IsPerfect B)
      (E : schemeDerivedCategory X),
    let instP : Category (schemeDerivedCategory (gj ⁻¹ᵁ U).toScheme) := inferInstance
    let instQ : Category (schemeDerivedCategory (gj ⁻¹ᵁ V).toScheme) := inferInstance
    let instX : Category (schemeDerivedCategory X) := inferInstance
    let PU : schemeDerivedCategory X ⥤ schemeDerivedCategory (gj ⁻¹ᵁ U).toScheme :=
      (schemeOpenRestriction X (gj ⁻¹ᵁ U)).mapDerivedCategory
    let PV : schemeDerivedCategory X ⥤ schemeDerivedCategory (gj ⁻¹ᵁ V).toScheme :=
      (schemeOpenRestriction X (gj ⁻¹ᵁ V)).mapDerivedCategory
    ∀ (φU : (derivedPullback (gj ∣_ U)).obj A ≅
        PU.obj E)
      (φV : (derivedPullback (gj ∣_ V)).obj B ≅
        PV.obj E),
      let P := gj ⁻¹ᵁ U
      let Q := gj ⁻¹ᵁ V
      let RU := (SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) P).mapDerivedCategory
      let RV := (SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) Q).mapDerivedCategory
      let RW := (SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) (P ⊓ Q)).mapDerivedCategory
      let SP := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE (show P ⊓ Q ≤ P from inf_le_left))).mapDerivedCategory
      let SQ := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE (show P ⊓ Q ≤ Q from inf_le_right))).mapDerivedCategory
      let τU : RU ⋙ SP ≅ RW := Functor.mapDerivedCategoryCompIso _ _ ≪≫
        Functor.mapDerivedCategoryNatIso (SheafOfModules.overFunctorMap.{u}
          (moduleRings X.toRingedSpace) (homOfLE (show P ⊓ Q ≤ P from inf_le_left)))
      let τV : RV ⋙ SQ ≅ RW := Functor.mapDerivedCategoryCompIso _ _ ≪≫
        Functor.mapDerivedCategoryNatIso (SheafOfModules.overFunctorMap.{u}
          (moduleRings X.toRingedSpace) (homOfLE (show P ⊓ Q ≤ Q from inf_le_right)))
    Nonempty (
      Σ data : (k : I) → (hjk : j ≤ k) →
        perfectOverlapComparisonDataType R c hc i Z t j hij hstage
          U V hcover hU hV A B hA hB E φU φV k hjk,
      let K := {k : I // j ≤ k}
      let C : K → Type (u + 1) := fun k ↦
        let Yk := pullback t (Spec.map (R.map (homOfLE (hij.trans k.property))))
        let f := baseChangeMap t
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans k.property)))))
          (Over.homMk (Spec.map (R.map (homOfLE k.property)))
            (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
        let U' := f ⁻¹ᵁ U
        let V' := f ⁻¹ᵁ V
        schemeDerivedCategory (U' ⊓ V').toScheme
      let F : (k : K) → Bool → C k := fun k b ↦
        let Yk := pullback t (Spec.map (R.map (homOfLE (hij.trans k.property))))
        let f := baseChangeMap t
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans k.property)))))
          (Over.homMk (Spec.map (R.map (homOfLE k.property)))
            (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
        let U' := f ⁻¹ᵁ U
        let V' := f ⁻¹ᵁ V
        let A' : schemeDerivedCategory U'.toScheme := (derivedPullback (f ∣_ U)).obj A
        let B' : schemeDerivedCategory V'.toScheme := (derivedPullback (f ∣_ V)).obj B
        let SU : schemeDerivedCategory U'.toScheme ⥤
            schemeDerivedCategory (U' ⊓ V').toScheme := (schemeOpenOverlapRestriction Yk
          (homOfLE (show U' ⊓ V' ≤ U' from inf_le_left))).mapDerivedCategory
        let SV : schemeDerivedCategory V'.toScheme ⥤
            schemeDerivedCategory (U' ⊓ V').toScheme := (schemeOpenOverlapRestriction Yk
          (homOfLE (show U' ⊓ V' ≤ V' from inf_le_right))).mapDerivedCategory
        if b then SV.obj B' else SU.obj A'
      let G : (k : K) → C k ⥤
          DerivedCategory (SheafOfModules.{u}
            ((moduleRings X.toRingedSpace).over (P ⊓ Q))) := fun k ↦
        (data k.val k.property).d.toDiagram.HW
      let ψ : ∀ k b, (G k).obj (F k b) ≅ RW.obj E := fun k b ↦
        let Yk := pullback t (Spec.map (R.map (homOfLE (hij.trans k.property))))
        let f := baseChangeMap t
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans k.property)))))
          (Over.homMk (Spec.map (R.map (homOfLE k.property)))
            (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
        let U' := f ⁻¹ᵁ U
        let V' := f ⁻¹ᵁ V
        let A' : schemeDerivedCategory U'.toScheme := (derivedPullback (f ∣_ U)).obj A
        let B' : schemeDerivedCategory V'.toScheme := (derivedPullback (f ∣_ V)).obj B
        let d := (data k.val k.property).d
        let θU := (data k.val k.property).θU
        let θV := (data k.val k.property).θV
        match b with
        | true => d.toDiagram.γV.symm.app B' ≪≫ SQ.mapIso θV ≪≫ τV.app E
        | false => d.toDiagram.γU.symm.app A' ≪≫ SP.mapIso θU ≪≫ τU.app E
      DirectedPerfectHomSystem K C F _ (fun _ ↦ RW.obj E) G ψ)

end AlgebraicGeometry
