/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.CategoryTheory.Monad.Adjunction
import WeilConjectures.Algebra.Homology.OpenExtensionRestrictionIso
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.AlgebraicGeometry.OpenPerfectModelTransport

/-! # Initial ambient representative of a supported perfect map

Source: Stacks Project, Tags 08BT and 09IM.
(blueprint: lem-sc-supported-map-initial-ambient-lift).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- Localize the degreewise exact adjunction and transpose a map across its invertible unit.
Source: Stacks Project, Tag 08BT and Tag 00A7 (4). -/
private theorem exact_adjunction_lifts_map
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
    (l : C ⥤ D) (r : D ⥤ C) [l.Additive] [r.Additive]
    [PreservesFiniteLimits l] [PreservesFiniteColimits l]
    [PreservesFiniteLimits r] [PreservesFiniteColimits r]
    (a : l ⊣ r) (c : l ⋙ r ≅ 𝟭 C)
    (F : DerivedCategory C) (E : DerivedCategory D)
    (α : F ⟶ r.mapDerivedCategory.obj E) :
    ∃ (R : DerivedCategory D) (β : R ⟶ E)
      (e : r.mapDerivedCategory.obj R ≅ F), r.mapDerivedCategory.map β = e.hom ≫ α := by
  let : CatCommSq (l.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q l.mapDerivedCategory := ⟨l.mapDerivedCategoryFactors.symm⟩
  let : CatCommSq (r.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q r.mapDerivedCategory := ⟨r.mapDerivedCategoryFactors.symm⟩
  let d : l.mapDerivedCategory ⊣ r.mapDerivedCategory :=
    (a.mapHomologicalComplex (.up ℤ)).localization
      DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
      DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
      l.mapDerivedCategory r.mapDerivedCategory
  let ff := d.fullyFaithfulLOfCompIsoId
    (Functor.mapDerivedCategoryCompIso l r ≪≫
      Functor.mapDerivedCategoryNatIso c ≪≫ Functor.mapDerivedCategoryIdIso _)
  let : l.mapDerivedCategory.Full := ff.full
  let : l.mapDerivedCategory.Faithful := ff.faithful
  let R := l.mapDerivedCategory.obj F
  let β : R ⟶ E := (d.homEquiv F E).symm α
  let e : r.mapDerivedCategory.obj R ≅ F :=
    (asIso (d.unit.app F)).symm
  refine ⟨R, β, e, ?_⟩
  have h : d.unit.app F ≫ r.mapDerivedCategory.map β = α := by
    exact (d.homEquiv_unit F E β).symm.trans
      ((d.homEquiv F E).apply_symm_apply α)
  calc
    r.mapDerivedCategory.map β =
        e.hom ≫ (d.unit.app F ≫ r.mapDerivedCategory.map β) := by
      change _ = (asIso (d.unit.app F)).inv ≫
        ((asIso (d.unit.app F)).hom ≫ _)
      rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    _ = e.hom ≫ α := by rw [h]

set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Exact restriction preserves the homology stalks at points of the open.
Source: Stacks Project, Tags 08DW and 06Z0. -/
private theorem openRestriction_support (X : Scheme.{u}) (U : X.Opens) (T : Set X)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    (R : schemeDerivedCategory X) (F : schemeDerivedCategory U.toScheme)
    (e : (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
        (Modules.overEquiv U)).mapDerivedCategory.obj R ≅ F)
    (hFT : ∀ (i : ℤ) (x : U.toScheme), x.val ∉ T →
      Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) i).obj F).val.presheaf x))) :
    ∀ (i : ℤ) (x : X), x ∈ U → x ∉ T →
      Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj R).val.presheaf x)) := by
  intro i x hx hxT
  let H := Modules.toPresheaf U.toScheme ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (⟨x, hx⟩ : U.toScheme)
  let r := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
    Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Modules.overEquiv U)
  let M := (DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj R
  let c := H.mapIso ((DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) i).mapIso e)
  let s := H.mapIso ((r.mapDerivedCategoryHomologyFunctorIso i).symm.app R) ≪≫
    H.mapIso ((Modules.overFunctorEquiv U).app M) ≪≫
      (Modules.restrictStalkNatIso U.ι (⟨x, hx⟩ : U.toScheme)).app M
  exact (s.symm ≪≫ c).addCommGroupIsoToAddEquiv.toEquiv.subsingleton_congr.mpr
    (hFT i ⟨x, hx⟩ hxT)

set_option backward.isDefEq.respectTransparency false in
/-- A supported perfect source and map on an open have an ambient representative
which is perfect and supported at the points of that open. No perfectness is asserted
outside the open.
Source: Stacks Project, Tags 08BT, 00A7 (4), and 09IM (initial object of the induction).
(blueprint: lem-sc-supported-map-initial-ambient-lift).

Proof: Apply the inverse of Modules.overEquiv U to F and then exact extension by
zero to X. These are actual functors: no arbitrary existence witness defines the
source. The exact extension-by-zero/restriction adjunction induces a derived
adjunction. The adjoint of α, after the equivalence comparisons, is β. The unit
is invertible since extension by zero restricts to the identity on U. Let e be
its inverse, transported to the open subscheme. The adjunction unit equation gives
β restricted to U = e.hom followed by α. At x in U extension by zero has the same
cohomology stalk as F, proving support. Transport a strictly perfect local model
of F at x along the equivalence of the localized site with the open subscheme.
The bounded complex and its finite-free retracts transport termwise, providing
O and K in the displayed local perfectness condition. The construction works for
empty U and zero F, and does not assert that extension by zero is globally perfect. -/
theorem exists_supported_map_initial_ambient_lift
    (X : Scheme.{u}) (U : X.Opens) (T : Set X)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [∀ V : U.toScheme.Opens,
      HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))]
    (E : schemeDerivedQCohCategory X)
    (F : schemeDerivedCategory U.toScheme) (hF : IsPerfect U.toScheme F)
    (hFT : ∀ (i : ℤ) (x : U.toScheme), x.val ∉ T →
      Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) i).obj F).val.presheaf x)))
    (α : F ⟶ ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory.obj E.obj) :
    ∃ (R : schemeDerivedCategory X) (β : R ⟶ E.obj),
      (∀ x : X, x ∈ U → ∃ O : X.Opens, x ∈ O ∧
        ∃ K : CochainComplex
            (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over O)) ℤ,
          IsStrictlyPerfect X O K ∧
          Nonempty ((SheafOfModules.overFunctor.{u}
            (moduleRings X.toRingedSpace) O).mapDerivedCategory.obj R ≅
              DerivedCategory.Q.obj K)) ∧
      (∀ (i : ℤ) (x : X), x ∈ U → x ∉ T →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj R).val.presheaf x))) ∧
      ∃ e : ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory.obj R ≅ F,
        ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory.map β = e.hom ≫ α := by
  set_option backward.isDefEq.respectTransparency true in
  all_goals
    classical
    let g := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U
    let L := SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X.toRingedSpace) U ⋙
      PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X.toRingedSpace).obj)
    let q : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U) ≌
        SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) := Modules.overEquiv U
    obtain ⟨hg₁, hg₂, hL₁, hL₂, ⟨adj⟩⟩ :=
      open_restriction_adjunction_exact X.toRingedSpace U
    let : PreservesFiniteLimits g := hg₁
    let : PreservesFiniteColimits g := hg₂
    let : PreservesFiniteLimits L := hL₁
    let : PreservesFiniteColimits L := hL₂
    let : q.functor.Additive := Functor.additive_of_preserves_binary_products _
    let : q.inverse.Additive := Functor.additive_of_preserves_binary_products _
    let : L.IsLeftAdjoint := adj.isLeftAdjoint
    let : L.Additive := Functor.additive_of_preserves_binary_products _
    let a : (q.inverse ⋙ L) ⊣ (g ⋙ q.functor) := q.symm.toAdjunction.comp adj
    obtain ⟨c⟩ := nonempty_openExtensionRestrictionIso X.toRingedSpace U
    let c' : (q.inverse ⋙ L) ⋙ (g ⋙ q.functor) ≅ 𝟭 _ :=
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft q.inverse (Functor.associator L g q.functor).symm ≪≫
        Functor.isoWhiskerLeft q.inverse (Functor.isoWhiskerRight c q.functor) ≪≫
        Functor.isoWhiskerLeft q.inverse (Functor.leftUnitor q.functor) ≪≫ q.counitIso
    let l := q.inverse ⋙ L
    let r := g ⋙ q.functor
    let : PreservesFiniteLimits l := comp_preservesFiniteLimits _ _
    let : PreservesFiniteColimits l := comp_preservesFiniteColimits _ _
    let : PreservesFiniteLimits r := comp_preservesFiniteLimits _ _
    let : PreservesFiniteColimits r := comp_preservesFiniteColimits _ _
    let : l.IsLeftAdjoint := a.isLeftAdjoint
    let : r.IsRightAdjoint := a.isRightAdjoint
    let : l.Additive := Functor.additive_of_preserves_binary_products l
    let : r.Additive := Functor.additive_of_preserves_binary_products r
    obtain ⟨R, β, e, he⟩ := exact_adjunction_lifts_map l r a c' F E.obj α
    refine ⟨R, β, ?_, ?_, e, ?_⟩
    · exact local_perfect_of_openRestriction_iso X U R F hF e
    · exact openRestriction_support X U T R F e hFT
    · exact he

end AlgebraicGeometry.Scheme
