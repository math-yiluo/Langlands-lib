/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.LinearAlgebra.TensorProduct.Tower
import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologySeparated
import Mathlib.RingTheory.Flat.Localization

/-! # Degree-zero base change to the fraction field

Source: Stacks Project, Cohomology of Schemes, Tag 02KH, degree zero.
(blueprint: lem-sc-fraction-field-sections-base-change)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped AlgebraicGeometry.Scheme.Modules TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

open CategoryTheory.Abelian TopologicalSpace in
set_option backward.isDefEq.respectTransparency.types false in
/-- In degree zero the exact inverse-image Ext map is the map on sections
induced by the pullback adjunction unit. This follows from the definition of
`constIso` by uniqueness of left adjoints and the constant-sheaf adjunction. -/
private theorem zero_inverseImage {X Y : Scheme.{u}} (g : Y ⟶ X)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (x : F.H 0) :
    Sheaf.H.equiv₀ ((invImage g).obj F) isTerminalTop
      (Sheaf.H.mapFunctor (invImage g) (constIso g).symm F 0 x) =
    (((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g.base).unit.app
      F).hom.app (op ⊤)) (Sheaf.H.equiv₀ F isTerminalTop x) := by
  classical
  let a := constantSheafAdj (Opens.grothendieckTopology X)
    AddCommGrpCat.{u} isTerminalTop
  let b := constantSheafAdj (Opens.grothendieckTopology Y)
    AddCommGrpCat.{u} isTerminalTop
  let adj := (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g.base)
  let z := AddCommGrpCat.of (ULift.{u} ℤ)
  let h := Ext.addEquiv₀ x
  have hx : x = Ext.mk₀ h := (Ext.mk₀_addEquiv₀_apply x).symm
  rw [hx]
  simp only [Sheaf.H.mapFunctor_apply, Ext.mapExactFunctor_mk₀]
  rw [Ext.mk₀_comp_mk₀]
  simp only [Sheaf.H.equiv₀, AddEquiv.trans_apply]
  have hm (P Q : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      (q : P ⟶ Q) : Ext.addEquiv₀ (Ext.mk₀ q) = q :=
    (Ext.addEquiv₀ : Ext P Q 0 ≃+ (P ⟶ Q)).apply_symm_apply q
  have hm' (P Q : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})
      (q : P ⟶ Q) : Ext.addEquiv₀ (Ext.mk₀ q) = q :=
    (Ext.addEquiv₀ : Ext P Q 0 ≃+ (P ⟶ Q)).apply_symm_apply q
  rw [hm, hm']
  change (b.homEquiv z _ ((constIso g).inv ≫ (invImage g).map h)) (ULift.up 1) =
    ((adj.unit.app F).hom.app (op ⊤)) ((a.homEquiv z F h) (ULift.up 1))
  let iso := (Opens.map g.base).sheafPushforwardContinuousCompSheafSectionsObjIso
    AddCommGrpCat.{u} (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) (op ⊤)
  let ab := (a.comp adj).ofNatIsoRight iso
  have hi := Adjunction.unit_leftAdjointUniq_hom_app b ab z
  have he : b.homEquiv z _ ((constIso g).inv ≫ (invImage g).map h) =
      ab.homEquiv z _ ((invImage g).map h) := by
    rw [Adjunction.homEquiv_apply, Adjunction.homEquiv_apply, Functor.map_comp]
    rw [← Category.assoc]
    have hi' : b.unit.app z ≫
        ((sheafSections (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj (op ⊤)).map
          (constIso g).inv = ab.unit.app z := by
      change b.unit.app z ≫
        ((sheafSections (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj (op ⊤)).map
          ((ab.leftAdjointUniq b).inv.app z) = ab.unit.app z
      rw [Adjunction.leftAdjointUniq_inv_app]
      exact hi
    rw [hi']
    rfl
  rw [he]
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
  change (a.homEquiv z _ (adj.homEquiv _ _ ((invImage g).map h)) ≫
    iso.hom.app _) (ULift.up 1) = _
  have hn : adj.homEquiv _ _ ((invImage g).map h) = h ≫ adj.unit.app F := by
    rw [Adjunction.homEquiv_apply]
    exact (adj.unit.naturality h).symm
  rw [hn, Adjunction.homEquiv_naturality_right]
  rfl

/-- Flat base change on global sections, including its normalization on pure tensors.

Source: Stacks Project, Cohomology of Schemes, Tag 02KH, degree zero; More on
Morphisms, Tag 0EX8, general-case proof, displayed base-change equality.
(blueprint: lem-sc-fraction-field-sections-base-change)

Proof: The fraction field is a flat A-algebra. For a finite affine open cover of X,
separatedness over the affine base makes finite intersections affine. Quasi-coherence
identifies sections on each base-changed affine with K tensor_A the original sections.
These identifications send 1 tensor s to the adjunction-unit image of s and commute
with restriction. Global sections are the kernel of the first Cech differential.
Flatness preserves that kernel, and tensoring commutes with the finite products
in the first two Cech terms. This gives the asserted K-linear isomorphism and its
formula. Equivalently, apply the separated flat-cohomology comparison in degree zero
and identify H^0 with sections, tracking the augmentation. On the empty scheme both
sides are zero. No properness, valuation hypothesis, or triviality is used. -/
theorem exists_fractionField_sections_baseChange
    (A : Type u) [CommRing A] [IsDomain A]
    (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
    {X : Scheme.{u}} [CompactSpace X]
    (f : X ⟶ Spec (CommRingCat.of A)) [IsSeparated f]
    (L : X.Modules) [L.IsQuasicoherent] :
    let g := pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A K)))
    let fK := pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A K)))
    let M := (ModuleCat.restrictScalars
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).obj
      ((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).obj L)
    let MK := (ModuleCat.restrictScalars
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ fK.appTop).hom).obj
      ((SheafOfModules.evaluation _ (op ⊤)).obj ((Modules.pullback g).obj L))
    ∃ e : K ⊗[A] M ≃ₗ[K] MK,
      ∀ s : Γ(L, ⊤), e (1 ⊗ₜ[A] s) =
        ((pullbackPushforwardAdjunction g).unit.app L).app ⊤ s := by
  classical
  let : Module.Flat A K := IsLocalization.flat K (nonZeroDivisors A)
  dsimp only
  let g := baseChangeFst (S := K) f
  let fK := baseChangeSnd (S := K) f
  let N := baseChangedModule (S := K) f L
  let M := (ModuleCat.restrictScalars
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).obj
    ((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).obj L)
  let MK := (ModuleCat.restrictScalars
    ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ fK.appTop).hom).obj
    ((SheafOfModules.evaluation _ (op ⊤)).obj N)
  let a : HOver f L 0 ≃ₗ[A] M :=
    { H.zeroLinearEquiv L with
      map_smul' := fun c x ↦ (H.zeroLinearEquiv L).map_smul
        (((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom c) x }
  let b : HOver fK N 0 ≃ₗ[K] MK :=
    { H.zeroLinearEquiv N with
      map_smul' := fun c x ↦ (H.zeroLinearEquiv N).map_smul
        (((Scheme.ΓSpecIso (.of K)).inv ≫ fK.appTop).hom c) x }
  let t := TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl K K) a.symm
  let c := LinearEquiv.ofBijective (H.baseChange (S := K) f L 0)
    (H.baseChange_bijective_of_isSeparated f L 0)
  refine ⟨t.trans (c.trans b), ?_⟩
  intro s
  change b (H.baseChange (S := K) f L 0 (t (1 ⊗ₜ[A] s))) = _
  rw [TensorProduct.AlgebraTensorModule.congr_tmul]
  change b (H.baseChange (S := K) f L 0 (1 ⊗ₜ[A] a.symm s)) = _
  simp only [H.baseChange, extendComparison, TensorProduct.AlgebraTensorModule.lift_tmul,
    LinearMap.coe_mk, AddHom.coe_mk, one_smul]
  change H.zeroLinearEquiv N (H.baseChangeLinear (S := K) f L 0 (a.symm s)) = _
  change Sheaf.H.equiv₀ _ isTerminalTop
    (Sheaf.H.map (coeff g (baseChangeUnit (S := K) f L)) 0
      (Sheaf.H.mapFunctor (invImage g) (constIso g).symm _ 0 (a.symm s))) = _
  rw [← Sheaf.H.equiv₀_naturality, zero_inverseImage]
  change ((coeff g (baseChangeUnit (S := K) f L)).hom.app (op ⊤))
    (((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g.base).unit.app
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj L)).hom.app (op ⊤)
        ((H.zeroLinearEquiv L) ((H.zeroLinearEquiv L).symm s))) = _
  rw [LinearEquiv.apply_symm_apply]
  have hunit := (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g.base)
    |>.homEquiv_apply _ _ (coeff g (baseChangeUnit (S := K) f L))
  rw [coeff, Equiv.apply_symm_apply] at hunit
  exact (ConcreteCategory.congr_hom
    (congrArg (fun q ↦ q.hom.app (op ⊤)) hunit) s).symm

end AlgebraicGeometry.Scheme.Modules
