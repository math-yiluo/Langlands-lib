/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
import all WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
import all WeilConjectures.AlgebraicGeometry.RegularExtensionComparison
import all WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# A specified scalar presentation after extension to coefficient sheaves

The coefficient functor and scalar matrix are the existing local-model constructions.
Matrix entries are maps from the integer tensor unit, equivalently elements of Λ(*).
Their first index is the source column and their second index is the target row.

## References

* Stacks, Modules on Sites, Tags 03CY, 03CZ, 0GMW and Section 03EK
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A specified finite scalar presentation remains a cokernel diagram after taking
constant module sheaves and extending scalars to Λ_U. The free comparisons send
`1 ⊗ e_j` to `e_j`; the final cokernel comparison commutes with the specified quotient. -/
theorem scalar_presentation_cokernel
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (U : Scheme.{u}) (m n : ℕ)
    (A : Fin m → Fin n → (𝟙_ Ab.{u + 1} ⟶ scalarRingObj Λ))
    (P : Mod Ab.{u + 1} (scalarRingObj Λ))
    (q : Mod.finiteFree (scalarRingObj Λ) n ⟶ P)
    (hAq : (biproduct.matrix fun j i ↦
      Mod.regularLift (Mod.regular (scalarRingObj Λ)) (A j i)) ≫ q = 0)
    (hq : IsColimit (CokernelCofork.ofπ q hAq)) :
    ∃ e : ∀ r : ℕ,
        (finiteConstantScalarExtension Λ U).obj (Mod.finiteFree (scalarRingObj Λ) r) ≅
          Mod.finiteFree (condensedRingObj Λ U) r,
      (∀ (r : ℕ) (j : Fin r),
        Functor.LaxMonoidal.ε (scalarConstant U) ≫
          (scalarConstant U).map
            ((MonObj.one : 𝟙_ Ab.{u + 1} ⟶ scalarRingObj Λ) ≫
              (biproduct.ι (fun _ : Fin r ↦ Mod.regular (scalarRingObj Λ)) j).hom) ≫
          Mod.extendUnitHom (scalarCoefficientHom Λ U)
            (((scalarConstant U).mapMod (scalarRingObj Λ)).obj
              (Mod.finiteFree (scalarRingObj Λ) r)) ≫ (e r).hom.hom =
          (MonObj.one : 𝟙_ (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) ⟶
            condensedRingObj Λ U) ≫
              (biproduct.ι (fun _ : Fin r ↦ Mod.regular (condensedRingObj Λ U)) j).hom) ∧
      ((e m).inv ≫ (finiteConstantScalarExtension Λ U).map
          (biproduct.matrix fun j i ↦
            Mod.regularLift (Mod.regular (scalarRingObj Λ)) (A j i)) ≫ (e n).hom =
        scalarMatrix Λ U A) ∧
      ∃ h : scalarMatrix Λ U A ≫ (e n).inv ≫
          (finiteConstantScalarExtension Λ U).map q = 0,
        Nonempty (IsColimit (CokernelCofork.ofπ
          ((e n).inv ≫ (finiteConstantScalarExtension Λ U).map q) h)) ∧
        ∃ c : (finiteConstantScalarExtension Λ U).obj P ≅ cokernel (scalarMatrix Λ U A),
          (e n).inv ≫ (finiteConstantScalarExtension Λ U).map q ≫ c.hom =
            cokernel.π (scalarMatrix Λ U A) := by
  let e := scalarFreeIso Λ U
  refine ⟨e, ?_, scalarMatrix_map Λ U A, ?_⟩
  · intro r j
    let F := scalarConstant U
    let R := scalarRingObj Λ
    let φ := scalarCoefficientHom Λ U
    let M := (F.mapMod R).obj (Mod.regular R)
    let N := (F.mapMod R).obj (Mod.finiteFree R r)
    let i := (F.mapMod R).map (biproduct.ι (fun _ : Fin r ↦ Mod.regular R) j)
    have hn : i.hom ≫ Mod.extendUnitHom φ N =
        Mod.extendUnitHom φ M ≫ ((Mod.extendScalars φ).map i).hom := by
      exact congrArg Mod.Hom.hom ((Mod.extendRestrictAdjunction φ).unit.naturality i)
    have hi : (finiteConstantScalarExtension Λ U).map
        (biproduct.ι (fun _ : Fin r ↦ Mod.regular R) j) ≫ (e r).hom =
        (scalarRegularIso Λ U).hom ≫
          biproduct.ι (fun _ : Fin r ↦ Mod.regular (condensedRingObj Λ U)) j := by
      let H := finiteConstantScalarExtension Λ U
      have hι : H.map (biproduct.ι (fun _ : Fin r ↦ Mod.regular R) j) ≫
          (H.mapBiproduct (fun _ : Fin r ↦ Mod.regular R)).hom =
          biproduct.ι (fun k : Fin r ↦ H.obj (Mod.regular R)) j := by
        apply (Iso.eq_comp_inv _).mp
        simp only [Functor.mapBiproduct_inv, biproduct.ι_desc]
      dsimp only [e, scalarFreeIso, Iso.trans_hom]
      rw [← Category.assoc, hι, biproduct.mapIso_hom, biproduct.ι_map]
    have hr : Mod.extendUnitHom φ M ≫ (scalarRegularIso Λ U).hom.hom = φ := by
      dsimp only [scalarRegularIso, Iso.trans_hom, Functor.mapIso_hom, Mod.comp_hom']
      change Mod.extendUnitHom φ (Mod.regular (F.obj R)) ≫
        ((Mod.extendScalars φ).map (𝟙 _)).hom ≫
          (Mod.regularExtensionIso φ).hom.hom = φ
      rw [CategoryTheory.Functor.map_id]
      change Mod.extendUnitHom φ (Mod.regular (F.obj R)) ≫
        (𝟙 _ ≫ (Mod.regularExtensionIso φ).hom.hom) = φ
      rw [Category.id_comp]
      exact Mod.extendUnitHom_extendHom φ (Mod.regularCoefficientMap φ)
    change Functor.LaxMonoidal.ε F ≫ F.map
        ((MonObj.one : 𝟙_ Ab.{u + 1} ⟶ R) ≫
        (biproduct.ι (fun _ : Fin r ↦ Mod.regular R) j).hom) ≫
        Mod.extendUnitHom φ N ≫ (e r).hom.hom = _
    rw [F.map_comp]
    simp only [Category.assoc]
    change Functor.LaxMonoidal.ε F ≫ F.map (MonObj.one : 𝟙_ Ab.{u + 1} ⟶ R) ≫
      i.hom ≫ Mod.extendUnitHom φ N ≫ (e r).hom.hom = _
    rw [← Category.assoc i.hom, hn, Category.assoc]
    have hi' := congrArg Mod.Hom.hom hi
    change ((Mod.extendScalars φ).map i).hom ≫ (e r).hom.hom =
      (scalarRegularIso Λ U).hom.hom ≫
        (biproduct.ι (fun _ : Fin r ↦ Mod.regular (condensedRingObj Λ U)) j).hom at hi'
    rw [hi']
    rw [← Category.assoc (Mod.extendUnitHom φ M), hr]
    simp only [← Category.assoc]
    rw [← Functor.obj.η_def]
    exact congrArg (fun k ↦ k ≫
      (biproduct.ι (fun _ : Fin r ↦ Mod.regular (condensedRingObj Λ U)) j).hom)
      (IsMonHom.one_hom (scalarCoefficientHom Λ U))
  · let F := finiteConstantScalarExtension Λ U
    let a := biproduct.matrix fun j i ↦
      Mod.regularLift (Mod.regular (scalarRingObj Λ)) (A j i)
    have ha : (e m).inv ≫ F.map a ≫ (e n).hom = scalarMatrix Λ U A :=
      scalarMatrix_map Λ U A
    have h : scalarMatrix Λ U A ≫ (e n).inv ≫ F.map q = 0 := by
      rw [← ha]
      simp only [Category.assoc, Iso.hom_inv_id_assoc, ← F.map_comp]
      change (e m).inv ≫ F.map (_ ≫ q) = 0
      rw [hAq, F.map_zero, comp_zero]
    refine ⟨h, ?_⟩
    let hc := CokernelCofork.mapIsColimit (CokernelCofork.ofπ q hAq) hq F
    have hc' : IsColimit (CokernelCofork.ofπ ((e n).inv ≫ F.map q) h) := by
      apply IsCokernel.ofIso (F.map a) hc
        (CokernelCofork.ofπ ((e n).inv ≫ F.map q) h)
        (e m) (e n) (Iso.refl _)
      · rw [← ha]
        simp
      · simp
    refine ⟨⟨hc'⟩, ?_⟩
    let c := hc'.coconePointUniqueUpToIso (cokernelIsCokernel (scalarMatrix Λ U A))
    refine ⟨c, ?_⟩
    exact hc'.comp_coconePointUniqueUpToIso_hom
      (cokernelIsCokernel (scalarMatrix Λ U A)) WalkingParallelPair.one

end AlgebraicGeometry.ProEtale
