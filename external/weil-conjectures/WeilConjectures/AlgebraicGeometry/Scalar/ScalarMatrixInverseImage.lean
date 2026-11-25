/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal
public import WeilConjectures.AlgebraicGeometry.RegularExtensionComparison
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule

/-!
# Inverse image of finite scalar matrices

The comparisons below use the canonical coefficient morphism and the regular-module
scalar-extension comparison, followed by the finite biproduct comparison.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] {V U : Scheme.{u}} (h : V ⟶ U)

/-- The regular-module comparison induced by the canonical coefficient map α_h.
First transport the regular module along the monoidal inverse image, and then use
extension of scalars along α_h. The forward map sends b ⊗ x to b α_h(x). -/
noncomputable def scalarMatrixRegularPullbackIso :
    (CondensedRing.upperStar Λ h).obj (Mod.regular (condensedRingObj Λ U)) ≅
      Mod.regular (condensedRingObj Λ V) :=
  (Mod.extendScalars (condensedPullbackHom Λ h)).mapIso
      ((upperStar Ab.{u + 1} h).mapModUnitIso (R := condensedRingObj Λ U)).symm ≪≫
    Mod.regularExtensionIso (condensedPullbackHom Λ h)

/-- The canonical finite-coproduct extension of the regular-module comparison.
This definition also includes rank zero, using the empty biproduct comparison. -/
noncomputable def scalarMatrixFreePullbackIso (r : ℕ) :
    (CondensedRing.upperStar Λ h).obj (Mod.finiteFree (condensedRingObj Λ U) r) ≅
      Mod.finiteFree (condensedRingObj Λ V) r :=
  (CondensedRing.upperStar Λ h).mapBiproduct
      (fun _ : Fin r ↦ Mod.regular (condensedRingObj Λ U)) ≪≫
    biproduct.mapIso (fun _ ↦ scalarMatrixRegularPullbackIso Λ h)

omit [MonObj Λ] [IsCommMonObj Λ] in
private theorem scalarSection_image (X : Scheme.{u})
    (a : 𝟙_ Ab.{u + 1} ⟶ scalarRingObj Λ) :
    scalarSection Λ X a = Functor.LaxMonoidal.ε (upperStarFromPoint X) ≫
      (upperStarFromPoint X).map
        (Functor.LaxMonoidal.ε
            (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) ≫
          (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map a ≫
          (constantSheafAdj (coherentTopology Profinite.{u}) Ab.{u + 1}
            Profinite.isTerminalPUnit).counit.app Λ) := by
  simp only [scalarSection, scalarCoefficientHom, Functor.map_comp]
  rfl

omit [IsCommMonObj Λ] in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalarEndomorphism_image (X : Scheme.{u})
    (a : 𝟙_ Ab.{u + 1} ⟶ scalarRingObj Λ) :
    (upperStarFromPoint X).map
        (Mod.regularLift (Mod.regular Λ)
          (Functor.LaxMonoidal.ε
              (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) ≫
            (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map a ≫
            (constantSheafAdj (coherentTopology Profinite.{u}) Ab.{u + 1}
              Profinite.isTerminalPUnit).counit.app Λ)).hom =
      (Mod.regularLift (Mod.regular (condensedRingObj Λ X))
        (scalarSection Λ X a)).hom := by
  let he : ((upperStarFromPoint X).mapMod Λ).obj (Mod.regular Λ) ≅
      Mod.regular (condensedRingObj Λ X) := Mod.isoMk (Iso.refl _) (by simp)
  have hm : ((upperStarFromPoint X).mapMod Λ).map
        (Mod.regularLift (Mod.regular Λ)
          (Functor.LaxMonoidal.ε
              (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) ≫
            (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map a ≫
            (constantSheafAdj (coherentTopology Profinite.{u}) Ab.{u + 1}
              Profinite.isTerminalPUnit).counit.app Λ)) ≫ he.hom =
      he.hom ≫ Mod.regularLift (Mod.regular (condensedRingObj Λ X))
        (scalarSection Λ X a) := by
    apply Mod.regular_hom_ext
    dsimp only [Functor.mapMod, Mod.homMk] at ⊢
    change (MonObj.one : 𝟙_ _ ⟶ (upperStarFromPoint X).obj Λ) ≫ (_ ≫ 𝟙 _) =
      (MonObj.one : 𝟙_ _ ⟶ (upperStarFromPoint X).obj Λ) ≫ (𝟙 _ ≫ _)
    simp only [Category.comp_id, Category.id_comp]
    rw [Mod.one_comp_regularLift, Functor.obj.η_def, Category.assoc,
      ← Functor.map_comp, Mod.one_comp_regularLift, scalarSection_image]
  simpa only [Functor.mapMod, Mod.homMk, Mod.regular, Mod.comp_hom', he,
    Mod.isoMk_hom_hom, Iso.refl_hom, Category.comp_id, Category.id_comp] using
      congrArg Mod.Hom.hom hm

omit [IsCommMonObj Λ] in
private theorem scalarEndomorphism_naturality
    (a : 𝟙_ Ab.{u + 1} ⟶ scalarRingObj Λ) :
    (upperStar Ab.{u + 1} h).map
        (Mod.regularLift (Mod.regular (condensedRingObj Λ U))
          (scalarSection Λ U a)).hom ≫ condensedPullbackHom Λ h =
      condensedPullbackHom Λ h ≫
        (Mod.regularLift (Mod.regular (condensedRingObj Λ V))
          (scalarSection Λ V a)).hom := by
  rw [← scalarEndomorphism_image, ← scalarEndomorphism_image]
  exact (upperStarFromPointComp h).hom.naturality (X := Λ) (Y := Λ) _

set_option backward.isDefEq.respectTransparency.types false in
private theorem scalarRegular_pullback
    (a : 𝟙_ Ab.{u + 1} ⟶ scalarRingObj Λ) :
    (CondensedRing.upperStar Λ h).map
        (Mod.regularLift (Mod.regular (condensedRingObj Λ U))
          (scalarSection Λ U a)) ≫ (scalarMatrixRegularPullbackIso Λ h).hom =
      (scalarMatrixRegularPullbackIso Λ h).hom ≫
        Mod.regularLift (Mod.regular (condensedRingObj Λ V))
          (scalarSection Λ V a) := by
  let F := upperStar Ab.{u + 1} h
  let R := condensedRingObj Λ U
  let φ := condensedPullbackHom Λ h
  let e : (F.mapMod R).obj (Mod.regular R) ≅ Mod.regular (F.obj R) :=
    Mod.isoMk (Iso.refl _) (by simp)
  have he : e.hom = (F.mapModUnitIso (R := R)).inv := by
    apply (cancel_mono (F.mapModUnitIso (R := R)).hom).mp
    apply Mod.hom_ext
    simp [e, Functor.mapModUnitIso]
    rfl
  let p := e.inv ≫ (F.mapMod R).map
    (Mod.regularLift (Mod.regular R) (scalarSection Λ U a)) ≫ e.hom
  have hp : p.hom ≫ φ = φ ≫
      (Mod.regularLift (Mod.regular (condensedRingObj Λ V))
        (scalarSection Λ V a)).hom := by
    simpa only [p, e, F, R, φ, Functor.mapMod, Mod.homMk, Mod.regular, Mod.comp_hom',
      Mod.isoMk_hom_hom, Mod.isoMk_inv_hom, Iso.refl_hom, Iso.refl_inv,
      Category.id_comp, Category.comp_id] using
      scalarEndomorphism_naturality Λ h a
  have hn := Mod.regularExtensionIso_naturality φ p
    (Mod.regularLift (Mod.regular (condensedRingObj Λ V)) (scalarSection Λ V a)) hp
  have hc := congrArg (fun f ↦ (Mod.extendScalars φ).map e.hom ≫ f) hn
  dsimp only [p] at hc
  simp only [Functor.map_comp, ← Category.assoc] at hc
  rw [← (Mod.extendScalars φ).map_comp e.hom e.inv, Iso.hom_inv_id,
    (Mod.extendScalars φ).map_id, Category.id_comp] at hc
  simpa only [scalarMatrixRegularPullbackIso, CondensedRing.upperStar,
    Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, he,
    Category.assoc, F, R, φ] using hc

set_option backward.isDefEq.respectTransparency.types false in
/-- Pullback preserves matrices of the same condensed scalars and their cokernels.
The entries are maps ℤ → Λ(*), equivalently elements of the scalar ring Λ(*).
As in `scalarMatrix`, the first index is the source column and the second the target row. -/
theorem scalarMatrix_inverseImage {m n : ℕ}
    (A : Fin m → Fin n → (𝟙_ Ab.{u + 1} ⟶ scalarRingObj Λ)) :
    (CondensedRing.upperStar Λ h).map (scalarMatrix Λ U A) ≫
        (scalarMatrixFreePullbackIso Λ h n).hom =
      (scalarMatrixFreePullbackIso Λ h m).hom ≫ scalarMatrix Λ V A ∧
    ∃ e : (CondensedRing.upperStar Λ h).obj (cokernel (scalarMatrix Λ U A)) ≅
        cokernel (scalarMatrix Λ V A),
      (CondensedRing.upperStar Λ h).map (cokernel.π (scalarMatrix Λ U A)) ≫ e.hom =
        (scalarMatrixFreePullbackIso Λ h n).hom ≫ cokernel.π (scalarMatrix Λ V A) := by
  let F := CondensedRing.upperStar Λ h
  have hm : (scalarMatrixFreePullbackIso Λ h m).inv ≫ F.map (scalarMatrix Λ U A) ≫
      (scalarMatrixFreePullbackIso Λ h n).hom = scalarMatrix Λ V A := by
    apply biproduct.hom_ext'
    intro j
    apply biproduct.hom_ext
    intro k
    dsimp only [F]
    simp only [scalarMatrixFreePullbackIso, Iso.trans_inv, Iso.trans_hom,
      biproduct.mapIso_inv, biproduct.mapIso_hom, Category.assoc,
      biproduct.ι_map_assoc, Functor.mapBiproduct_inv, Functor.mapBiproduct_hom,
      biproduct.ι_desc_assoc, biproduct.map_π, biproduct.lift_π,
      scalarMatrix, biproduct.matrix]
    erw [biproduct.lift_π_assoc]
    simp only [← Category.assoc, ← Functor.map_comp, biproduct.ι_desc,
      biproduct.lift_π]
    simp only [Category.assoc]
    rw [scalarRegular_pullback, Iso.inv_hom_id_assoc]
  have hs : F.map (scalarMatrix Λ U A) ≫ (scalarMatrixFreePullbackIso Λ h n).hom =
      (scalarMatrixFreePullbackIso Λ h m).hom ≫ scalarMatrix Λ V A := by
    rw [← hm, Iso.hom_inv_id_assoc]
  refine ⟨hs, ?_⟩
  let e := PreservesCokernel.iso F (scalarMatrix Λ U A) ≪≫
    cokernel.mapIso (F.map (scalarMatrix Λ U A)) (scalarMatrix Λ V A)
      (scalarMatrixFreePullbackIso Λ h m) (scalarMatrixFreePullbackIso Λ h n) hs
  refine ⟨e, ?_⟩
  dsimp only [e, Iso.trans_hom]
  rw [← Category.assoc, PreservesCokernel.π_iso_hom]
  exact cokernel.π_desc _ _ _

end AlgebraicGeometry.ProEtale
