/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ConstructibleTorsionCurveSheaf
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.AlgebraicGeometry.ConstructibleCurveAnnihilator
import WeilConjectures.AlgebraicGeometry.ConstructibleSubsheafNoetherian
import WeilConjectures.AlgebraicGeometry.ConstructibleTorsionModulesAgree

@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.CurveCoefficientPair
/-- Constructibility of the subobject in the six step dévissage argument.
The proof is the finite torsion bound, cyclic module bridge, and the Noetherian
constructible subobject theorem described in the parent blueprint node.
(blueprint: lem-weil-pbc-curve-constructible-sub-part) -/
theorem constructible_sub_part {k : Type u} [Field k] [IsAlgClosed k]
    (P : AlgebraicGeometry.CurveCoefficientPair k)
    (F₁ F₂ : Sheaf P.C.smallEtaleTopology AddCommGrpCat.{u + 1})
    (h₁ : P.C.IsTorsionAbelianSheaf F₁) (h₂ : P.C.IsTorsionAbelianSheaf F₂)
    (α : F₁ ⟶ P.F) (β : P.F ⟶ F₂) (w : α ≫ β = 0)
    (hS : (ShortComplex.mk α β w).ShortExact) (hF : (Scheme.IsConstructibleEtaleSheafOfSets
      ((sheafCompose P.C.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj P.F))) :
    (fun P : AlgebraicGeometry.CurveCoefficientPair k ↦
    (Scheme.IsConstructibleEtaleSheafOfSets
      ((sheafCompose P.C.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj P.F)))
      { P with F := F₁, isTorsion :=
      ((Scheme.isTorsionAbelianSheaf_characterizations _).1.mp h₁) } := by
  have _hT₂ := h₂
  have : IsCurve P.toSpec := P.isCurve
  have : IsLocallyNoetherian P.C := LocallyOfFiniteType.isLocallyNoetherian P.toSpec
  have : CompactSpace P.C := QuasiCompact.compactSpace_of_compactSpace P.toSpec
  have : IsNoetherian P.C := ⟨⟩
  obtain ⟨n, hn, hkill⟩ := exists_annihilator_of_constructible P hF
  have : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have : Mono α := hS.mono_f
  have hkill₁ : n • 𝟙 F₁ = 0 := by
    rw [← cancel_mono α, Limits.zero_comp, Preadditive.nsmul_comp, Category.id_comp,
      ← Category.comp_id α, ← Preadditive.comp_nsmul, hkill, Limits.comp_zero]
  obtain ⟨hT, M, e, _, hM, _⟩ :=
    Scheme.constructible_torsion_modules_agree P.toSpec n hn P.F hkill
  obtain ⟨hT₁, M₁, e₁, _, hM₁, _⟩ :=
    Scheme.constructible_torsion_modules_agree P.toSpec n hn F₁ hkill₁
  let R := ULift.{u + 1} (ZMod n)
  let U := sheafCompose P.C.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})
  let a : U.obj M₁ ⟶ U.obj M := e₁.hom ≫ α ≫ e.inv
  let i : M₁ ⟶ M := ⟨{
    app := fun V ↦ ModuleCat.ofHom
      { toFun := a.hom.app V
        map_add' := map_add (a.hom.app V).hom
        map_smul' := fun c x ↦ by
          have hc : (c.down.val : R) = c := by
            apply ULift.ext
            exact ZMod.natCast_zmod_val c.down
          let f : (M₁.obj.obj V) →+ (M.obj.obj V) := (a.hom.app V).hom
          change f (c • x) = c • f x
          rw [← hc]
          simpa only [Nat.cast_smul_eq_nsmul] using
            f.map_nsmul c.down.val x }
    naturality := fun V W f ↦ by
      ext x
      exact ConcreteCategory.congr_hom (a.hom.naturality f) x }⟩
  have hi : U.map i = a := by rfl
  have : Mono a := inferInstance
  have : Mono i := by
    apply Functor.mono_of_mono_map U
    rw [hi]
    infer_instance
  have hMc : Scheme.IsConstructibleEtaleModuleSheaf M := hM.mp hF
  exact hM₁.mpr (Scheme.isConstructibleEtaleModuleSheaf_of_mono_noetherian i hMc)
end AlgebraicGeometry.CurveCoefficientPair
