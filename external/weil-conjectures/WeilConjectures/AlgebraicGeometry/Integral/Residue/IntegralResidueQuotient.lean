/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.Residue.IntegralResidueLimit
public import WeilConjectures.TateTwist.ProEtale
import Mathlib.Algebra.Homology.ShortComplex.Ab
import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

/-!
# Free integral modules on finite constant coefficients
-/

@[expose] public section
universe u
open CategoryTheory Limits MonoidalCategory Opposite Preadditive MonObj
open scoped Topology CategoryTheory.Obj
open Filter
namespace PadicInt
variable {p : ℕ} [Fact p.Prime]
private theorem continuousMap_toZModPow_surjective
    (n : ℕ) (S : Type*) [TopologicalSpace S]
    :
    Function.Surjective (fun f : C(S, ℤ_[p]) ↦
      (⟨toZModPow n, PadicInt.continuous_toZModPow n⟩ : C(ℤ_[p], ZMod (p ^ n))).comp f) := by
  intro f
  let s : C(ZMod (p ^ n), ℤ_[p]) := ⟨fun z ↦ (z.val : ℤ_[p]), continuous_of_discreteTopology⟩
  refine ⟨s.comp f, ?_⟩
  ext x
  exact (map_natCast (toZModPow n) (f x).val).trans (ZMod.natCast_zmod_val (f x))

private theorem continuousMap_toZModPow_kernel
    (n : ℕ) (S : Type*) [TopologicalSpace S]
    (f : C(S, ℤ_[p])) (hf : ∀ x, toZModPow n (f x) = 0) :
    ∃ g : C(S, ℤ_[p]), ∀ x, f x = (p : ℤ_[p]) ^ n * g x := by
  have hpn : (p : ℚ_[p]) ^ n ≠ 0 := pow_ne_zero n (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  let g : S → ℤ_[p] := fun x ↦ Padic.lift ((f x : ℚ_[p]) / (p : ℚ_[p]) ^ n) (by
    rw [norm_div, div_le_one₀ (norm_pos_iff.mpr hpn), Padic.norm_p_pow]
    apply (norm_le_pow_iff_mem_span_pow (f x) n).mpr
    rw [← ker_toZModPow, RingHom.mem_ker]
    exact hf x)
  have hg : Continuous g := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp f.continuous).div_const _
  refine ⟨⟨g, hg⟩, fun x ↦ ?_⟩
  apply Subtype.ext
  change (f x : ℚ_[p]) = (p : ℚ_[p]) ^ n * ((f x : ℚ_[p]) / (p : ℚ_[p]) ^ n)
  exact (mul_div_cancel₀ _ hpn).symm

end PadicInt
namespace AlgebraicGeometry.ProEtale
open CondensedRing
private theorem residue_nsmul_condition (X : Scheme.{u}) (ℓ n : ℕ) [Fact ℓ.Prime] :
    ((ℓ ^ n) • 𝟙 (continuousAbRing X ℤ_[ℓ])) ≫ tateResidueMap X ℓ n = 0 := by
  apply (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map_injective
  rw [Functor.map_comp, Functor.map_nsmul, CategoryTheory.Functor.map_id, Functor.map_zero]
  ext U a
  simp only [NatTrans.comp_app, NatTrans.app_nsmul, NatTrans.id_app]
  apply ULift.ext
  ext x
  change PadicInt.toZModPow n ((ℓ ^ n) • a.down x) = 0
  simp [-Nat.cast_pow]

private noncomputable def residueCokernel (X : Scheme.{u}) (ℓ n : ℕ) [Fact ℓ.Prime] :
    IsColimit (CokernelCofork.ofπ (tateResidueMap X ℓ n)
      (residue_nsmul_condition X ℓ n)) := by
  apply isColimitOfReflects (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1})
  apply evaluationJointlyReflectsColimits
  intro U
  let E := sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1} ⋙
    (evaluation X.ProEtᵒᵖ Ab.{u + 1}).obj U
  let c := CokernelCofork.ofπ (tateResidueMap X ℓ n) (residue_nsmul_condition X ℓ n)
  change IsColimit (E.mapCocone c)
  apply (CokernelCofork.isColimitMapCoconeEquiv c E).symm.toFun
  have : Epi (E.map (tateResidueMap X ℓ n)) := by
    rw [AddCommGrpCat.epi_iff_surjective]
    intro a
    obtain ⟨b, hb⟩ := PadicInt.continuousMap_toZModPow_surjective n U.unop.left a.down
    exact ⟨ULift.up b, congrArg ULift.up hb⟩
  let S : ShortComplex Ab.{u + 1} :=
    ShortComplex.mk (E.map ((ℓ ^ n) • 𝟙 (continuousAbRing X ℤ_[ℓ])))
      (E.map (tateResidueMap X ℓ n)) (c.map_condition E)
  have hS : S.Exact := by
    rw [ShortComplex.ab_exact_iff]
    intro a ha
    have hres (x : U.unop.left) : PadicInt.toZModPow n (a.down x) = 0 :=
      congrArg (fun z : ULift.{u + 1} C(U.unop.left, ZMod (ℓ ^ n)) ↦ z.down x) ha
    obtain ⟨b, hb⟩ := PadicInt.continuousMap_toZModPow_kernel n U.unop.left a.down hres
    refine ⟨ULift.up b, ?_⟩
    apply ULift.ext
    apply ContinuousMap.ext
    intro x
    change (ℓ ^ n) • b x = a.down x
    rw [hb x, nsmul_eq_mul, ← Nat.cast_pow]
  exact hS.gIsCokernel

end AlgebraicGeometry.ProEtale

namespace AddCommGrpCat
private def intResidue (n : ℕ) : 𝟙_ Ab.{u + 1} ⟶ of (ULift.{u + 1} (ZMod n)) :=
  ofHom ((AddEquiv.ulift.symm.toAddMonoidHom).comp
    ((Int.castAddHom (ZMod n)).comp AddEquiv.ulift.toAddMonoidHom))
private theorem intResidue_condition (n : ℕ) : (n • 𝟙 (𝟙_ Ab.{u + 1})) ≫ intResidue n = 0 := by
  ext x
  change ((n • x.down : ℤ) : ZMod n) = 0
  simp
private noncomputable def intResidueCokernel (n : ℕ) :
    IsColimit (CokernelCofork.ofπ (intResidue.{u} n) (intResidue_condition n)) := by
  have : Epi (intResidue.{u} n) := by
    rw [epi_iff_surjective]
    intro a
    obtain ⟨b, hb⟩ := ZMod.intCast_surjective a.down
    exact ⟨ULift.up b, congrArg ULift.up hb⟩
  let S := ShortComplex.mk (n • 𝟙 (𝟙_ Ab.{u + 1})) (intResidue.{u} n)
    (intResidue_condition n)
  have hS : S.Exact := by
    rw [ShortComplex.ab_exact_iff]
    intro a ha
    have h : (a.down : ZMod n) = 0 := congrArg ULift.down ha
    obtain ⟨b, hb⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h
    refine ⟨ULift.up b, ?_⟩
    apply ULift.ext
    exact (show (n : ℤ) * b = a.down from hb.symm)
  exact hS.gIsCokernel
end AddCommGrpCat

namespace AlgebraicGeometry.ProEtale
universe v w
private def freeUnitIso {C : Type v} [Category.{w} C] [MonoidalCategory C]
    (R : C) [MonObj R] :
    (Mod.freeFunctor R).obj (𝟙_ _) ≅ Mod.regular R :=
  Mod.isoMk (ρ_ R) (by
    change ((α_ R R (𝟙_ _)).inv ≫ μ[R] ▷ (𝟙_ _)) ≫ (ρ_ R).hom =
      R ◁ (ρ_ R).hom ≫ μ[R]
    rw [Category.assoc, rightUnitor_naturality]
    monoidal)

end AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.ProEtale
open CondensedRing
private theorem residueModule_condition (X : Scheme.{u}) (ℓ n : ℕ) [Fact ℓ.Prime] :
    ((ℓ ^ n) • 𝟙 (Mod.regular
      (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X))) ≫
        tateResidueModuleProjection X ℓ n = 0 := by
  let R := condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X
  apply (Mod.forget R).map_injective
  rw [Functor.map_comp, Functor.map_nsmul, CategoryTheory.Functor.map_id, Functor.map_zero]
  change ((ℓ ^ n) • 𝟙 R) ≫ (chartComparison X ℤ_[ℓ] ≫ tateResidueMap X ℓ n) = 0
  rw [Preadditive.nsmul_comp, Category.id_comp, ← Preadditive.comp_nsmul]
  have h : (ℓ ^ n) • tateResidueMap X ℓ n = 0 := by
    simpa only [Preadditive.nsmul_comp, Category.id_comp] using residue_nsmul_condition X ℓ n
  rw [h, comp_zero]

private noncomputable def residueModuleCokernel (X : Scheme.{u}) (ℓ n : ℕ) [Fact ℓ.Prime] :
    IsColimit (CokernelCofork.ofπ (tateResidueModuleProjection X ℓ n)
      (residueModule_condition X ℓ n)) := by
  let R := condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X
  let F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R ⥤
      Sheaf (Scheme.ProEt.topology X) Ab.{u + 1} := Mod.forget R
  have : ReflectsColimitsOfShape WalkingParallelPair F :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  apply isColimitOfReflects F
  let c := CokernelCofork.ofπ (tateResidueModuleProjection X ℓ n)
    (residueModule_condition X ℓ n)
  apply (CokernelCofork.isColimitMapCoconeEquiv c F).symm.toFun
  let e : R ≅ continuousAbRing X ℤ_[ℓ] := asIso (chartComparison X ℤ_[ℓ])
  let a : parallelPair ((ℓ ^ n) • 𝟙 R) 0 ≅
      parallelPair ((ℓ ^ n) • 𝟙 (continuousAbRing X ℤ_[ℓ])) 0 :=
    parallelPair.ext e e (by simp) (by simp)
  let c' := CokernelCofork.ofπ (tateResidueMap X ℓ n) (residue_nsmul_condition X ℓ n)
  have hc' := (IsColimit.precomposeHomEquiv a c').symm (residueCokernel X ℓ n)
  refine IsColimit.ofIsoColimit hc' ?_
  refine Cofork.ext (Iso.refl _) ?_
  rfl
end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale
private instance freeFunctorAdditive (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] :
    (Mod.freeFunctor R).Additive :=
  { map_add := by
      intro A B f g
      apply Mod.hom_ext
      exact MonoidalPreadditive.whiskerLeft_add f g }

private noncomputable def freeConstantUnitIso (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] :
    (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1} ⋙ Mod.freeFunctor R).obj
      (𝟙_ Ab.{u + 1}) ≅ Mod.regular R :=
  (Mod.freeFunctor R).mapIso
    (Functor.Monoidal.εIso (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1})).symm ≪≫
      freeUnitIso R

private noncomputable def freeConstantResidueIso (X : Scheme.{u}) (ℓ n : ℕ) [Fact ℓ.Prime] :
    (Mod.freeFunctor (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X)).obj
      ((constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} (ZMod (ℓ ^ n))))) ≅
          tateResidueModuleLevel X ℓ n := by
  let R := condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X
  let F := constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1} ⋙ Mod.freeFunctor R
  have : (Mod.freeFunctor R).IsLeftAdjoint := ⟨_, ⟨Mod.freeForgetAdjunction R⟩⟩
  let c := CokernelCofork.ofπ (AddCommGrpCat.intResidue.{u} (ℓ ^ n))
    (AddCommGrpCat.intResidue_condition (ℓ ^ n))
  let e := freeConstantUnitIso X R
  exact CokernelCofork.mapIsoOfIsColimit
    (c.mapIsColimit (AddCommGrpCat.intResidueCokernel (ℓ ^ n)) F)
    (residueModuleCokernel X ℓ n)
    (Arrow.isoMk e e (by
      change e.hom ≫ ((ℓ ^ n) • 𝟙 _) = F.map ((ℓ ^ n) • 𝟙 _) ≫ e.hom
      rw [Functor.map_nsmul, CategoryTheory.Functor.map_id,
        Preadditive.nsmul_comp, Preadditive.comp_nsmul, Category.id_comp, Category.comp_id]))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem freeConstantResidueIso_hom (X : Scheme.{u}) (ℓ n : ℕ) [Fact ℓ.Prime] :
    (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1} ⋙
      Mod.freeFunctor (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X)).map
        (AddCommGrpCat.intResidue (ℓ ^ n)) ≫ (freeConstantResidueIso X ℓ n).hom =
    (freeConstantUnitIso X (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X)).hom ≫
      tateResidueModuleProjection X ℓ n := by
  dsimp only [freeConstantResidueIso, CokernelCofork.mapIsoOfIsColimit]
  exact CokernelCofork.π_mapOfIsColimit
    (C := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X)) _ _ _
end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale
/-- Reduction between the finite constant abelian coefficient groups. -/
noncomputable def integralResidueAbTransition (ℓ n : ℕ) :
    AddCommGrpCat.of (ULift.{u + 1} (ZMod (ℓ ^ (n + 1)))) ⟶
      AddCommGrpCat.of (ULift.{u + 1} (ZMod (ℓ ^ n))) :=
  AddCommGrpCat.ofHom (AddEquiv.ulift.symm.toAddMonoidHom.comp
    ((ZMod.castHom (pow_dvd_pow ℓ (Nat.le_add_right n 1)) (ZMod (ℓ ^ n))).toAddMonoidHom.comp
      AddEquiv.ulift.toAddMonoidHom))
private theorem intResidue_transition (ℓ n : ℕ) :
    AddCommGrpCat.intResidue.{u} (ℓ ^ (n + 1)) ≫ integralResidueAbTransition ℓ n =
      AddCommGrpCat.intResidue (ℓ ^ n) := by
  ext x
  change ZMod.castHom (pow_dvd_pow ℓ (Nat.le_add_right n 1)) _
    (x.down : ZMod (ℓ ^ (n + 1))) = (x.down : ZMod (ℓ ^ n))
  simp
/-- The constant finite coefficient tower, including its zero level. -/
noncomputable def constantTateResidueSystem (X : Scheme.{u}) (ℓ : ℕ) :
    ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology X) Ab.{u + 1} :=
  Functor.ofOpSequence
    (X := fun n ↦ AddCommGrpCat.of (ULift.{u + 1} (ZMod (ℓ ^ n))))
    (integralResidueAbTransition.{u} ℓ) ⋙
    constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}

private noncomputable def freeConstantResidueNatIso (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] :
    constantTateResidueSystem X ℓ ⋙
      Mod.freeFunctor (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X) ≅
        tateResidueModuleSystem X ℓ := by
  let R := condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X
  let F := constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1} ⋙ Mod.freeFunctor R
  have : (Mod.freeFunctor R).IsLeftAdjoint := ⟨_, ⟨Mod.freeForgetAdjunction R⟩⟩
  let t : constantTateResidueSystem X ℓ ⋙ Mod.freeFunctor R ⟶
      tateResidueModuleSystem X ℓ :=
    NatTrans.ofOpSequence (fun n ↦ (freeConstantResidueIso X ℓ n).hom) (fun n ↦ by
      simp only [Functor.comp_map, constantTateResidueSystem, tateResidueModuleSystem,
        Functor.ofOpSequence_map_homOfLE_succ]
      have : Epi (AddCommGrpCat.intResidue.{u} (ℓ ^ (n + 1))) :=
        Cofork.IsColimit.epi (AddCommGrpCat.intResidueCokernel (ℓ ^ (n + 1)))
      have : Epi (F.map (AddCommGrpCat.intResidue (ℓ ^ (n + 1)))) := inferInstance
      apply (cancel_epi (F.map (AddCommGrpCat.intResidue (ℓ ^ (n + 1))))).mp
      change F.map (AddCommGrpCat.intResidue (ℓ ^ (n + 1))) ≫
        F.map (integralResidueAbTransition ℓ n) ≫ _ = _
      rw [← F.map_comp_assoc, intResidue_transition, freeConstantResidueIso_hom,
        ← Category.assoc, freeConstantResidueIso_hom, Category.assoc]
      congr 1
      apply Mod.hom_ext
      exact (tateResidueCoefficientMap_compat X ℓ n).symm)
  have : ∀ n, IsIso (t.app n) := fun n ↦ inferInstanceAs
    (IsIso (freeConstantResidueIso X ℓ n.unop).hom)
  have : IsIso t := NatIso.isIso_of_isIso_app t
  exact asIso t
end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale
/-- Free integral modules on the constant finite coefficients form the actual residue diagram. -/
theorem constantTateResidueSystem_free_iso (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] :
    Nonempty (constantTateResidueSystem X ℓ ⋙
      Mod.freeFunctor (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X) ≅
        tateResidueModuleSystem X ℓ) :=
  ⟨freeConstantResidueNatIso X ℓ⟩
end AlgebraicGeometry.ProEtale
