/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
import WeilConjectures.AlgebraicGeometry.PoincareDuality.CompatiblePrimitiveRoots
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule

/-! # Local bases for the native finite root line
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory MonObj Limits Opposite
open scoped CategoryTheory.Obj
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

private def freeUnitIso {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] :
    (Mod.freeFunctor R).obj (𝟙_ _) ≅ Mod.regular R :=
  Mod.isoMk (ρ_ R) (by
    change ((α_ R R (𝟙_ _)).inv ≫ μ[R] ▷ (𝟙_ _)) ≫ (ρ_ R).hom =
      R ◁ (ρ_ R).hom ≫ μ[R]
    rw [Category.assoc, rightUnitor_naturality]
    monoidal)

private instance freeFunctorAdditive {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] :
    (Mod.freeFunctor R).Additive :=
  { map_add := by
      intro A B f g
      apply Mod.hom_ext
      exact MonoidalPreadditive.whiskerLeft_add f g }

private def freeConstantResidueIso {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R]
    (n : ℕ) (hR : n • 𝟙 R = 0) :
    (Mod.freeFunctor R).obj ((constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} (ZMod n)))) ≅ Mod.regular R := by
  let F := constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1} ⋙ Mod.freeFunctor R
  let e : F.obj (𝟙_ Ab.{u + 1}) ≅ Mod.regular R :=
    (Mod.freeFunctor R).mapIso
      (Functor.Monoidal.εIso (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1})).symm ≪≫
        freeUnitIso R
  have : (Mod.freeFunctor R).IsLeftAdjoint := ⟨_, ⟨Mod.freeForgetAdjunction R⟩⟩
  let c := CokernelCofork.ofπ (AddCommGrpCat.intResidue.{u} n)
    (AddCommGrpCat.intResidue_condition n)
  have hzero : F.map (n • 𝟙 (𝟙_ Ab.{u + 1})) = 0 := by
    rw [Functor.map_nsmul, CategoryTheory.Functor.map_id]
    apply (cancel_mono e.hom).mp
    rw [Preadditive.nsmul_comp, Category.id_comp, zero_comp]
    have hh : n • 𝟙 (Mod.regular R) = 0 := by
      apply (Mod.forget R).map_injective
      rw [Functor.map_nsmul, CategoryTheory.Functor.map_id, Functor.map_zero]
      change n • 𝟙 R = 0
      exact hR
    calc
      n • e.hom = e.hom ≫ (n • 𝟙 _) := by
        rw [Preadditive.comp_nsmul, Category.comp_id]
      _ = 0 := by rw [hh, comp_zero]
  have : IsIso (F.map (AddCommGrpCat.intResidue n)) :=
    CokernelCofork.IsColimit.isIso_π (c.map F)
      (c.mapIsColimit (AddCommGrpCat.intResidueCokernel n) F) hzero
  exact (asIso (F.map (AddCommGrpCat.intResidue n))).symm ≪≫ e

private def freePullIso {X Y : Scheme.{u}} (f : Y ⟶ X)
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    Mod.freeFunctor R ⋙ (upperStar Ab.{u + 1} f).mapMod R ≅
      upperStar Ab.{u + 1} f ⋙ Mod.freeFunctor ((upperStar Ab.{u + 1} f).obj R) := by
  let adj := upperStarLowerStarAdjunction Ab.{u + 1} f
  exact ((Mod.freeForgetAdjunction R).comp (adj.mapModAdjunction R)).leftAdjointUniq
    (adj.comp (Mod.freeForgetAdjunction ((upperStar Ab.{u + 1} f).obj R)))

private theorem finiteRing_nsmul (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) (n : ℕ) :
    (l ^ (n + 1)) • 𝟙 (condensedRingObj (twistFiniteRing l E n) X) = 0 := by
  let : TopologicalSpace (Padic.coefficientExtensionRing l E (n + 1)) := ⊥
  let : DiscreteTopology (Padic.coefficientExtensionRing l E (n + 1)) := ⟨rfl⟩
  have hp : (l ^ (n + 1)) • 𝟙 (twistFiniteRing l E n) = 0 := by
    apply Sheaf.hom_ext
    ext V f
    apply ULift.ext
    apply ContinuousMap.ext
    intro x
    change (l ^ (n + 1)) • _ = (0 : Padic.coefficientExtensionRing l E (n + 1))
    rw [nsmul_eq_mul, Nat.cast_pow, coefficientFiniteTwist_annihilator, zero_mul]
  let adj := pointUpperStarLowerStarAdjunction.comp
    (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))
  have : PreservesColimitsOfSize.{0, 0} (upperStarFromPoint X) :=
    adj.leftAdjoint_preservesColimits
  have : PreservesBinaryBiproducts (upperStarFromPoint X) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  have : (upperStarFromPoint X).Additive := Functor.additive_of_preservesBinaryBiproducts _
  change (l ^ (n + 1)) • 𝟙 ((upperStarFromPoint X).obj (twistFiniteRing l E n)) = 0
  rw [← CategoryTheory.Functor.map_id, ← Functor.map_nsmul, hp, Functor.map_zero]

end AlgebraicGeometry.ProEtale
