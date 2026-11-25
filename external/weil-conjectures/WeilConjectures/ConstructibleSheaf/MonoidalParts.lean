/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs

import Mathlib.RingTheory.TensorProduct.Finite
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.StalkMonoidal
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry Scheme

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
variable {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}

/-- Sheafification is monoidal, and the tensor of constant presheaves is constant. -/
private theorem constant_tensor (Y : Scheme.{u})
    (P Q : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [P.IsConstant Y.smallEtaleTopology] [Q.IsConstant Y.smallEtaleTopology] :
    (P ⊗ Q).IsConstant Y.smallEtaleTopology := by
  obtain ⟨a, ⟨i⟩⟩ := P.mem_essImage_of_isConstant
  obtain ⟨b, ⟨j⟩⟩ := Q.mem_essImage_of_isConstant
  let e : ((Functor.const Y.Etaleᵒᵖ).obj a ⊗ (Functor.const Y.Etaleᵒᵖ).obj b) ≅
      (Functor.const Y.Etaleᵒᵖ).obj (a ⊗ b) :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; simp)
  exact Sheaf.isConstant_of_iso _
    (tensorIso i.symm j.symm ≪≫
      Functor.Monoidal.μIso (presheafToSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
        ((Functor.const Y.Etaleᵒᵖ).obj a) ((Functor.const Y.Etaleᵒᵖ).obj b) ≪≫
      (presheafToSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapIso e)

/-- The tensor product of locally constant module sheaves is locally constant.
(blueprint: lem-weil-pbc-flc-tensor-locally-constant-part) -/
theorem IsLocallyConstantSheaf.tensorObj_part
    (hF : IsLocallyConstantSheaf F) (hG : IsLocallyConstantSheaf G) :
    IsLocallyConstantSheaf (F ⊗ G) := by
  let := hF
  let := hG
  obtain ⟨⟨𝒰, h𝒰⟩⟩ := IsLocallyConstantSheaf.nonempty_locallyConstantDatum (F := F)
  obtain ⟨⟨𝒱, h𝒱⟩⟩ := IsLocallyConstantSheaf.nonempty_locallyConstantDatum (F := G)
  let A := ModuleCat.{u + 1} Λ
  have : etalePrecoverage.{u}.IsStableUnderComposition :=
    inferInstanceAs (precoverage @Etale).IsStableUnderComposition
  refine ⟨⟨⟨𝒰.bind fun i ↦ 𝒱.pullback₂ (𝒰.f i), fun ⟨i, j⟩ ↦ ?_⟩⟩⟩
  rw [isConstant_over_iff_upperStar]
  set f := Limits.pullback.snd (𝒱.f j) (𝒰.f i) ≫ 𝒰.f i
  change ((Etale.upperStar A f).obj (F ⊗ G)).IsConstant
    (Limits.pullback (𝒱.f j) (𝒰.f i)).smallEtaleTopology
  have hF' : ((Etale.upperStar A f).obj F).IsConstant
      (Limits.pullback (𝒱.f j) (𝒰.f i)).smallEtaleTopology := by
    have h₁ : ((Etale.upperStar A (𝒰.f i)).obj F).IsConstant
        (𝒰.X i).smallEtaleTopology :=
      (isConstant_over_iff_upperStar A (𝒰.etalePrecoverageToEtale i) F).mp (h𝒰 i)
    have h₂ : ((Etale.upperStar A (𝒰.f i) ⋙
        Etale.upperStar A (Limits.pullback.snd (𝒱.f j) (𝒰.f i))).obj F).IsConstant
        (Limits.pullback (𝒱.f j) (𝒰.f i)).smallEtaleTopology :=
      Sheaf.IsConstant.upperStar A (Limits.pullback.snd (𝒱.f j) (𝒰.f i))
        ((Etale.upperStar A (𝒰.f i)).obj F)
    exact Sheaf.isConstant_congr _
      ((Etale.upperStarComp A (Limits.pullback.snd (𝒱.f j) (𝒰.f i)) (𝒰.f i)).app F).symm
  have hG' : ((Etale.upperStar A f).obj G).IsConstant
      (Limits.pullback (𝒱.f j) (𝒰.f i)).smallEtaleTopology := by
    have h₁ : ((Etale.upperStar A (𝒱.f j)).obj G).IsConstant
        (𝒱.X j).smallEtaleTopology :=
      (isConstant_over_iff_upperStar A (𝒱.etalePrecoverageToEtale j) G).mp (h𝒱 j)
    have h₂ : ((Etale.upperStar A (𝒱.f j) ⋙
        Etale.upperStar A (Limits.pullback.fst (𝒱.f j) (𝒰.f i))).obj G).IsConstant
        (Limits.pullback (𝒱.f j) (𝒰.f i)).smallEtaleTopology :=
      Sheaf.IsConstant.upperStar A (Limits.pullback.fst (𝒱.f j) (𝒰.f i))
        ((Etale.upperStar A (𝒱.f j)).obj G)
    exact Sheaf.isConstant_congr _
      (((Etale.upperStarComp A (Limits.pullback.fst (𝒱.f j) (𝒰.f i)) (𝒱.f j)).app G).symm ≪≫
        eqToIso (congrArg (fun m ↦ (Etale.upperStar A m).obj G) Limits.pullback.condition))
  have hFG := constant_tensor _ ((Etale.upperStar A f).obj F) ((Etale.upperStar A f).obj G)
  exact Sheaf.isConstant_congr _ (Functor.Monoidal.μIso (Etale.upperStar A f) F G)

/-- The tensor product of finite module sheaves is finite on geometric stalks.
(blueprint: lem-weil-pbc-flc-tensor-finite-part) -/
theorem IsFiniteSheaf.tensorObj_part
    (hF : IsFiniteSheaf F) (hG : IsFiniteSheaf G) :
    IsFiniteSheaf (F ⊗ G) := by
  let := hF
  let := hG
  constructor
  intro Ω _ _ s
  let Φ := (pointSmallEtale s).ulift.{u + 1}
  have hF' := (hF.isFinitelyGenerated_sheafFiber Ω s).of_iso
    (((pointSmallEtale s).uliftSheafFiberIso.{u + 1} (ModuleCat.{u + 1} Λ)).app F).symm
  have hG' := (hG.isFinitelyGenerated_sheafFiber Ω s).of_iso
    (((pointSmallEtale s).uliftSheafFiberIso.{u + 1} (ModuleCat.{u + 1} Λ)).app G).symm
  have := (ModuleCat.isFinitelyGenerated_iff _).mp hF'
  have := (ModuleCat.isFinitelyGenerated_iff _).mp hG'
  exact ((ModuleCat.isFinitelyGenerated_iff _).mpr
    (by
      change Module.Finite Λ
        (TensorProduct Λ ((Φ.sheafFiber (A := ModuleCat.{u + 1} Λ)).obj F)
          ((Φ.sheafFiber (A := ModuleCat.{u + 1} Λ)).obj G))
      infer_instance)).of_iso
    ((Etale.sheafFiberTensorIso s F G).symm ≪≫
      ((pointSmallEtale s).uliftSheafFiberIso.{u + 1} (ModuleCat.{u + 1} Λ)).app (F ⊗ G))

end AlgebraicGeometry.Scheme
