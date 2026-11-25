/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceVaryingScalarSquare
public import Mathlib.CategoryTheory.Adjunction.Mates
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceVaryingScalarSquare
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerOrdinaryUnitEvaluation
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalRlimForgetUnit

/-! # Invertibility of the varying scalar inverse-image mate -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures AlgebraicGeometry.ProEtale.SpTowerClasses
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
attribute [local implicit_reducible] spCoefficientCommRings SpTowerShriek.tau
  CategoryTheory.Functor.ofOpSequence CategoryTheory.Functor.ofSequence
  WeilConjectures.SemilinearSections.evaluation
  SheafOfModules.pushforward PresheafOfModules.pushforward PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj Scheme.proEtaleRingModuleDirectImage
attribute [local irreducible] CategoryTheory.constantSheaf Padic
  WeilConjectures.SemilinearSections.systemRing
  WeilConjectures.SemilinearSections.ringPresheaf WeilConjectures.SemilinearSections.rings
  Padic.coefficientExtensionIntegers
attribute [local irreducible] SemilinearSections.transition SemilinearSections.coefficientMap
  Scheme.proEtaleRingModulePullback Scheme.proEtaleRingModuleAdjunction
  Scheme.proEtaleConstantRingComparison Scheme.proEtaleRingDirectImageMap

/-- The section-normalized varying direct-image square has invertible inverse-image mate.

Source: blueprint coefficient proof (1), exact residue scalar restriction.
At each finite level, forget the fixed scalars and identify the result with the
underlying abelian sheaf of the actual finite module. The direct-image square
is the normalized push-evaluation square: both maps are the identity on sections.
The unit-mate equation, the naturality of restriction's underlying comparison,
and the evaluated system-unit equation identify the underlying mate with the
comparison between the fixed-scalar unit and the finite-ring unit. Their abelian
adjuncts are invertible. Therefore the comparison is invertible by naturality of
adjunction. Forgetting scalars and evaluation reflect isomorphisms, giving the
claim for strict systems. The argument includes the zero system and level zero.
(blueprint: new-sfb-diagonal-rlim-varying-scalar-mate). -/
theorem diagonalRlimVaryingScalarMate (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S)
    (b : SpTowerShriek.Base l (ULift.{u} (Padic l)))
    (g : SpTowerShriek.Geometry l (ULift.{u} (Padic l)) b f)
    (rS : Restriction l (ULift.{u} (Padic l)) S)
    (rX : Restriction l (ULift.{u} (Padic l)) X)
    (d : g.push ⋙ rS.F ≅ rX.F ⋙ diagonalTraceSystemPush l f)
    (hd : ∀ (M : Systems X (Arings l (ULift.{u} (Padic l)) X)) (n : ℕ)
      (U : S.ProEtᵒᵖ) (x : (((g.push ⋙ rS.F).obj M).obj (op n)).obj.obj U),
      HEq (((d.hom.app M).app (op n)).hom.app U x) x) :
    IsIso (((mateEquiv g.ordinaryAdjunction
      (((upperStarLowerStarAdjunction
        (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f).whiskerRight ℕᵒᵖ))).symm
        (TwoSquare.mk _ _ _ _ d.hom))) := by
  let am := ((upperStarLowerStarAdjunction
        (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f).whiskerRight ℕᵒᵖ)
  let aa := upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f
  let FS := diagonalForget l S
  let FX := diagonalForget l X
  let P := lowerStar AddCommGrpCat.{u + 1} f
  let δ := ((mateEquiv g.ordinaryAdjunction am).symm
    (TwoSquare.mk _ _ _ _ d.hom))
  have hde (n : ℕ) (M : SpTowerShriek.S l (ULift.{u} (Padic l)) X) :
      FS.map ((d.hom.app M).app (op n)) =
        (levelUnderlying l f b g rS rX n).hom.app M := by
    rw [← levelIso_forget_hom l f b g rS rX n M]
    ext U x
    exact eq_of_heq ((hd M n U x).trans
      (levelIso_sections l f b g rS rX M n U x).symm)
  have hi (M : SpTowerShriek.S l (ULift.{u} (Padic l)) S) (n : ℕᵒᵖ) :
      IsIso ((δ.app M).app n) := by
    let : FX.ReflectsIsomorphisms := by
      dsimp [FX, diagonalForget]
      infer_instance
    apply (isIso_iff_of_reflects_iso ((δ.app M).app n) FX).mp
    let eS := restrictionUnderlying l S rS n.unop
    let eX := restrictionUnderlying l X rX n.unop
    let U := finiteForget l (ULift.{u} (Padic l)) S n.unop
    let V := finiteForget l (ULift.{u} (Padic l)) X n.unop
    let N := (SpTowerShriek.ev l (ULift.{u} (Padic l)) S n.unop).obj M
    let a := Scheme.proEtaleConstantRingAdjunction
      (SpTowerShriek.R l (ULift.{u} (Padic l)) n.unop) f
    let z := FS.map (((am.unit.app (rS.F.obj M)).app n))
    let h := eS.hom.app M ≫ U.map (a.unit.app N)
    let B := FS.obj ((rS.F.obj M).obj n)
    let Y := FX.obj ((upperStar
      (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f).obj ((rS.F.obj M).obj n))
    let Z := V.obj ((Scheme.proEtaleConstantRingPullback
      (SpTowerShriek.R l (ULift.{u} (Padic l)) n.unop) f).obj N)
    let k : Y ⟶ Z := FX.map ((δ.app M).app n) ≫ eX.hom.app (g.pull.obj M) ≫
      V.map ((g.ordinaryPullEvaluation n.unop).hom.app M)
    have hz : IsIso ((aa.homEquiv B Y).symm z) :=
      diagonalRlimForgetUnit l f ((rS.F.obj M).obj n)
    have hf : IsIso ((aa.homEquiv (U.obj N) Z).symm (U.map (a.unit.app N))) :=
      Scheme.ringUnitComparison f
        (Scheme.proEtaleConstantRing S (SpTowerShriek.R l (ULift.{u} (Padic l)) n.unop))
        (Scheme.proEtaleConstantRing X (SpTowerShriek.R l (ULift.{u} (Padic l)) n.unop))
        (Scheme.proEtaleConstantRingComparison f
          (SpTowerShriek.R l (ULift.{u} (Padic l)) n.unop)) a N
    have hh : IsIso ((aa.homEquiv B Z).symm h) := by
      dsimp only [h]
      rw [aa.homEquiv_naturality_left_symm]
      change IsIso ((upperStar AddCommGrpCat.{u + 1} f).map (eS.hom.app M) ≫
        (aa.homEquiv (U.obj N) Z).symm (U.map (a.unit.app N)))
      infer_instance
    have hu := unit_mateEquiv_symm g.ordinaryAdjunction am
      (TwoSquare.mk _ _ _ _ d.hom) M
    have huv := congrArg (fun t ↦ FS.map (t.app n)) hu
    dsimp only [Functor.comp_map, NatTrans.comp_app] at huv
    simp only [Functor.map_comp] at huv
    change FS.map ((rS.F.map (g.ordinaryAdjunction.unit.app M)).app n) ≫
        FS.map ((d.hom.app (g.pull.obj M)).app n) =
      z ≫ P.map (FX.map ((δ.app M).app n)) at huv
    have he := SpTowerShriek.geometry_unit_evaluation l (ULift.{u} (Padic l)) b
      g n.unop M
    have hk : z ≫ P.map k = h := by
      dsimp only [k]
      simp only [CategoryTheory.Functor.map_comp, ← Category.assoc]
      rw [← huv]
      simp only [Category.assoc]
      rw [hde]
      dsimp only [levelUnderlying, directImageUnderlying, NatIso.ofComponents_hom_app,
        Iso.refl_hom, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
        Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
        Functor.whiskerRight_app, Iso.symm_hom]
      change FS.map ((rS.F.map (g.ordinaryAdjunction.unit.app M)).app n) ≫
        eS.hom.app (g.push.obj (g.pull.obj M)) ≫
        U.map ((g.ordinaryPushEvaluation n.unop).hom.app (g.pull.obj M)) ≫
        (𝟙 (P.obj (V.obj
          ((SpTowerShriek.ev l (ULift.{u} (Padic l)) X n.unop).obj (g.pull.obj M))))) ≫
        P.map (eX.inv.app (g.pull.obj M)) ≫
        P.map (eX.hom.app (g.pull.obj M) ≫
          V.map ((g.ordinaryPullEvaluation n.unop).hom.app M)) = h
      simp only [← P.map_comp, Iso.inv_hom_id_app_assoc]
      have hn := eS.hom.naturality (g.ordinaryAdjunction.unit.app M)
      change FS.map ((rS.F.map (g.ordinaryAdjunction.unit.app M)).app n) ≫
          eS.hom.app (g.push.obj (g.pull.obj M)) =
        eS.hom.app M ≫ U.map
          ((SpTowerShriek.ev l (ULift.{u} (Padic l)) S n.unop).map
            (g.ordinaryAdjunction.unit.app M)) at hn
      erw [reassoc_of% hn]
      change eS.hom.app M ≫ U.map
        ((SpTowerShriek.ev l (ULift.{u} (Padic l)) S n.unop).map
          (g.ordinaryAdjunction.unit.app M)) ≫
        U.map ((g.ordinaryPushEvaluation n.unop).hom.app (g.pull.obj M)) ≫
        U.map ((Scheme.proEtaleConstantRingPushforward
          (SpTowerShriek.R l (ULift.{u} (Padic l)) n.unop) f).map
            ((g.ordinaryPullEvaluation n.unop).hom.app M)) = _
      rw [← U.map_comp, ← U.map_comp, he]
    have : IsIso k := isoOfAdjunct aa (X := B) (Y := Y) (Z := Z) z h k hz hh hk
    dsimp only [k] at this
    exact IsIso.of_isIso_comp_right (FX.map ((δ.app M).app n))
      (eX.hom.app (g.pull.obj M) ≫
        V.map ((g.ordinaryPullEvaluation n.unop).hom.app M))
  let (M : SpTowerShriek.S l (ULift.{u} (Padic l)) S) (n : ℕᵒᵖ) :
      IsIso ((δ.app M).app n) := hi M n
  let (M : SpTowerShriek.S l (ULift.{u} (Padic l)) S) : IsIso (δ.app M) :=
    NatIso.isIso_of_isIso_app _
  exact NatIso.isIso_of_isIso_app δ

end AlgebraicGeometry.ProEtale.DiagonalTrace
