import Langlands.Geometry.FormalGroup.DrinfeldFramedFrameClassAction
import Mathlib.CategoryTheory.Endomorphism

/-! # Varying-Nilp naturality of integral fixed-frame automorphisms -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v s

namespace Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas

open CategoryTheory ValuativeRel CentralDivision ModuleLaw

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {R : Type v} [CommRing R] [Algebra 𝒪[K] R]
variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] {π : 𝒪[K]}
variable {A B : Nilp.{v,u} R (algebraMap 𝒪[K] R π)}
variable {Φ : SpecialModule.HeightSquaredModule (K := K) (D := D) (ι := ι) (R := κ) π}

attribute [local instance] coefficientAlgebra coefficientScalarTower

set_option maxHeartbeats 1000000 in
/-- The two specified actual source automorphisms have the same complete series under base extension. -/
theorem frameAutomorphismIso_baseChange_coordinates (a : ModuleLaw.OrderAction.Automorphism Φ.val.order)
    (X : DrinfeldFramedAtlas Φ A) (f : A ⟶ B)
    (C : CommAlgCat.{u} ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj)
    (b : (X.baseChange f).source.atlas.opens)
    (hb : IsUnit (algebraMap
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj C b.val)) :
    (((X.frameAutomorphismIso a).baseChangeAlong (Nilp.reducedScalarMap 𝒪[K] f)).hom.val.hom C
      (BasicAtlas.sourceChart (X.target.val.atlas.reductionBaseChangeOpens_eq f).symm b) hb).toHom.toCoordinateMap =
      (((X.baseChange f).frameAutomorphismIso a).hom.val.hom C b hb).toHom.toCoordinateMap := by
  let φ := Nilp.reducedScalarMap 𝒪[K] f
  let b' := BasicAtlas.sourceChart (X.target.val.atlas.reductionBaseChangeOpens_eq f).symm b
  have h₁ := congrArg (fun j => (j.val.hom C b' hb).toHom.toCoordinateMap)
    (BasicAtlas.OrderAction.Iso.baseChangeAlong_hom (X.frameAutomorphismIso a) φ)
  have h₂ := congrArg (fun j => (j.hom C b' hb).toHom.toCoordinateMap)
    (BasicAtlas.OrderAction.Hom.baseChangeAlong_val (X.frameAutomorphismIso a).hom φ)
  have h₃ := BasicAtlas.Hom.baseChangeAlong_coordinates (X.frameAutomorphismIso a).hom.val φ C b' hb
  refine h₁.trans (h₂.trans (h₃.trans ?_))
  change (BasicAtlas.globalChartHom (a.toIso.map X.residueMap).hom.val _
      (restrictCoefficientAlgebra φ C) _).toHom.toCoordinateMap =
    (BasicAtlas.globalChartHom (a.toIso.map (φ.comp X.residueMap)).hom.val _ C _).toHom.toCoordinateMap
  rw [BasicAtlas.globalChartHom_coordinates, BasicAtlas.globalChartHom_coordinates]
  change (a.toIso.hom.val.toHom.toCoordinateMap.map X.residueMap.toRingHom).map
      (algebraMap _ (restrictCoefficientAlgebra φ C)) =
    (a.toIso.hom.val.toHom.toCoordinateMap.map (φ.comp X.residueMap).toRingHom).map (algebraMap _ C)
  rw [CoordinateMap.map_ringHom_comp, CoordinateMap.map_ringHom_comp]
  rfl

set_option maxHeartbeats 2000000 in
/-- The actual quotient-frame comparison intertwines the two actual extended source automorphisms. -/
theorem frameAutomorphismIso_baseChange (a : ModuleLaw.OrderAction.Automorphism Φ.val.order)
    (X : DrinfeldFramedAtlas Φ A) (f : A ⟶ B) :
    ((X.frameAutomorphismIso a).baseChangeAlong (Nilp.reducedScalarMap 𝒪[K] f)).trans
        (SpecialAtlas.quotientFrameBaseChangeIso Φ.val X.residueMap X.target.val f) =
      (SpecialAtlas.quotientFrameBaseChangeIso Φ.val X.residueMap X.target.val f).trans
        ((X.baseChange f).frameAutomorphismIso a) := by
  apply BasicAtlas.OrderAction.Iso.ext_hom
  apply Subtype.ext
  apply BasicAtlas.Hom.ext
  intro C b hb
  apply ModuleLaw.Hom.ext
  apply CommLaw.Hom.ext
  let φ := Nilp.reducedScalarMap 𝒪[K] f
  let sa := SpecialAtlas.quotientFrameBaseChangeIso Φ.val X.residueMap X.target.val f
  change (sa.hom.val.hom C b hb).toHom.toCoordinateMap.comp
      (((X.frameAutomorphismIso a).baseChangeAlong φ).hom.val.hom C
        (BasicAtlas.sourceChart (X.target.val.atlas.reductionBaseChangeOpens_eq f).symm b) hb).toHom.toCoordinateMap =
    (((X.baseChange f).frameAutomorphismIso a).hom.val.hom C b hb).toHom.toCoordinateMap.comp
      (sa.hom.val.hom C b hb).toHom.toCoordinateMap
  have hs : (sa.hom.val.hom C b hb).toHom.toCoordinateMap = CoordinateMap.id :=
    SpecialAtlas.quotientFrameBaseChangeIso_hom_coordinates Φ.val X.residueMap X.target.val f C b hb
  rw [hs, CoordinateMap.id_comp, CoordinateMap.comp_id]
  exact frameAutomorphismIso_baseChange_coordinates a X f C b hb

set_option maxHeartbeats 2000000 in
/-- Base extension and inverse frame precomposition give exactly the same whole framing tensor. -/
theorem frameAct_baseChange_rho (a : ModuleLaw.OrderAction.Automorphism Φ.val.order)
    (X : DrinfeldFramedAtlas Φ A) (f : A ⟶ B) :
    ((frameAct a X).baseChange f).rho = (frameAct a (X.baseChange f)).rho := by
  let φ := Nilp.reducedScalarMap 𝒪[K] f
  let sa := SpecialAtlas.quotientFrameBaseChangeIso Φ.val X.residueMap X.target.val f
  let tq := X.target.val.reductionBaseChangeIso f
  let qsa := BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := K) sa
  let qt := BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := K) tq
  let abase := BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := K)
    ((X.frameAutomorphismIso a).baseChangeAlong φ)
  let anew := BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := K) ((X.baseChange f).frameAutomorphismIso a)
  let q := X.rho.baseChangeAlong φ
  have hb : ((frameAct a X).rho.baseChangeAlong φ) = abase.symm.trans q := by
    change (((BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := K) (X.frameAutomorphismIso a)).symm.trans
      X.rho).baseChangeAlong φ) = _
    rw [BasicAtlas.OrderAction.QuasiIsogeny.baseChangeAlong_trans,
      BasicAtlas.OrderAction.QuasiIsogeny.baseChangeAlong_symm,
      BasicAtlas.OrderAction.QuasiIsogeny.baseChangeAlong_ofIso]
  have hi : qsa.symm.trans abase.symm = anew.symm.trans qsa.symm := by
    have hh := congrArg (fun j => BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := K) j.symm)
      (frameAutomorphismIso_baseChange a X f)
    simpa only [BasicAtlas.OrderAction.Iso.symm_trans,
      BasicAtlas.OrderAction.QuasiIsogeny.ofIso_trans,
      BasicAtlas.OrderAction.QuasiIsogeny.ofIso_symm] using hh
  have hl : ((frameAct a X).baseChange f).rho =
      ((qsa.symm.trans abase.symm).trans q).trans qt.symm := by
    have hh := (frameAct a X).baseChange_rho_formula f
    change ((frameAct a X).baseChange f).rho =
      (qsa.symm.trans ((frameAct a X).rho.baseChangeAlong φ)).trans qt.symm at hh
    exact hh.trans ((congrArg (fun j => (qsa.symm.trans j).trans qt.symm) hb).trans
      (congrArg (fun j => j.trans qt.symm)
        (BasicAtlas.OrderAction.QuasiIsogeny.trans_assoc qsa.symm abase.symm q).symm))
  have hr : (frameAct a (X.baseChange f)).rho =
      anew.symm.trans ((qsa.symm.trans q).trans qt.symm) := by
    exact congrArg (fun j => anew.symm.trans j) (X.baseChange_rho_formula f)
  have ha : ((anew.symm.trans qsa.symm).trans q).trans qt.symm =
      anew.symm.trans ((qsa.symm.trans q).trans qt.symm) := by
    simp only [BasicAtlas.OrderAction.QuasiIsogeny.trans_assoc]
  exact hl.trans ((congrArg (fun j => (j.trans q).trans qt.symm) hi).trans (ha.trans hr.symm))

/-- Equality of the actual stored data determines a framed representative; the height field is a certificate. -/
theorem eq_of_residue_target_rho {X Y : DrinfeldFramedAtlas Φ A}
    (he : X.residueMap = Y.residueMap) (ht : X.target = Y.target) (hr : HEq X.rho Y.rho) : X = Y := by
  cases X
  cases Y
  cases he
  cases ht
  cases hr
  rfl

set_option maxHeartbeats 2000000 in
/-- Actual base extension commutes with integral fixed-frame inverse precomposition on representatives. -/
theorem frameAct_baseChange (a : ModuleLaw.OrderAction.Automorphism Φ.val.order)
    (X : DrinfeldFramedAtlas Φ A) (f : A ⟶ B) :
    (frameAct a X).baseChange f = frameAct a (X.baseChange f) :=
  eq_of_residue_target_rho rfl rfl (heq_of_eq (frameAct_baseChange_rho a X f))

namespace ComparisonClass

/-- Actual base extension commutes with the action on the same original framed comparison quotient. -/
theorem frameAct_baseChange (a : ModuleLaw.OrderAction.Automorphism Φ.val.order)
    (q : ComparisonClass Φ A) (f : A ⟶ B) :
    (frameAct a q).baseChange f = frameAct a (q.baseChange f) := by
  refine Quotient.inductionOn q ?_
  intro X
  exact congrArg comparisonClassOf (DrinfeldFramedAtlas.frameAct_baseChange a X f)

end ComparisonClass

/-- Each actual integral full-order frame automorphism is a natural endomorphism of the actual framed Nilp functor. -/
def frameAutomorphismNatTrans (a : ModuleLaw.OrderAction.Automorphism Φ.val.order) :
    comparisonClassFunctor (R := R) Φ ⟶ comparisonClassFunctor Φ where
  app A := ↾(ComparisonClass.frameAct a)
  naturality A B f := by
    apply ConcreteCategory.hom_ext
    intro q
    exact (ComparisonClass.frameAct_baseChange a q f).symm

/-- The inverse frame map supplies the inverse natural transformation. -/
def frameAutomorphismNatIso (a : ModuleLaw.OrderAction.Automorphism Φ.val.order) :
    comparisonClassFunctor (R := R) Φ ≅ comparisonClassFunctor Φ where
  hom := frameAutomorphismNatTrans a
  inv := frameAutomorphismNatTrans a⁻¹
  hom_inv_id := by
    apply NatTrans.ext
    funext A
    apply ConcreteCategory.hom_ext
    intro q
    change ComparisonClass.frameAct a⁻¹ (ComparisonClass.frameAct a q) = q
    rw [← ComparisonClass.frameAct_mul, inv_mul_cancel, ComparisonClass.frameAct_one]
  inv_hom_id := by
    apply NatTrans.ext
    funext A
    apply ConcreteCategory.hom_ext
    intro q
    change ComparisonClass.frameAct a (ComparisonClass.frameAct a⁻¹ q) = q
    rw [← ComparisonClass.frameAct_mul, mul_inv_cancel, ComparisonClass.frameAct_one]

/-- The natural action is exactly the descended original frame action at every Nilp object. -/
@[simp]
theorem frameAutomorphismNatIso_hom_app (a : ModuleLaw.OrderAction.Automorphism Φ.val.order)
    (q : ComparisonClass Φ A) :
    (frameAutomorphismNatIso (R := R) a).hom.app A q = ComparisonClass.frameAct a q := rfl

/-- The actual integral frame automorphism group acts by natural automorphisms of the actual framed Nilp functor. -/
def frameAutomorphismActionHom : ModuleLaw.OrderAction.Automorphism Φ.val.order →*
    CategoryTheory.Aut (comparisonClassFunctor (R := R) Φ) where
  toFun a := Aut.of (frameAutomorphismNatIso a)
  map_one' := by
    apply Aut.ext
    apply CategoryTheory.Iso.ext
    apply NatTrans.ext
    funext A
    apply ConcreteCategory.hom_ext
    intro q
    exact ComparisonClass.frameAct_one q
  map_mul' a b := by
    apply Aut.ext
    apply CategoryTheory.Iso.ext
    apply NatTrans.ext
    funext A
    apply ConcreteCategory.hom_ext
    intro q
    exact ComparisonClass.frameAct_mul a b q

/-- Evaluation retains the same actual original comparison-class action. -/
@[simp]
theorem frameAutomorphismActionHom_app (a : ModuleLaw.OrderAction.Automorphism Φ.val.order)
    (q : ComparisonClass Φ A) :
    (frameAutomorphismActionHom (R := R) a).asIso.hom.app A q = ComparisonClass.frameAct a q := rfl

end Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas

