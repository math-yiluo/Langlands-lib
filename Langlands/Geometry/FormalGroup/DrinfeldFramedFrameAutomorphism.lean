import Langlands.Geometry.FormalGroup.DrinfeldFramedClassFunctor
import Langlands.Geometry.FormalGroup.OrderAutomorphism

/-! # Actual integral fixed-frame automorphisms on framed representatives -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v w s

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {σ τ υ : Type} [Finite σ] [Finite τ] [Finite υ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ} {P : ModuleLaw O R υ}
variable {E : ModuleLaw.OrderAction D M} {E' : ModuleLaw.OrderAction D N}
variable {E'' : ModuleLaw.OrderAction D P}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Restriction of actual global full-order isomorphisms preserves identity. -/
@[simp]
theorem ofGlobalOrderIso_refl (E : ModuleLaw.OrderAction D M) (t : Set R) (ht : Ideal.span t = ⊤) :
    ofGlobalOrderIso (ModuleLaw.OrderAction.Iso.refl E) t ht = OrderAction.Iso.refl _ := by
  apply OrderAction.Iso.ext_hom
  exact ofGlobalOrderHom_id E t ht

/-- Restriction of actual global full-order isomorphisms preserves composition. -/
@[simp]
theorem ofGlobalOrderIso_trans (a : ModuleLaw.OrderAction.Iso E E')
    (b : ModuleLaw.OrderAction.Iso E' E'') (t : Set R) (ht : Ideal.span t = ⊤) :
    ofGlobalOrderIso (a.trans b) t ht = (ofGlobalOrderIso a t ht).trans (ofGlobalOrderIso b t ht) := by
  apply OrderAction.Iso.ext_hom
  exact ofGlobalOrderHom_comp b.hom a.hom t ht

/-- Restriction retains the same actual global inverse map. -/
@[simp]
theorem ofGlobalOrderIso_symm (a : ModuleLaw.OrderAction.Iso E E') (t : Set R) (ht : Ideal.span t = ⊤) :
    ofGlobalOrderIso a.symm t ht = (ofGlobalOrderIso a t ht).symm := rfl

end Langlands.FormalGroup.ModuleLaw.BasicAtlas

namespace Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas

open CategoryTheory ValuativeRel CentralDivision ModuleLaw

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {R : Type v} [CommRing R] [Algebra 𝒪[K] R]
variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] {π : 𝒪[K]}
variable {A : Nilp.{v,u} R (algebraMap 𝒪[K] R π)}
variable {Φ : SpecialModule.HeightSquaredModule (K := K) (D := D) (ι := ι) (R := κ) π}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Extend the actual integral frame automorphism along the residue map and restrict to the actual source cover. -/
def frameAutomorphismIso (X : DrinfeldFramedAtlas Φ A) (a : ModuleLaw.OrderAction.Automorphism Φ.val.order) :
    BasicAtlas.OrderAction.Iso X.source.order X.source.order rfl :=
  BasicAtlas.ofGlobalOrderIso (a.toIso.map X.residueMap) X.target.val.reduction.atlas.opens
    X.target.val.reduction.atlas.covers

@[simp]
theorem frameAutomorphismIso_one (X : DrinfeldFramedAtlas Φ A) :
    X.frameAutomorphismIso 1 = BasicAtlas.OrderAction.Iso.refl X.source.order := by
  simp only [frameAutomorphismIso, ModuleLaw.OrderAction.Automorphism.toIso_one,
    ModuleLaw.OrderAction.Iso.map_refl, BasicAtlas.ofGlobalOrderIso_refl]
  rfl

/-- Multiplication uses actual functional composition on the fixed frame. -/
theorem frameAutomorphismIso_mul (X : DrinfeldFramedAtlas Φ A)
    (a b : ModuleLaw.OrderAction.Automorphism Φ.val.order) :
    X.frameAutomorphismIso (a * b) = (X.frameAutomorphismIso b).trans (X.frameAutomorphismIso a) := by
  simp only [frameAutomorphismIso, ModuleLaw.OrderAction.Automorphism.toIso_mul,
    ModuleLaw.OrderAction.Iso.map_trans, BasicAtlas.ofGlobalOrderIso_trans]

/-- Precompose the actual framing with the inverse integral fixed-frame automorphism. -/
def frameAct (a : ModuleLaw.OrderAction.Automorphism Φ.val.order) (X : DrinfeldFramedAtlas Φ A) :
    DrinfeldFramedAtlas Φ A where
  residueMap := X.residueMap
  target := X.target
  rho := (BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := K) (X.frameAutomorphismIso a)).symm.trans X.rho
  height_zero := by
    have hz := X.rho.isoTransport_height (X.frameAutomorphismIso a)
      (BasicAtlas.OrderAction.Iso.refl X.target.val.reduction.order) X.height_zero
    have he := BasicAtlas.OrderAction.QuasiIsogeny.trans_refl
      ((BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := K) (X.frameAutomorphismIso a)).symm.trans X.rho)
    change (X.rho.isoTransport (X.frameAutomorphismIso a)
      (BasicAtlas.OrderAction.Iso.refl X.target.val.reduction.order)).hom.val.HasConstantChartHeight
        π (Nat.card 𝓀[K]) 0 at hz
    exact (congrArg (fun q => q.hom.val.HasConstantChartHeight π (Nat.card 𝓀[K]) 0) he).mp hz


@[simp]
theorem frameAct_residueMap (a : ModuleLaw.OrderAction.Automorphism Φ.val.order) (X : DrinfeldFramedAtlas Φ A) :
    (frameAct a X).residueMap = X.residueMap := rfl

@[simp]
theorem frameAct_target (a : ModuleLaw.OrderAction.Automorphism Φ.val.order) (X : DrinfeldFramedAtlas Φ A) :
    (frameAct a X).target = X.target := rfl

/-- The action retains the specified whole actual framing tensor and actual inverse map. -/
theorem frameAct_rho (a : ModuleLaw.OrderAction.Automorphism Φ.val.order) (X : DrinfeldFramedAtlas Φ A) :
    (frameAct a X).rho =
      (BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := K) (X.frameAutomorphismIso a)).symm.trans X.rho := rfl

/-- The integral identity fixes the whole actual framed representative. -/
@[simp]
theorem frameAct_one (X : DrinfeldFramedAtlas Φ A) : frameAct 1 X = X := by
  cases X with
  | mk residueMap target rho height_zero =>
    unfold frameAct
    congr 1
    rw [frameAutomorphismIso_one]
    change (BasicAtlas.OrderAction.QuasiIsogeny.refl _).trans rho = rho
    exact BasicAtlas.OrderAction.QuasiIsogeny.refl_trans _

set_option maxHeartbeats 1000000 in
/-- Inverse precomposition gives the actual left multiplication law on representatives. -/
theorem frameAct_mul (a b : ModuleLaw.OrderAction.Automorphism Φ.val.order) (X : DrinfeldFramedAtlas Φ A) :
    frameAct (a * b) X = frameAct a (frameAct b X) := by
  cases X with
  | mk residueMap target rho height_zero =>
    unfold frameAct
    congr 1
    rw [frameAutomorphismIso_mul, BasicAtlas.OrderAction.QuasiIsogeny.ofIso_trans]
    change ((BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := K) _).symm.trans
      (BasicAtlas.OrderAction.QuasiIsogeny.ofIso _).symm).trans rho = _
    exact BasicAtlas.OrderAction.QuasiIsogeny.trans_assoc _ _ _

/-- The actual integral full-order fixed-frame automorphism group acts on actual framed representatives. -/
instance frameAutomorphismMulAction :
    MulAction (ModuleLaw.OrderAction.Automorphism Φ.val.order) (DrinfeldFramedAtlas Φ A) where
  smul := frameAct
  one_smul := frameAct_one
  mul_smul := frameAct_mul

/-- The group action is exactly inverse precomposition of the specified actual framing. -/
@[simp]
theorem frameAutomorphism_smul_eq (a : ModuleLaw.OrderAction.Automorphism Φ.val.order)
    (X : DrinfeldFramedAtlas Φ A) : a • X = frameAct a X := rfl

end Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas
