import Langlands.Geometry.FormalGroup.AtlasTangentOrder
import Langlands.Geometry.FormalGroup.DrinfeldTangentUniformizer
import Langlands.Geometry.FormalGroup.SpecialAtlas

/-! # Split coefficient projectors on the compatible Drinfeld tangent module -/

noncomputable section

universe u v w s

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction

open CategoryTheory

attribute [local instance] ModuleLaw.coefficientAlgebra ModuleLaw.coefficientScalarTower

variable {O : Type u} [CommRing O] {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D] {I : Type} [Finite I]
variable {X : BasicAtlas O R I} (E : OrderAction D X) (A : CommAlgCat.{v} R)

/-- The overlap tangent representation extends the scalar action of the formal module. -/
def tangentAlgebraAction : D →ₐ[O] Module.End A (X.tangentSubmodule A) :=
  { E.tangentAction A with
    commutes' := fun c => by
      apply LinearMap.ext
      intro z
      apply Subtype.ext
      funext a
      change (E.tangentAction A (algebraMap O D c) z).val a =
        ((algebraMap O (Module.End A (X.tangentSubmodule A)) c) z).val a
      rw [Module.algebraMap_end_apply, ← algebraMap_smul A c z, E.tangentAction_apply]
      let T : CommAlgCat.{v} R := X.localAlgebra A a
      let : Algebra O T := ModuleLaw.coefficientAlgebra T
      let e := (E.chart a).map (BasicAtlas.coefficientLift (O := O) a.val T (X.localUnit A a))
      change E.chartTangent (X.localAlgebra A a) a (X.localUnit A a)
        (algebraMap O D c) (z.val a) = (algebraMap O A c) • z.val a
      have h : e.tangent (algebraMap O D c) (z.val a) = algebraMap O T c • z.val a :=
        e.tangent_scalar c (z.val a)
      have hs : algebraMap O T c = algebraMap A T (algebraMap O A c) := rfl
      exact h.trans ((congrArg (fun r : T => r • z.val a) hs).trans
        (algebraMap_smul T (algebraMap O A c) (z.val a))) }

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction

namespace Langlands.FormalGroup.LocalDivision.SpecialAtlas

open IsLocalRing ValuativeRel CentralDivision CentralSimple ModuleLaw
open scoped TensorProduct

attribute [local instance] ModuleLaw.coefficientAlgebra ModuleLaw.coefficientScalarTower

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] (ι : L →ₐ[K] D)

local instance atlasTangentProjectorsLocalHom :
    IsLocalHom (algebraMap 𝒪[K] (SubfieldIntegerRing K D ι)) := subfieldIntegerAlgebra_isLocalHom ι

variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] [Algebra 𝓀[K] κ]
  [IsScalarTower 𝒪[K] 𝓀[K] κ]
variable (χ : ResidueField (SubfieldIntegerRing K D ι) →ₐ[𝓀[K]] κ)
variable {π : 𝒪[K]} {B : Nilp.{u,v} 𝒪[K] π} (ψ : κ →ₐ[𝒪[K]] Nilp.Reduction π B.obj)
variable (X : SpecialAtlas K D ι B.obj)

local notation "d" => CentralSimple.reducedDegree K D
local notation "C" => SubfieldIntegerRing K D ι
local notation "B₀" => CommAlgCat.of B.obj B.obj
local notation "V" => BasicAtlas.tangentSubmodule X.atlas B₀
local notation "orderAction" => BasicAtlas.OrderAction.tangentAlgebraAction X.order B₀
local notation "δ" => subfieldCyclicSplitting (SpecialAtlas.unramified X) χ ψ
local notation "λs" => (fun i : Fin d => subfieldCoefficientLift (SpecialAtlas.unramified X)
  (subfieldCyclicCharacter ι (SpecialAtlas.unramified X) χ i) ψ)

/-- The actual split coefficient algebra acts on the compatible tangent module. -/
def tangentCharacterAction : (Fin d → B.obj) →ₐ[B.obj] Module.End B.obj V :=
  (((orderAction).comp (subfieldIntegerInclusion K D ι)).liftEquiv 𝒪[K] B.obj C
    (Module.End B.obj V)).comp (δ).symm.toAlgHom

local notation "ρ" => tangentCharacterAction ι χ ψ X

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 700000 in
/-- The tuple of lifted characters acts as the original embedded integer. -/
theorem tangentCharacterAction_coeff (a : C) :
    ρ (fun i => λs i a) = orderAction (subfieldIntegerInclusion K D ι a) := by
  let f : C →ₐ[𝒪[K]] Module.End B.obj V :=
    (orderAction).comp (subfieldIntegerInclusion K D ι)
  let μ := f.liftEquiv 𝒪[K] B.obj C (Module.End B.obj V)
  let z : B.obj ⊗[𝒪[K]] C := 1 ⊗ₜ[𝒪[K]] a
  have h : δ z = fun i => λs i a := by
    funext i
    change δ (1 ⊗ₜ[𝒪[K]] a) i = λs i a
    rw [subfieldCyclicSplitting_tmul, one_mul]
  change μ ((δ).symm (fun i => λs i a)) = f a
  have hz : (δ).symm (fun i => λs i a) = z :=
    (congrArg (fun t : Fin d → B.obj => (δ).symm t) h.symm).trans ((δ).symm_apply_apply z)
  exact (congrArg (fun t : B.obj ⊗[𝒪[K]] C => μ t) hz).trans
    ((AlgHom.liftEquiv_tmul f (1 : B.obj) a).trans (one_smul B.obj (f a)))

/-- The actual projector associated to a coordinate of the split coefficient algebra. -/
def tangentProjector (i : Fin d) : Module.End B.obj V := ρ (Pi.single i 1)

local notation "P" => tangentProjector ι χ ψ X

@[simp]
theorem tangentProjector_mul_same (i : Fin d) : P i * P i = P i := by
  let p : Fin d → B.obj := Pi.single i 1
  have h : p * p = p := by
    funext j
    by_cases hj : j = i <;> simp [p, hj]
  exact ((ρ).map_mul p p).symm.trans (congrArg (ρ) h)

theorem tangentProjector_mul_ne {i j : Fin d} (hij : i ≠ j) : P i * P j = 0 := by
  let p : Fin d → B.obj := Pi.single i 1
  let q : Fin d → B.obj := Pi.single j 1
  have h : p * q = 0 := by
    funext k
    by_cases hk : k = i
    · subst k
      simp [p, q, hij]
    · simp [p, hk]
  exact (((ρ).map_mul p q).symm.trans (congrArg (ρ) h)).trans ((ρ).map_zero)

theorem sum_tangentProjector : (∑ i : Fin d, P i) = 1 := by
  let p (i : Fin d) : Fin d → B.obj := Pi.single i 1
  have h : (∑ i : Fin d, p i) = 1 := by
    funext j
    simp [p, Finset.sum_apply, Pi.single_apply]
  exact (((map_sum (ρ) p Finset.univ).symm).trans (congrArg (ρ) h)).trans ((ρ).map_one)

/-- The compatible tangent module carries the original uniformizer power relation. -/
theorem tangentUniformizer_pow (j : Dˣ)
    (hPow : (j : D) ^ d = algebraMap K D (π : K)) :
    orderAction (drinfeldIntegralUniformizer j hPow) ^ d =
      algebraMap B.obj (Module.End B.obj V) (algebraMap 𝒪[K] B.obj π) := by
  exact ((map_pow (orderAction) (drinfeldIntegralUniformizer j hPow) d).symm.trans
    ((congrArg (orderAction) (drinfeldIntegralUniformizer_pow j hPow)).trans
      ((orderAction).commutes π))).trans
    (IsScalarTower.algebraMap_apply 𝒪[K] B.obj (Module.End B.obj V) π)

end Langlands.FormalGroup.LocalDivision.SpecialAtlas
