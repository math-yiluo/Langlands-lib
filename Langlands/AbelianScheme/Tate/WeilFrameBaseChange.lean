import Langlands.AbelianScheme.Tate.WeilAlongHomBaseChange
import Langlands.AbelianScheme.Tate.WeilFrame
import Langlands.AbelianScheme.Tate.AdelicFrameBaseChange
import Langlands.Shimura.PEL.FormIsoTransport

/-! # Pointed base change of Weil-compatible adelic frames -/

universe u v w
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
noncomputable section

namespace Langlands.AbelianScheme.Tate
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.GroupScheme Langlands.Shimura.PEL

variable {S S' : Scheme.{u}} (b : S' ⟶ S) (A : AbelianScheme S)

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (composition : PullbackTensorCompositionStatement.{u})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
  (symmetry : PullbackTensorSymmetryStatement.{u})
  (stability : PicardZeroPullbackStatement.{u})
  (universality : PicardZeroUniversalBaseChangeStatement.{u})
  (hA : HasDualScheme A) (geometryA : DualSchemeGeometry A hA)
  (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
    structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (hA' : HasDualScheme ((baseChange b).obj A))
  (geometryA' : DualSchemeGeometry ((baseChange b).obj A) hA')
  (MA' : LineBundle ((relativeSpace ((baseChange b).obj A).X.hom).obj
    (dualScheme ((baseChange b).obj A) hA')))
  (evaluationA' : tensorObj (poincareFamily ((baseChange b).obj A) hA').obj.carrier
    MA'.obj ≅ structureSheaf ((relativeSpace ((baseChange b).obj A).X.hom).obj
      (dualScheme ((baseChange b).obj A) hA')))

local notation "DA" => dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
  evaluationA stability composition unitCoherence associativity comparison symmetry
set_option quotPrecheck false in
local notation "DAb" => dualAbelianSchemeFromEvaluation ((baseChange b).obj A) hA'
  geometryA' preservation MA' evaluationA' stability composition unitCoherence associativity
  comparison symmetry
local notation "lamBC" => canonicalDualValuedBaseChange b A preservation composition
  unitCoherence associativity comparison symmetry stability universality hA geometryA MA
  evaluationA hA' geometryA' MA' evaluationA'

variable [QuasiSeparatedSpace S] [QuasiSeparatedSpace S']
  (compatibility : RelativeFiniteWeilTransitionStatement.{u})
  (lam : A ⟶ dualAbelianSchemeFromEvaluation A hA geometryA preservation MA evaluationA
    stability composition unitCoherence associativity comparison symmetry)
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  {D : Type v} [Ring D] [Algebra ℚ D] (i : D →ₐ[ℚ] End0 A)
  (V : Type w) [AddCommGroup V] [Module ℚ V] [Module D V] [IsScalarTower ℚ D V]
  (ψ : LinearMap.BilinForm ℚ V)
  {Ω : Type u} [Field Ω] (s : Spec (.of Ω) ⟶ S')

set_option quotPrecheck false in
local notation "iBC" => (AbelianScheme.rationalBaseChangeEnd b A).comp i

section Full
local notation "FrameA" => WeilAdelicFrame preservation composition unitCoherence associativity
  comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ (s ≫ b)
local notation "Frameb" => WeilAdelicFrame preservation composition unitCoherence associativity
  comparison symmetry stability hA' geometryA' MA' evaluationA' compatibility (lamBC lam) h
  iBC V ψ s
local notation "rightA" => weilAdelicFrameRightAction preservation composition unitCoherence
  associativity comparison symmetry stability hA geometryA MA evaluationA compatibility lam h
  i V ψ (s ≫ b)
local notation "rightb" => weilAdelicFrameRightAction preservation composition unitCoherence
  associativity comparison symmetry stability hA' geometryA' MA' evaluationA' compatibility
  (lamBC lam) h iBC V ψ s

/-- Actual tensor-linear Tate base change restricts to the Weil-compatible frame subtype. -/
def weilAdelicFrameBaseChange : Frameb ≃ FrameA := by
  letI := scalarExtensionAlgebraModule D V (Global.FiniteAdeles ℚ)
  letI := finiteAdeleAlgebraModule ((baseChange b).obj A) (Over.mk s) (fun _ => True) h iBC
  letI := finiteAdeleAlgebraModule A (Over.mk (s ≫ b)) (fun _ => True) h i
  letI := GroupScheme.Tate.finiteAdeleModule ((baseChange b).obj A).toGrp
    (Over.mk s) (fun _ => True) h
  letI := GroupScheme.Tate.finiteAdeleModule A.toGrp (Over.mk (s ≫ b)) (fun _ => True) h
  letI := TateTwist.Divisibility.finiteAdeleModule Γ((Over.mk s).left, ⊤) (fun _ => True) h
  letI := TateTwist.Divisibility.finiteAdeleModule Γ((Over.mk (s ≫ b)).left, ⊤) (fun _ => True) h
  exact FormIso.transport (finiteAdeleAlgebraBaseChange b (Over.mk s) (fun _ => True) A i h)
    (LinearEquiv.refl (Global.FiniteAdeles ℚ) _) (fun x y =>
      (adelicWeilAlongHomBilinearMap_baseChange b A preservation composition unitCoherence
        associativity comparison symmetry stability universality hA geometryA MA evaluationA
        hA' geometryA' MA' evaluationA' (Over.mk s) compatibility lam (fun _ => True) h x y).symm)

local notation "frameBC" => weilAdelicFrameBaseChange b A preservation composition unitCoherence
  associativity comparison symmetry stability universality hA geometryA MA evaluationA hA'
  geometryA' MA' evaluationA' compatibility lam h i V ψ s

@[simp] theorem weilAdelicFrameBaseChange_apply (eta : Frameb)
    (x : (Global.FiniteAdeles ℚ) ⊗[ℚ] V) :
    (frameBC eta).1 x = rationalBaseChange b A (Over.mk s) (fun _ => True) (eta.1 x) := rfl

@[simp] theorem weilAdelicFrameBaseChange_symm_apply (eta : FrameA)
    (x : (Global.FiniteAdeles ℚ) ⊗[ℚ] V) :
    ((frameBC).symm eta).1 x =
      (rationalBaseChange b A (Over.mk s) (fun _ => True)).symm (eta.1 x) := rfl

/-- Forgetting the form condition recovers the existing ambient frame comparison. -/
theorem weilAdelicFrameBaseChange_underlying (eta : Frameb) :
    letI := scalarExtensionAlgebraModule D V (Global.FiniteAdeles ℚ)
    (frameBC eta).1 =
      adelicFrameBaseChange b A h i ((Global.FiniteAdeles ℚ) ⊗[ℚ] V) s eta.1 := rfl

/-- Pointed base change preserves the right precomposition action. -/
theorem weilAdelicFrameBaseChange_right :
    letI := rightb
    letI := rightA
    ∀ (eta : Frameb) (g : ScalarExtensionSimilitudes D V (Global.FiniteAdeles ℚ) ψ),
      frameBC (right eta g) = right (frameBC eta) g := by
  let := rightb
  let := rightA
  intro eta g
  apply Subtype.ext
  ext x
  rfl

/-- The compatible-frame comparison descends to arbitrary right subgroup orbits. -/
def weilAdelicFrameRightOrbitBaseChange
    (U : Subgroup (ScalarExtensionSimilitudes D V (Global.FiniteAdeles ℚ) ψ)) :
    letI := rightb
    letI := rightA
    RightOrbit Frameb U ≃ RightOrbit FrameA U := by
  let := rightb
  let := rightA
  exact RightOrbit.equiv U frameBC
    (weilAdelicFrameBaseChange_right b A preservation composition unitCoherence associativity
      comparison symmetry stability universality hA geometryA MA evaluationA hA' geometryA'
      MA' evaluationA' compatibility lam h i V ψ s)

local notation "orbitBC" => weilAdelicFrameRightOrbitBaseChange b A preservation composition
  unitCoherence associativity comparison symmetry stability universality hA geometryA MA
  evaluationA hA' geometryA' MA' evaluationA' compatibility lam h i V ψ s

@[simp] theorem weilAdelicFrameRightOrbitBaseChange_mk
    (U : Subgroup (ScalarExtensionSimilitudes D V (Global.FiniteAdeles ℚ) ψ)) :
    letI := rightb
    letI := rightA
    ∀ eta : Frameb, orbitBC U (RightOrbit.mk U eta) = RightOrbit.mk U (frameBC eta) := by
  intro eta
  rfl

/-- The same comparison commutes with every allowed level/Hecke translation. -/
theorem weilAdelicFrameRightOrbitBaseChange_translate
    {U U' : Subgroup (ScalarExtensionSimilitudes D V (Global.FiniteAdeles ℚ) ψ)}
    (g : ScalarExtensionSimilitudes D V (Global.FiniteAdeles ℚ) ψ)
    (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ U') :
    letI := rightb
    letI := rightA
    ∀ q : RightOrbit Frameb U,
      orbitBC U' (RightOrbit.translate g hg q) = RightOrbit.translate g hg (orbitBC U q) := by
  let := rightb
  let := rightA
  intro q
  exact RightOrbit.map_translate frameBC
    (weilAdelicFrameBaseChange_right b A preservation composition unitCoherence associativity
      comparison symmetry stability universality hA geometryA MA evaluationA hA' geometryA'
      MA' evaluationA' compatibility lam h i V ψ s) g hg q


@[simp] theorem weilAdelicFrameRightOrbitBaseChange_symm_mk
    (U : Subgroup (ScalarExtensionSimilitudes D V (Global.FiniteAdeles ℚ) ψ)) :
    letI := rightb
    letI := rightA
    ∀ eta : FrameA, (orbitBC U).symm (RightOrbit.mk U eta) =
      RightOrbit.mk U ((frameBC).symm eta) := by
  intro eta
  rfl

/-- Forgetting to a larger subgroup commutes with pointed base change. -/
theorem weilAdelicFrameRightOrbitBaseChange_forget
    {U U' : Subgroup (ScalarExtensionSimilitudes D V (Global.FiniteAdeles ℚ) ψ)} (hU : U ≤ U') :
    letI := rightb
    letI := rightA
    ∀ q : RightOrbit Frameb U,
      orbitBC U' (RightOrbit.translate 1 (by intro u hu; simpa using hU hu) q) =
        RightOrbit.translate 1 (by intro u hu; simpa using hU hu) (orbitBC U q) := by
  intro q
  exact weilAdelicFrameRightOrbitBaseChange_translate b A preservation composition
    unitCoherence associativity comparison symmetry stability universality hA geometryA MA
    evaluationA hA' geometryA' MA' evaluationA' compatibility lam h i V ψ s 1 _ q

end Full


section Away
variable {m : ℕ} (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)
local notation "FrameA" => WeilPrimeToAdelicFrame preservation composition unitCoherence associativity
  comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ (s ≫ b) hAway
local notation "Frameb" => WeilPrimeToAdelicFrame preservation composition unitCoherence associativity
  comparison symmetry stability hA' geometryA' MA' evaluationA' compatibility (lamBC lam) h
  iBC V ψ s hAway
local notation "rightA" => weilPrimeToAdelicFrameRightAction preservation composition unitCoherence
  associativity comparison symmetry stability hA geometryA MA evaluationA compatibility lam h
  i V ψ (s ≫ b) hAway
local notation "rightb" => weilPrimeToAdelicFrameRightAction preservation composition unitCoherence
  associativity comparison symmetry stability hA' geometryA' MA' evaluationA' compatibility
  (lamBC lam) h iBC V ψ s hAway

/-- Actual tensor-linear Tate base change restricts to the Weil-compatible frame subtype. -/
def weilPrimeToAdelicFrameBaseChange : Frameb ≃ FrameA := by
  letI := scalarExtensionAlgebraModule D V (Global.PrimeToFiniteAdeles m)
  letI := primeToFiniteAdeleAlgebraModule ((baseChange b).obj A) (Over.mk s) hAway iBC
  letI := primeToFiniteAdeleAlgebraModule A (Over.mk (s ≫ b)) hAway i
  letI := GroupScheme.Tate.primeToFiniteAdeleModule ((baseChange b).obj A).toGrp
    (Over.mk s) hAway
  letI := GroupScheme.Tate.primeToFiniteAdeleModule A.toGrp (Over.mk (s ≫ b)) hAway
  letI := TateTwist.Divisibility.primeToFiniteAdeleModule Γ((Over.mk s).left, ⊤) hAway
  letI := TateTwist.Divisibility.primeToFiniteAdeleModule Γ((Over.mk (s ≫ b)).left, ⊤) hAway
  exact FormIso.transport (primeToFiniteAdeleAlgebraBaseChange b (Over.mk s) A i hAway)
    (LinearEquiv.refl (Global.PrimeToFiniteAdeles m) _) (fun x y =>
      (awayAdelicWeilAlongHomBilinearMap_baseChange b A preservation composition unitCoherence
        associativity comparison symmetry stability universality hA geometryA MA evaluationA
        hA' geometryA' MA' evaluationA' (Over.mk s) compatibility lam hAway x y).symm)

local notation "frameBC" => weilPrimeToAdelicFrameBaseChange b A preservation composition unitCoherence
  associativity comparison symmetry stability universality hA geometryA MA evaluationA hA'
  geometryA' MA' evaluationA' compatibility lam h i V ψ s hAway

@[simp] theorem weilPrimeToAdelicFrameBaseChange_apply (eta : Frameb)
    (x : (Global.PrimeToFiniteAdeles m) ⊗[ℚ] V) :
    (frameBC eta).1 x = rationalBaseChange b A (Over.mk s) (fun n => Nat.Coprime n m) (eta.1 x) := rfl

@[simp] theorem weilPrimeToAdelicFrameBaseChange_symm_apply (eta : FrameA)
    (x : (Global.PrimeToFiniteAdeles m) ⊗[ℚ] V) :
    ((frameBC).symm eta).1 x =
      (rationalBaseChange b A (Over.mk s) (fun n => Nat.Coprime n m)).symm (eta.1 x) := rfl

/-- Forgetting the form condition recovers the existing ambient frame comparison. -/
theorem weilPrimeToAdelicFrameBaseChange_underlying (eta : Frameb) :
    letI := scalarExtensionAlgebraModule D V (Global.PrimeToFiniteAdeles m)
    (frameBC eta).1 =
      primeToAdelicFrameBaseChange b A m hAway i ((Global.PrimeToFiniteAdeles m) ⊗[ℚ] V) s eta.1 := rfl

/-- Pointed base change preserves the right precomposition action. -/
theorem weilPrimeToAdelicFrameBaseChange_right :
    letI := rightb
    letI := rightA
    ∀ (eta : Frameb) (g : ScalarExtensionSimilitudes D V (Global.PrimeToFiniteAdeles m) ψ),
      frameBC (right eta g) = right (frameBC eta) g := by
  let := rightb
  let := rightA
  intro eta g
  apply Subtype.ext
  ext x
  rfl

/-- The compatible-frame comparison descends to arbitrary right subgroup orbits. -/
def weilPrimeToAdelicFrameRightOrbitBaseChange
    (U : Subgroup (ScalarExtensionSimilitudes D V (Global.PrimeToFiniteAdeles m) ψ)) :
    letI := rightb
    letI := rightA
    RightOrbit Frameb U ≃ RightOrbit FrameA U := by
  let := rightb
  let := rightA
  exact RightOrbit.equiv U frameBC
    (weilPrimeToAdelicFrameBaseChange_right b A preservation composition unitCoherence associativity
      comparison symmetry stability universality hA geometryA MA evaluationA hA' geometryA'
      MA' evaluationA' compatibility lam h i V ψ s hAway)

local notation "orbitBC" => weilPrimeToAdelicFrameRightOrbitBaseChange b A preservation composition
  unitCoherence associativity comparison symmetry stability universality hA geometryA MA
  evaluationA hA' geometryA' MA' evaluationA' compatibility lam h i V ψ s hAway

@[simp] theorem weilPrimeToAdelicFrameRightOrbitBaseChange_mk
    (U : Subgroup (ScalarExtensionSimilitudes D V (Global.PrimeToFiniteAdeles m) ψ)) :
    letI := rightb
    letI := rightA
    ∀ eta : Frameb, orbitBC U (RightOrbit.mk U eta) = RightOrbit.mk U (frameBC eta) := by
  intro eta
  rfl

/-- The same comparison commutes with every allowed level/Hecke translation. -/
theorem weilPrimeToAdelicFrameRightOrbitBaseChange_translate
    {U U' : Subgroup (ScalarExtensionSimilitudes D V (Global.PrimeToFiniteAdeles m) ψ)}
    (g : ScalarExtensionSimilitudes D V (Global.PrimeToFiniteAdeles m) ψ)
    (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ U') :
    letI := rightb
    letI := rightA
    ∀ q : RightOrbit Frameb U,
      orbitBC U' (RightOrbit.translate g hg q) = RightOrbit.translate g hg (orbitBC U q) := by
  let := rightb
  let := rightA
  intro q
  exact RightOrbit.map_translate frameBC
    (weilPrimeToAdelicFrameBaseChange_right b A preservation composition unitCoherence associativity
      comparison symmetry stability universality hA geometryA MA evaluationA hA' geometryA'
      MA' evaluationA' compatibility lam h i V ψ s hAway) g hg q


@[simp] theorem weilPrimeToAdelicFrameRightOrbitBaseChange_symm_mk
    (U : Subgroup (ScalarExtensionSimilitudes D V (Global.PrimeToFiniteAdeles m) ψ)) :
    letI := rightb
    letI := rightA
    ∀ eta : FrameA, (orbitBC U).symm (RightOrbit.mk U eta) =
      RightOrbit.mk U ((frameBC).symm eta) := by
  intro eta
  rfl

/-- Forgetting to a larger subgroup commutes with pointed base change. -/
theorem weilPrimeToAdelicFrameRightOrbitBaseChange_forget
    {U U' : Subgroup (ScalarExtensionSimilitudes D V (Global.PrimeToFiniteAdeles m) ψ)} (hU : U ≤ U') :
    letI := rightb
    letI := rightA
    ∀ q : RightOrbit Frameb U,
      orbitBC U' (RightOrbit.translate 1 (by intro u hu; simpa using hU hu) q) =
        RightOrbit.translate 1 (by intro u hu; simpa using hU hu) (orbitBC U q) := by
  intro q
  exact weilPrimeToAdelicFrameRightOrbitBaseChange_translate b A preservation composition
    unitCoherence associativity comparison symmetry stability universality hA geometryA MA
    evaluationA hA' geometryA' MA' evaluationA' compatibility lam h i V ψ s hAway 1 _ q

end Away

end Langlands.AbelianScheme.Tate
