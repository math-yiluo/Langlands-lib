import Langlands.Geometry.FormalGroup.Copies
import Langlands.Geometry.FormalGroup.DrinfeldCyclicOrderAction
import Langlands.Geometry.FormalGroup.DrinfeldSubfieldCharacters

/-! # Assembling a special division-order module from a one-coordinate factor -/

noncomputable section

namespace Langlands.FormalGroup.LocalDivision

open ValuativeRel CentralDivision CentralSimple ModuleLaw Langlands.ClassFieldTheory.Local
open Langlands.LocalField Langlands.LocalGalois.Separable

universe u

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {E : IntermediateField K (SeparableClosure K)} [FiniteDimensional K E] [IsGalois K E]
  (hE : ArithmeticUnramified K E) (ι : E →ₐ[K] D)
  (hdegree : Module.finrank K E = CentralSimple.reducedDegree K D)
variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ]

local instance frameLineLocalHom : IsLocalHom (algebraMap 𝒪[K] (SubfieldIntegerRing K D ι)) :=
  subfieldIntegerAlgebra_isLocalHom ι

local notation "d" => CentralSimple.reducedDegree K D
local notation "C" => SubfieldIntegerRing K D ι
local notation "hC" => subfieldArithmeticUnramifiedOfReducedDegree K D E ι hE hdegree
local notation "s" => finiteUnramifiedFrobenius K E hE
local notation "τ" => subfieldIntegerFrobenius ι s hC
local notation "r" => IsLocalRing.residue (SubfieldIntegerRing K D ι)
local notation "rF" => subfieldResidueFrobenius ι hC

include hE hdegree in
private theorem frameLineResidue_twist (a : C) (n : ℕ) :
    r ((τ⁻¹ ^ n) a) = (rF⁻¹ ^ n) (r a) := by
  have hinv (b : C) : r (τ⁻¹ b) = rF⁻¹ (r b) := by
    apply (rF).injective
    change rF (r (τ⁻¹ b)) = rF ((rF).symm (r b))
    rw [(rF).apply_symm_apply, subfieldResidueFrobenius_apply]
    have h := subfieldIntegerFrobenius_residue_pow ι s hC
      (subfieldArithmeticFrobenius_sub_lt_one K D E ι hE) (τ⁻¹ b)
    change r (τ ((τ).symm b)) = (r (τ⁻¹ b)) ^ Nat.card 𝓀[K] at h
    rw [(τ).apply_symm_apply] at h
    exact h.symm
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ', AlgEquiv.mul_apply, hinv, ih]

variable (H : ModuleLaw 𝒪[K] κ Unit)
  (f : SubfieldIntegerRing K D ι →+* CommLaw.Hom H.groupLaw H.groupLaw)
  (t : CommLaw.Hom H.groupLaw H.groupLaw)

local notation "diag" => CommLaw.Hom.diagonalRingHom (I := Fin d) (G := H.groupLaw)
local notation "G" => H.groupLaw.copies (Fin d)

private def frameLineCoefficients : C →+* CommLaw.Hom G G :=
  (diag).comp (RingHom.pi fun i : Fin d => f.comp ((τ⁻¹ ^ i.val).toAlgHom.toRingHom))

variable {π : 𝒪[K]} (hπ : Irreducible π) (j : Dˣ)
  (hjPow : (j : D) ^ CentralSimple.reducedDegree K D = algebraMap K D (π : K))
  (hjComm : ∀ a : E, (j : D) * ι a = ι (finiteUnramifiedFrobenius K E hE a) * (j : D))
  (htPow : t ^ CentralSimple.reducedDegree K D = f (algebraMap 𝒪[K] _ π))
  (htComm : ∀ a : SubfieldIntegerRing K D ι,
    t * f a = f (subfieldIntegerFrobenius ι (finiteUnramifiedFrobenius K E hE)
      (subfieldArithmeticUnramifiedOfReducedDegree K D E ι hE hdegree) a) * t)

local notation "N" => H.copies (Fin d)
local notation "F" => frameLineCoefficients hE ι hdegree H f
local notation "T" => (diag) (fun _ => t)

include htPow htComm in
private def frameLineGroupAction : IntegerRing K D →+* CommLaw.Hom G G :=
  liftCyclicOrder E hE ι hdegree hπ hjPow
    ((finiteUnramifiedFrobenius_orderOf K E hE).trans hdegree) hjComm F T
    (by
      change (diag) (fun _ => t) ^ d = (diag) (fun i => f ((τ⁻¹ ^ i.val) (algebraMap 𝒪[K] C π)))
      rw [← map_pow (diag)]
      apply congrArg (diag)
      funext i
      change t ^ d = f ((τ⁻¹ ^ i.val) (algebraMap 𝒪[K] C π))
      rwa [AlgEquiv.commutes])
    (by
      intro a
      change (diag) (fun _ => t) * (diag) (fun i => f ((τ⁻¹ ^ i.val) a)) =
        (diag) (fun i => f ((τ⁻¹ ^ i.val) (τ a))) * (diag) (fun _ => t)
      rw [← map_mul (diag), ← map_mul (diag)]
      apply congrArg (diag)
      funext i
      change t * f ((τ⁻¹ ^ i.val) a) = f ((τ⁻¹ ^ i.val) (τ a)) * t
      rw [htComm]
      have hc := ((Commute.refl τ).inv_right.pow_right i.val).eq
      exact congrArg (fun σ : C ≃ₐ[𝒪[K]] C => f (σ a) * t) hc)

local notation "A" => frameLineGroupAction hE ι hdegree H f t hπ j hjPow hjComm htPow htComm

private theorem frameLineGroupAction_subfield (a : C) :
    A (subfieldIntegerInclusion K D ι a) = F a := by
  unfold frameLineGroupAction
  rw [liftCyclicOrder_subfield]

variable (hfScalar : ∀ a : 𝒪[K], f (algebraMap 𝒪[K] (SubfieldIntegerRing K D ι) a) = H.action a)

include hfScalar in
private theorem frameLineGroupAction_scalar (a : 𝒪[K]) :
    A (algebraMap 𝒪[K] (IntegerRing K D) a) = (N).action a := by
  rw [← (subfieldIntegerInclusion K D ι).commutes a, frameLineGroupAction_subfield]
  change (diag) (fun i => f ((τ⁻¹ ^ i.val) (algebraMap 𝒪[K] C a))) = (diag) (fun _ => H.action a)
  apply congrArg (diag)
  funext i
  rw [AlgEquiv.commutes, hfScalar]

include hfScalar in
private def frameLineOrderAction : OrderAction (IntegerRing K D) N where
  action :=
    { toFun := fun z =>
        ⟨A z, fun a => by
          let b : CommLaw.Hom G G := (N).action a
          have hs : A (algebraMap 𝒪[K] (IntegerRing K D) a) = b :=
            frameLineGroupAction_scalar hE ι hdegree H f t hπ j hjPow hjComm htPow htComm hfScalar a
          have hc : A z * b = b * A z := by
            rw [← hs, ← (A).map_mul, ← (A).map_mul]
            exact congrArg (A) (Algebra.commutes a z).symm
          exact hc⟩
      map_zero' := ModuleLaw.Hom.ext (map_zero A)
      map_one' := ModuleLaw.Hom.ext (map_one A)
      map_add' := fun x y => ModuleLaw.Hom.ext (map_add A x y)
      map_mul' := fun x y => ModuleLaw.Hom.ext (map_mul A x y) }
  extends_scalars := frameLineGroupAction_scalar hE ι hdegree H f t hπ j hjPow hjComm htPow htComm hfScalar

variable [Algebra 𝓀[K] κ] [IsScalarTower 𝒪[K] 𝓀[K] κ]
  (χ : IsLocalRing.ResidueField (SubfieldIntegerRing K D ι) →ₐ[𝓀[K]] κ)
  (hfTangent : ∀ a : SubfieldIntegerRing K D ι,
    (f a).toCoordinateMap.linearCoeff () () = χ (IsLocalRing.residue _ a))

include hfTangent in
/-- The product of the inverse coefficient twists of the line, with the
semilinear uniformizer acting diagonally, is special. -/
def specialFrameFromLine : SpecialModule K D ι κ where
  formalModule := N
  order := frameLineOrderAction hE ι hdegree H f t hπ j hjPow hjComm htPow htComm hfScalar
  unramified := hC
  tangent := by
    intro S _ _ φ
    let c := subfieldCyclicCharacter ι hC χ
    refine ⟨{
      characters := fun i => φ.comp (c i).toRingHom
      distinct := ?_
      coordinates := LinearEquiv.refl S _
      diagonalizes := ?_ }⟩
    · intro i k heq
      apply subfieldCyclicCharacter_injective ι hC χ
      apply AlgHom.ext
      intro a
      apply φ.injective
      exact RingHom.congr_fun heq a
    · intro a x i
      change (frameLineOrderAction hE ι hdegree H f t hπ j hjPow hjComm htPow htComm hfScalar).fiberTangent
        φ (subfieldIntegerInclusion K D ι a) x i = φ (c i a) * x i
      rw [OrderAction.fiberTangent_apply_apply]
      have hlin (k : Fin d) : (A (subfieldIntegerInclusion K D ι a)).toCoordinateMap.linearCoeff i k =
          CoordinateMap.scalarLinearCoeff (c i a) i k := by
        rw [frameLineGroupAction_subfield]
        change (CommLaw.Hom.diagonal fun m : Fin d => f ((τ⁻¹ ^ m.val) a)).toCoordinateMap.linearCoeff i k = _
        rw [CommLaw.Hom.diagonal_linearCoeff, hfTangent, frameLineResidue_twist hE ι hdegree]
        rfl
      change (∑ k, φ ((A (subfieldIntegerInclusion K D ι a)).toCoordinateMap.linearCoeff i k) * x k) = _
      rw [Finset.sum_eq_single i]
      · simp [hlin, CoordinateMap.scalarLinearCoeff]
      · intro k _ hki
        simp [hlin, CoordinateMap.scalarLinearCoeff, hki]
      · simp

/-- The embedded integers act on each factor through its inverse Frobenius twist. -/
theorem specialFrameFromLine_coefficient (a : C) :
    ((specialFrameFromLine hE ι hdegree H f t hπ j hjPow hjComm htPow htComm hfScalar χ hfTangent).order.action
      (subfieldIntegerInclusion K D ι a)).toHom =
        CommLaw.Hom.diagonal (fun i : Fin d => f ((τ⁻¹ ^ i.val) a)) :=
  frameLineGroupAction_subfield hE ι hdegree H f t hπ j hjPow hjComm htPow htComm a

/-- The division uniformizer acts by the given operator on every factor. -/
theorem specialFrameFromLine_uniformizer :
    ((specialFrameFromLine hE ι hdegree H f t hπ j hjPow hjComm htPow htComm hfScalar χ hfTangent).order.action
      (drinfeldIntegralUniformizer j hjPow)).toHom =
        CommLaw.Hom.diagonal (fun _ : Fin d => t) := by
  change A (drinfeldIntegralUniformizer j hjPow) = T
  unfold frameLineGroupAction
  rw [liftCyclicOrder_uniformizer]

end Langlands.FormalGroup.LocalDivision
