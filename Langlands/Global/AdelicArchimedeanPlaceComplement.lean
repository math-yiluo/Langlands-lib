import Langlands.Global.AdelicBlockParabolicPlace

/-! # Deleting an archimedean coordinate of an adelic matrix -/

noncomputable section

universe u

namespace Langlands.Global.AdelicGL

open NumberField Langlands.GeneralLinear RankinSelbergGlobal
open scoped Classical

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

local notation "RP" => {v : InfinitePlace F // InfinitePlace.IsReal v}
local notation "CP" => {v : InfinitePlace F // InfinitePlace.IsComplex v}
local notation "RealFactors" => (RP → Langlands.GeneralLinear n ℝ)
local notation "ComplexFactors" => (CP → Langlands.GeneralLinear n ℂ)

private def realCoordinate (v : RP) : ArchimedeanGL F n →* Langlands.GeneralLinear n ℝ :=
  Matrix.GeneralLinearGroup.map
    ((Pi.evalRingHom (fun _ : RP => ℝ) v).comp (RingHom.fst _ _))

private def complexCoordinate (v : CP) : ArchimedeanGL F n →* Langlands.GeneralLinear n ℂ :=
  Matrix.GeneralLinearGroup.map
    ((Pi.evalRingHom (fun _ : CP => ℂ) v).comp (RingHom.snd _ _))

omit [NumberField F] in
private theorem placeGL_coordinates (a : ArchimedeanGL F n) :
    placeGL F n (fun v => realCoordinate F n v a, fun v => complexCoordinate F n v a) = a := by
  apply Units.ext
  exact Matrix.ext fun _ _ => Prod.ext rfl rfl

/-- Assemble the actual full adelic matrix from its real, complex and finite matrix data. -/
def assemblePlaces :
    ((RealFactors × ComplexFactors) × FiniteAdelicGL F n) →* AdelicGL F n :=
  (split F n).symm.toMonoidHom.comp
    (MonoidHom.prodMap ((archimedeanGLCoordinates F n).symm.toMonoidHom.comp (placeGL F n))
      (MonoidHom.id _))

private theorem assemblePlaces_coordinates (x : AdelicGL F n) :
    let a := archimedeanGLCoordinates F n (infinite F n x)
    assemblePlaces F n
      ((fun v => realCoordinate F n v a, fun v => complexCoordinate F n v a), finite F n x) = x := by
  intro a
  change pair F n ((archimedeanGLCoordinates F n).symm
    (placeGL F n (fun v => realCoordinate F n v a, fun v => complexCoordinate F n v a)))
    (finite F n x) = x
  rw [placeGL_coordinates]
  exact congrArg (fun g => pair F n g (finite F n x))
    ((archimedeanGLCoordinates F n).symm_apply_apply (infinite F n x)) |>.trans
      (pair_projections F n x)

private theorem update_mulSingle {I G : Type*} [DecidableEq I] [Monoid G]
    (r : I → G) (v : I) :
    Function.update r v 1 * Pi.mulSingle v (r v) = r := by
  funext w
  by_cases hw : w = v
  · subst w
    simp
  · simp [Function.update_of_ne hw, Pi.mulSingle_eq_of_ne hw]

private theorem commute_update_mulSingle {I G : Type*} [DecidableEq I] [Monoid G]
    (r : I → G) (v : I) (g : G) :
    Commute (Function.update r v 1) (Pi.mulSingle v g) := by
  show Function.update r v 1 * Pi.mulSingle v g = Pi.mulSingle v g * Function.update r v 1
  funext w
  by_cases hw : w = v
  · subst w
    simp
  · simp [Function.update_of_ne hw, Pi.mulSingle_eq_of_ne hw]

/-- Every adelic matrix decomposes into an element with the real coordinate removed
and a matrix supported at that place. The first element commutes with the entire
image of the place group. -/
theorem exists_realPlace_complement (v : RP) (x : AdelicGL F n) :
    ∃ (y : AdelicGL F n) (g : Langlands.GeneralLinear n ℝ),
      (∀ h, Commute y (realPlaceInclusion F n v h)) ∧
      y * realPlaceInclusion F n v g = x := by
  let a := archimedeanGLCoordinates F n (infinite F n x)
  let r : RealFactors := fun w => realCoordinate F n w a
  let c : ComplexFactors := fun w => complexCoordinate F n w a
  let b := finite F n x
  let p : (RealFactors × ComplexFactors) × FiniteAdelicGL F n :=
    ((Function.update r v 1, c), b)
  refine ⟨assemblePlaces F n p, r v, ?_, ?_⟩
  · intro h
    let q : (RealFactors × ComplexFactors) × FiniteAdelicGL F n := ((Pi.mulSingle v h, 1), 1)
    have hcomm : Commute p q := by
      change p * q = q * p
      exact Prod.ext (Prod.ext (commute_update_mulSingle r v h).eq
        ((mul_one c).trans (one_mul c).symm)) ((mul_one b).trans (one_mul b).symm)
    exact hcomm.map (assemblePlaces F n)
  · let q : (RealFactors × ComplexFactors) × FiniteAdelicGL F n := ((Pi.mulSingle v (r v), 1), 1)
    change assemblePlaces F n p * assemblePlaces F n q = x
    have hsplit : p * q = ((r, c), b) :=
      Prod.ext (Prod.ext (update_mulSingle r v) (mul_one c)) (mul_one b)
    rw [← (assemblePlaces F n).map_mul p q, hsplit]
    exact assemblePlaces_coordinates F n x

/-- The same decomposition at a complex place in the actual mixed coordinates. -/
theorem exists_complexPlace_complement (v : CP) (x : AdelicGL F n) :
    ∃ (y : AdelicGL F n) (g : Langlands.GeneralLinear n ℂ),
      (∀ h, Commute y (complexPlaceInclusion F n v h)) ∧
      y * complexPlaceInclusion F n v g = x := by
  let a := archimedeanGLCoordinates F n (infinite F n x)
  let r : RealFactors := fun w => realCoordinate F n w a
  let c : ComplexFactors := fun w => complexCoordinate F n w a
  let b := finite F n x
  let p : (RealFactors × ComplexFactors) × FiniteAdelicGL F n :=
    ((r, Function.update c v 1), b)
  refine ⟨assemblePlaces F n p, c v, ?_, ?_⟩
  · intro h
    let q : (RealFactors × ComplexFactors) × FiniteAdelicGL F n := ((1, Pi.mulSingle v h), 1)
    have hcomm : Commute p q := by
      change p * q = q * p
      exact Prod.ext (Prod.ext ((mul_one r).trans (one_mul r).symm)
        (commute_update_mulSingle c v h).eq) ((mul_one b).trans (one_mul b).symm)
    exact hcomm.map (assemblePlaces F n)
  · let q : (RealFactors × ComplexFactors) × FiniteAdelicGL F n := ((1, Pi.mulSingle v (c v)), 1)
    change assemblePlaces F n p * assemblePlaces F n q = x
    have hsplit : p * q = ((r, c), b) :=
      Prod.ext (Prod.ext (mul_one r) (update_mulSingle c v)) (mul_one b)
    rw [← (assemblePlaces F n).map_mul p q, hsplit]
    exact assemblePlaces_coordinates F n x

end Langlands.Global.AdelicGL
