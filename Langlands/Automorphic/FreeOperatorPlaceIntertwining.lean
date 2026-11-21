import Langlands.Automorphic.OperatorSubquotientPullback
import Langlands.Global.ArchimedeanPlaceCompact
import Langlands.Global.ArchimedeanPlaceEnveloping
import Langlands.Representation.Archimedean.RealGKInfinitesimalCharacter
import Mathlib.Algebra.Group.Submonoid.Finite

/-! # Extending place intertwiners to the common free operators -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Classical TensorProduct

universe u

namespace Langlands.Global.ArchimedeanGL

open NumberField

attribute [local instance 100] LieRing.ofAssociativeRing

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

local notation "RP" => {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "CP" => {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}

/-- Every complexified Lie element is the sum of its actual place components. -/
theorem sum_placeComplexLieInclusions (Z : ComplexLieAlgebra F n) :
    (∑ v : RP, realPlaceComplexLieInclusion F n v (realPlaceComplexLieProjection F n v Z)) +
      (∑ v : CP, complexPlaceComplexLieInclusion F n v (complexPlaceComplexLieProjection F n v Z)) = Z := by
  induction Z using TensorProduct.inductionOn with
  | tmul z X =>
    simpa only [realPlaceComplexLieProjection_tmul, realPlaceComplexLieInclusion_tmul,
      complexPlaceComplexLieProjection_tmul, complexPlaceComplexLieInclusion_tmul,
      TensorProduct.tmul_add, TensorProduct.tmul_sum] using
      congrArg (fun Y : RealLieAlgebra F n => z ⊗ₜ[ℝ] Y) (sum_placeLieInclusions F n X)
  | add X Y hX hY =>
    simp only [map_add, Finset.sum_add_distrib] at *
    rw [add_add_add_comm, hX, hY]

end Langlands.Global.ArchimedeanGL

namespace Langlands.Automorphic

open NumberField Langlands.Global ArchimedeanGL

attribute [local instance 100] LieRing.ofAssociativeRing

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

local notation "RP" => {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "CP" => {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}
local notation "RK" => Matrix.unitaryGroup (Fin n) ℝ
local notation "CK" => Matrix.unitaryGroup (Fin n) ℂ
local notation "RL" => ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ
local notation "CL" => ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ

section Compact

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- A linear map intertwining every place compact intertwines the full infinite compact. -/
theorem intertwines_infiniteCompact_of_places (f : V →ₗ[ℂ] W)
    (κ : Representation ℂ (standardInfiniteCompact F n) V)
    (κ' : Representation ℂ (standardInfiniteCompact F n) W)
    (hr : ∀ (v : RP) (k : RK) x,
      f (κ (realPlaceCompactInclusion F n v k) x) = κ' (realPlaceCompactInclusion F n v k) (f x))
    (hc : ∀ (v : CP) (k : CK) x,
      f (κ (complexPlaceCompactInclusion F n v k) x) = κ' (complexPlaceCompactInclusion F n v k) (f x)) :
    ∀ k x, f (κ k x) = κ' k (f x) := by
  let H : Submonoid (standardInfiniteCompact F n) :=
    { carrier := {k | ∀ x, f (κ k x) = κ' k (f x)}
      one_mem' := by simp
      mul_mem' := fun ha hb x => by
        rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, ha, hb] }
  let proj := (ArchimedeanCompactFactors.toStandardCompact F n).toMonoidHom
  let qr := proj.comp (MonoidHom.inl (RP → RK) (CP → CK))
  let qc := proj.comp (MonoidHom.inr (RP → RK) (CP → CK))
  intro k
  obtain ⟨p, rfl⟩ := ArchimedeanCompactFactors.toStandardCompact_surjective F n k
  have hpr : p.1 ∈ H.comap qr := by
    apply Submonoid.pi_mem_of_mulSingle_mem
    intro v
    exact hr v (p.1 v)
  have hpc : p.2 ∈ H.comap qc := by
    apply Submonoid.pi_mem_of_mulSingle_mem
    intro v
    exact hc v (p.2 v)
  have hk := H.mul_mem (show qr p.1 ∈ H from hpr) (show qc p.2 ∈ H from hpc)
  change proj (p.1, 1) * proj (1, p.2) ∈ H at hk
  rw [← map_mul] at hk
  have hp : ((p.1, 1) : ArchimedeanCompactFactors F n) * (1, p.2) = p := by
    ext <;> simp
  exact show proj p ∈ H from hp ▸ hk

end Compact

section Enveloping

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- Intertwining each included Lie generator gives equivariance for the entire
actual archimedean enveloping algebra. -/
theorem intertwines_enveloping_of_places (f : V →ₗ[ℂ] W)
    (D : EnvelopingAlgebra F n →ₐ[ℂ] Module.End ℂ V)
    (D' : EnvelopingAlgebra F n →ₐ[ℂ] Module.End ℂ W)
    (hr : ∀ (v : RP) (X : RL) x,
      f (D (envelopingGenerator F n (realPlaceComplexLieInclusion F n v X)) x) =
        D' (envelopingGenerator F n (realPlaceComplexLieInclusion F n v X)) (f x))
    (hc : ∀ (v : CP) (X : CL) x,
      f (D (envelopingGenerator F n (complexPlaceComplexLieInclusion F n v X)) x) =
        D' (envelopingGenerator F n (complexPlaceComplexLieInclusion F n v X)) (f x)) :
    ∀ U x, f (D U x) = D' U (f x) := by
  intro U
  induction U using Langlands.Archimedean.InfinitesimalCharacter.envInduction with
  | algebraMap c =>
    intro x
    simp only [AlgHom.commutes, Module.algebraMap_end_apply, map_smul]
  | ι Z =>
    intro x
    let L := (D.toLieHom.comp (envelopingGenerator F n)).toLinearMap
    let L' := (D'.toLieHom.comp (envelopingGenerator F n)).toLinearMap
    let lhs := f.comp ((LinearMap.applyₗ (R := ℂ) (M₂ := V) x).comp L)
    let rhs := (LinearMap.applyₗ (R := ℂ) (M₂ := W) (f x)).comp L'
    change lhs Z = rhs Z
    let rz (v : RP) := realPlaceComplexLieProjection F n v Z
    let cz (v : CP) := complexPlaceComplexLieProjection F n v Z
    let sumZ := (∑ v : RP, realPlaceComplexLieInclusion F n v (rz v)) +
      (∑ v : CP, complexPlaceComplexLieInclusion F n v (cz v))
    have hs : sumZ = Z := sum_placeComplexLieInclusions F n Z
    calc
      lhs Z = lhs sumZ := congrArg lhs hs.symm
      _ = rhs sumZ := by
        simp only [sumZ, map_add, map_sum]
        exact congrArg₂ (· + ·)
          (Finset.sum_congr rfl fun v _ => hr v (rz v) x)
          (Finset.sum_congr rfl fun v _ => hc v (cz v) x)
      _ = rhs Z := congrArg rhs hs
  | mul a b ha hb =>
    intro x
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, ha, hb]
  | add a b ha hb =>
    intro x
    rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, map_add, ha, hb]

end Enveloping

section FreeAction

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- Extend the finite translations, compact representation and enveloping action
as the designated generators of the common free operator algebra. -/
def freeActionOfOperators (fin : FiniteAdelicGL F n → Module.End ℂ V)
    (κ : Representation ℂ (standardInfiniteCompact F n) V)
    (D : EnvelopingAlgebra F n →ₐ[ℂ] Module.End ℂ V) :
    FreeOperatorAlgebra F n →ₐ[ℂ] Module.End ℂ V :=
  FreeAlgebra.lift ℂ (Sum.elim (Sum.elim fin κ) D)

set_option maxHeartbeats 600000 in
/-- The finite translations and the compact and Lie operators of every infinite
place suffice to check equivariance for the full common free action. -/
theorem intertwines_freeActionOfOperators_of_places (f : V →ₗ[ℂ] W)
    (fin : FiniteAdelicGL F n → Module.End ℂ V) (fin' : FiniteAdelicGL F n → Module.End ℂ W)
    (κ : Representation ℂ (standardInfiniteCompact F n) V)
    (κ' : Representation ℂ (standardInfiniteCompact F n) W)
    (D : EnvelopingAlgebra F n →ₐ[ℂ] Module.End ℂ V)
    (D' : EnvelopingAlgebra F n →ₐ[ℂ] Module.End ℂ W)
    (hf : ∀ d x, f (fin d x) = fin' d (f x))
    (hKr : ∀ (v : RP) (k : RK) x,
      f (κ (realPlaceCompactInclusion F n v k) x) = κ' (realPlaceCompactInclusion F n v k) (f x))
    (hKc : ∀ (v : CP) (k : CK) x,
      f (κ (complexPlaceCompactInclusion F n v k) x) = κ' (complexPlaceCompactInclusion F n v k) (f x))
    (hLr : ∀ (v : RP) (X : RL) x,
      f (D (envelopingGenerator F n (realPlaceComplexLieInclusion F n v X)) x) =
        D' (envelopingGenerator F n (realPlaceComplexLieInclusion F n v X)) (f x))
    (hLc : ∀ (v : CP) (X : CL) x,
      f (D (envelopingGenerator F n (complexPlaceComplexLieInclusion F n v X)) x) =
        D' (envelopingGenerator F n (complexPlaceComplexLieInclusion F n v X)) (f x)) :
    ∀ a x, f (freeActionOfOperators F n fin κ D a x) = freeActionOfOperators F n fin' κ' D' a (f x) := by
  let a := freeActionOfOperators F n fin κ D
  let b := freeActionOfOperators F n fin' κ' D'
  change ∀ t x, f (a t x) = b t (f x)
  intro t
  induction t using FreeAlgebra.induction with
  | grade0 c =>
    intro x
    simp only [AlgHom.commutes, Module.algebraMap_end_apply, map_smul]
  | grade1 i =>
    intro x
    simp only [a, b, freeActionOfOperators, FreeAlgebra.lift_ι_apply]
    rcases i with (d | k) | U
    · exact hf d x
    · exact intertwines_infiniteCompact_of_places F n f κ κ' hKr hKc k x
    · exact intertwines_enveloping_of_places F n f D D' hLr hLc U x
  | mul p q hp hq =>
    intro x
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hp, hq]
  | add p q hp hq =>
    intro x
    rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, map_add, hp, hq]

end FreeAction

end Langlands.Automorphic
