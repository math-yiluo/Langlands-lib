import Langlands.Global.Factors.CuspidalBlockPlaceCoefficients
import Langlands.Global.Factors.CuspidalBlockInfiniteEvaluationLeft

/-! # Compact translation in the actual tensor of one Levi block -/

noncomputable section

open scoped Classical TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 120000
set_option synthInstance.maxHeartbeats 58000

universe u uQ v w x

namespace Langlands.Global.CuspidalBlockInduction

open Automorphic FiniteAdelicGL AdelicBlockParabolic InfinitePlaceFamily
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents)

private theorem product_compact_covariance {I : Type v} [Finite I] [DecidableEq I]
    {G : I → Type w} [∀ i, Group (G i)] {V : I → Type x}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    {U : Type u} [AddCommGroup U] [Module ℂ U]
    (ρ : ∀ i, Representation ℂ (G i) (V i)) (κ : Representation ℂ (∀ i, G i) U)
    (L : (⨂[ℂ] i, V i) →ₗ[ℂ] U)
    (hL : ∀ i (g : G i) (b : ∀ j, V j),
      L (PiTensorProduct.tprod ℂ (fun j => ρ j (Pi.mulSingle i g j) (b j))) =
        κ (Pi.mulSingle i g) (L (PiTensorProduct.tprod ℂ b)))
    (d : ∀ i, G i) (b : ∀ i, V i) :
    L (PiTensorProduct.tprod ℂ (fun j => ρ j (d j) (b j))) =
      κ d (L (PiTensorProduct.tprod ℂ b)) := by
  let H : Submonoid (∀ i, G i) :=
    { carrier := {d | ∀ b : ∀ i, V i,
        L (PiTensorProduct.tprod ℂ (fun j => ρ j (d j) (b j))) =
          κ d (L (PiTensorProduct.tprod ℂ b))}
      one_mem' := by
        intro b
        simp only [Pi.one_apply, map_one, Module.End.one_apply]
      mul_mem' := by
        intro a c ha hc b
        change L (PiTensorProduct.tprod ℂ (fun j => ρ j (a j * c j) (b j))) =
          κ (a * c) (L (PiTensorProduct.tprod ℂ b))
        simp only [map_mul, Module.End.mul_apply]
        exact (ha (fun j => ρ j (c j) (b j))).trans (congrArg (κ a) (hc b)) }
  have hd : d ∈ H := Submonoid.pi_mem_of_mulSingle_mem d fun i => hL i (d i)
  exact hd b

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
variable {r k : ℕ} {m : Fin k → ℕ} (hm : ∑ i, (m i + 1) = r + 1)
variable {T : ∀ i, CuspidalOperatorRealization F (m i)}
variable (P : ∀ i, CuspidalSpectralPresentation.{u, uQ} (T i))
variable (h : ∀ i, HasIrreducibleAdmissibleComponents (P i))

local notation "B" => blockShape hm
local notation "D" => finiteReferences hm P
local notation "S" => (fun i : Fin k => CuspidalOperatorRealization.realization (T i))
local notation "CF" => (fun i : Fin k => BlockInducedReferences.BlockCoefficients D i)
local notation "CI" => (fun (p : Index F) (i : Fin k) => InfiniteBlockCoefficient T i p)

private local instance (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
private local instance (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
private local instance (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
private local instance (n : ℕ) : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
private local instance (n : ℕ) : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
private local instance {n : ℕ} (R : OperatorRealization F n) : AddCommGroup R.Space := Submodule.addCommGroup _
private local instance {n : ℕ} {v : FinitePlace F} (R : LocalRealization F n v) : AddCommGroup R.Space :=
  Submodule.addCommGroup _
private local instance (i : Fin k) (p : Index F) : AddCommGroup (CI p i) := Submodule.addCommGroup _

private theorem blockVectorEquiv_placeCompact (i : Fin k) (p : Index F)
    (d : Compact (m i + 1) p) (a : CF i) (b c : ∀ q, CI q i)
    (hother : ∀ q, q ≠ p → c q = b q)
    (hlocal : c p = (T i).placeDensityModels.sourceCompact p d (b p)) :
    blockVectorEquiv hm P h i (a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ c) =
      (S i).placeCompactFamily p d
        (blockVectorEquiv hm P h i (a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ b)) := by
  let e := (blockTensorPresentationEquiv hm P i).toLinearEquiv
  let Q := (P i).allPlaceTensorEquiv (h i)
  have he (t : ⨂[ℂ] q, CI q i) : blockVectorEquiv hm P h i (a ⊗ₜ[ℂ] t) =
      Q (e a ⊗ₜ[ℂ] t) :=
    congrArg Q (TensorProduct.congr_tmul e (LinearEquiv.refl ℂ _) a t)
  exact (he _).trans (((P i).allPlaceTensorEquiv_compact (h i) p d (e a) b c hother hlocal).trans
    (congrArg ((S i).placeCompactFamily p d) (he _).symm))

/-- Compact translation on the infinite factors of a single block, transported
from the actual matrix-unitary actions at all its places. -/
def blockInfiniteCompactAction (i : Fin k) :
    Representation ℂ (standardInfiniteCompact F (m i + 1)) (⨂[ℂ] p, CI p i) :=
  (FiniteTensor.external (T i).placeDensityModels.sourceCompact).comp
    (infiniteCompactCoordinates F (m i + 1)).toMonoidHom

theorem blockVectorEquiv_compact_tprod (i : Fin k) (d : standardInfiniteCompact F (m i + 1))
    (a : CF i) (b : ∀ q, CI q i) :
    blockVectorEquiv hm P h i (a ⊗ₜ[ℂ]
      PiTensorProduct.tprod ℂ (fun q => (T i).placeDensityModels.sourceCompact q
        (infiniteCompactCoordinates F (m i + 1) d q) (b q))) =
      (S i).compactRepresentation d (blockVectorEquiv hm P h i (a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ b)) := by
  let g := infiniteCompactCoordinates F (m i + 1)
  let ρ := (T i).placeDensityModels.sourceCompact
  let κ := (S i).compactRepresentation.comp g.symm.toMonoidHom
  let L := (blockVectorEquiv hm P h i).toLinearMap.comp
    ((TensorProduct.mk ℂ (CF i) (⨂[ℂ] q, CI q i)) a)
  have hL (p : Index F) (z : Compact (m i + 1) p) (f : ∀ q, CI q i) :
      L (PiTensorProduct.tprod ℂ (fun q => ρ q (Pi.mulSingle p z q) (f q))) =
        κ (Pi.mulSingle p z) (L (PiTensorProduct.tprod ℂ f)) := by
    let c (q : Index F) := ρ q (Pi.mulSingle p z q) (f q)
    have hother (q : Index F) (hq : q ≠ p) : c q = f q := by
      simp only [c, Pi.mulSingle_eq_of_ne hq, map_one, Module.End.one_apply]
    have hlocal : c p = ρ p z (f p) := by simp only [c, Pi.mulSingle_eq_same]
    have h₁ := blockVectorEquiv_placeCompact hm P h i p z a f c hother hlocal
    have hg : g.symm (Pi.mulSingle p z) = compactInclusion (m i + 1) p z :=
      g.symm_apply_eq.mpr (infiniteCompactCoordinates_inclusion p z).symm
    exact h₁.trans (congrArg (fun d => (S i).compactRepresentation d
      (L (PiTensorProduct.tprod ℂ f))) hg.symm)
  have h₂ := product_compact_covariance ρ κ L hL (g d) b
  exact h₂.trans (congrArg (fun x => (S i).compactRepresentation x
    (L (PiTensorProduct.tprod ℂ b))) (g.symm_apply_apply d))

theorem blockVectorEquiv_compact (i : Fin k) (d : standardInfiniteCompact F (m i + 1))
    (a : CF i) (b : ⨂[ℂ] q, CI q i) :
    blockVectorEquiv hm P h i (a ⊗ₜ[ℂ] blockInfiniteCompactAction (T := T) i d b) =
      (S i).compactRepresentation d (blockVectorEquiv hm P h i (a ⊗ₜ[ℂ] b)) := by
  let L := (blockVectorEquiv hm P h i).toLinearMap.comp
    ((TensorProduct.mk ℂ (CF i) (⨂[ℂ] q, CI q i)) a)
  have he : L.comp (blockInfiniteCompactAction (T := T) i d) = ((S i).compactRepresentation d).comp L := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro f
    exact (congrArg L (FiniteTensor.external_tprod (T i).placeDensityModels.sourceCompact
      (infiniteCompactCoordinates F (m i + 1) d) f)).trans
      (blockVectorEquiv_compact_tprod hm P h i d a f)
  exact LinearMap.congr_fun he b

end Langlands.Global.CuspidalBlockInduction
