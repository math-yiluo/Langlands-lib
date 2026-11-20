import Langlands.Global.FiniteAdelicGL.BlockInducedTensorEvaluation
import Langlands.Global.FiniteAdelicGL.BlockParabolicHalfProduct
import Langlands.Representation.RestrictedTensor.BlockRegrouping
import Langlands.Representation.RestrictedTensor.FiniteTail

/-!
# The finite adelic normalized action on block coefficients

Regrouping the coefficient tensor turns the restricted tensor of normalized
local parabolic actions into the actual finite adelic half character times
the external tensor of the block actions.
-/

noncomputable section

open scoped BigOperators Classical TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 120000

universe u uV

namespace Langlands.Global.FiniteAdelicGL.BlockInducedReferences

open Langlands.GeneralLinear Langlands.RestrictedTensor CompletionPadic
open AdelicBlockDeterminantCharacter

variable {F : Type u} [Field F] [NumberField F] {n : ℕ} {B : BlockShape n}
variable {V : FinitePlace F → Fin B.length → Type uV}
variable [∀ v i, AddCommGroup (V v i)] [∀ v i, Module ℂ (V v i)]
variable {σ : ∀ (v : FinitePlace F) (i : Fin B.length),
  Representation ℂ (FiniteLocalGL F (B.size i) v) (V v i)}
variable (D : BlockInducedReferences F B σ)

local notation "P" => (AdelicBlockParabolic.Finite F B)
local notation "W" => (fun v => PiTensorProduct ℂ (V v))
local notation "τ" => (fun v => localBlockInducing F B v (σ v))
local notation "μ" => (B.leviProjection (FiniteAdeles F))

/-- The finite restricted coefficient tensor belonging to a single Levi block. -/
abbrev BlockCoefficients (i : Fin B.length) :=
  Space ℂ (fun v => V v i) D.exceptional (fun v => D.blockReference v i)

private theorem blockReference_fixed' (i : Fin B.length) (v : FinitePlace F)
    (hv : v ∉ D.exceptional) (g : FiniteLocalGL F (B.size i) v)
    (hg : g ∈ localIntegral F (B.size i) v) :
    σ v i g (D.blockReference v i) = D.blockReference v i :=
  D.blockReference_fixed v hv i ⟨g, hg⟩

/-- The actual finite adelic group of one block acts on its restricted coefficient. -/
abbrev blockRepresentation (i : Fin B.length) :
    Representation ℂ (FiniteAdelicGL F (B.size i)) (D.BlockCoefficients i) :=
  tensorRepresentation F (B.size i) (fun v => σ v i) D.exceptional
    (fun v => D.blockReference v i) (D.blockReference_fixed' i)

/-- The actual finite normalized parabolic action on the tensor grouped by blocks. -/
def normalizedLeviAction : Representation ℂ P (⨂[ℂ] i, D.BlockCoefficients i) := by
  let r : Representation ℂ (AdelicBlockParabolic.FiniteLevi F B)
      (⨂[ℂ] i, D.BlockCoefficients i) := FiniteTensor.external (fun i => D.blockRepresentation i)
  exact twist (V := ⨂[ℂ] i, D.BlockCoefficients i)
    ((parabolicHalfCharacter F B).comp (AdelicBlockParabolic.ofFinite F B)).toMonoidHom (r.comp μ)

private theorem parabolicAction_pure_of_mem (p : P) (S : Index D.exceptional)
    (hS : ∀ v ∉ S.1, localProjection F n v p.val ∈ localIntegral F n v)
    (x : ∀ v : S.1, W v) :
    D.parabolicAction p (pure D.exceptional D.coefficientReference S x) =
      pure D.exceptional D.coefficientReference S (fun v =>
        τ v (localParabolicProjection F B v p) (x v)) := by
  unfold parabolicAction
  rw [MonoidHom.comp_apply]
  exact representation_pure_of_mem _ τ D.exceptional D.coefficientReference _ _ S hS x

private theorem localBlockInducing_tprod (p : P) (v : FinitePlace F) (x : ∀ i, V v i) :
    τ v (localParabolicProjection F B v p) (PiTensorProduct.tprod ℂ x) =
      ((padicField v).canonicalTopologicalData.parabolicHalfModulus B
        (localParabolicProjection F B v p) : ℂ) •
        PiTensorProduct.tprod ℂ (fun i =>
          σ v i (localProjection F (B.size i) v (μ p i)) (x i)) := by
  change (_ : ℂ) • B.blockTensor (σ v)
    (B.leviProjection (FiniteCompletion F v) (localParabolicProjection F B v p))
    (PiTensorProduct.tprod ℂ x) = _
  rw [B.blockTensor_tprod]
  congr 1

private theorem pure_smul_family (S : Index D.exceptional)
    (c : S.1 → ℂ) (x : ∀ v : S.1, W v) :
    pure (K := ℂ) D.exceptional D.coefficientReference S (fun v => c v • x v) =
      (∏ v : S.1, c v) • pure (K := ℂ) D.exceptional D.coefficientReference S x := by
  unfold RestrictedTensor.pure
  rw [(PiTensorProduct.tprod ℂ).map_smul_univ, map_smul]

private theorem blockRegroup_parabolic_pure (p : P) (S : Index D.exceptional)
    (hS : ∀ v ∉ S.1, localProjection F n v p.val ∈ localIntegral F n v)
    (x : ∀ (v : S.1) i, V v i) :
    blockRegroup ℂ D.exceptional D.blockReference
        (D.parabolicAction p (pure D.exceptional D.coefficientReference S
          (fun v => PiTensorProduct.tprod ℂ (x v)))) =
      D.normalizedLeviAction p (blockRegroup ℂ D.exceptional D.blockReference
        (pure D.exceptional D.coefficientReference S (fun v => PiTensorProduct.tprod ℂ (x v)))) := by
  let d (v : FinitePlace F) := (padicField v).canonicalTopologicalData.parabolicHalfModulus B
    (localParabolicProjection F B v p)
  let y (v : S.1) (i : Fin B.length) :=
    σ v i (localProjection F (B.size i) v (μ p i)) (x v i)
  let u : ⨂[ℂ] i, D.BlockCoefficients i := PiTensorProduct.tprod ℂ
    (fun i => pure (K := ℂ) D.exceptional (fun v => D.blockReference v i) S (fun v => y v i))
  have hf : (fun v : S.1 => τ v (localParabolicProjection F B v p)
      (PiTensorProduct.tprod ℂ (x v))) =
      (fun v : S.1 => (d v : ℂ) • PiTensorProduct.tprod ℂ (y v)) :=
    funext fun v => localBlockInducing_tprod p v (x v)
  have hlevi (i : Fin B.length) (v : FinitePlace F) (hv : v ∉ S.1) :
      localProjection F (B.size i) v (μ p i) ∈ localIntegral F (B.size i) v := by
    rw [localProjection_leviProjection]
    exact localLeviProjection_mem_integral F B v (localParabolicProjection F B v p) (hS v hv) i
  rw [D.parabolicAction_pure_of_mem p S hS, hf, D.pure_smul_family, map_smul]
  change (∏ v : S.1, (d v : ℂ)) • blockRegroup ℂ D.exceptional D.blockReference
      (pure D.exceptional (fun v => PiTensorProduct.tprod ℂ (D.blockReference v)) S
        (fun v => PiTensorProduct.tprod ℂ (y v))) =
    (parabolicHalfCharacter F B (AdelicBlockParabolic.ofFinite F B p) : ℂ) •
      FiniteTensor.external D.blockRepresentation (μ p)
        (blockRegroup ℂ D.exceptional D.blockReference
          (pure D.exceptional (fun v => PiTensorProduct.tprod ℂ (D.blockReference v)) S
            (fun v => PiTensorProduct.tprod ℂ (x v))))
  rw [blockRegroup_pure, blockRegroup_pure, FiniteTensor.external_tprod]
  have hblock (i : Fin B.length) :
      D.blockRepresentation i (μ p i)
        (pure (K := ℂ) D.exceptional (fun v => D.blockReference v i) S (fun v => x v i)) =
      pure (K := ℂ) D.exceptional (fun v => D.blockReference v i) S (fun v => y v i) :=
    tensorRepresentation_pure_of_mem F (B.size i) (fun v => σ v i) D.exceptional
      (fun v => D.blockReference v i) (D.blockReference_fixed' i) _ S (hlevi i) _
  simp only [hblock]
  change (∏ v : S.1, (d v : ℂ)) • u =
    (parabolicHalfCharacter F B (AdelicBlockParabolic.ofFinite F B p) : ℂ) • u
  rw [parabolicHalfCharacter_ofFinite_eq_prod F B S.1 p hS, Units.coe_prod]
  exact congrArg (fun z : ℂ => z • u) (Finset.prod_attach S.1 (fun v => (d v : ℂ)))

/-- Regrouping intertwines the actual normalized finite adelic parabolic actions. -/
theorem blockRegroup_parabolicAction (p : P) :
    (blockRegroup ℂ D.exceptional D.blockReference).comp (D.parabolicAction p) =
      (D.normalizedLeviAction p).comp (blockRegroup ℂ D.exceptional D.blockReference) := by
  obtain ⟨S, _, hS⟩ := exists_finset_reference_outside
    (fun v => (localIntegral F n v).toSubgroup) D.exceptional
    (restrictedProductEquiv F n p.val)
  let L := (blockRegroup ℂ D.exceptional D.blockReference).comp (D.parabolicAction p)
  let R := (D.normalizedLeviAction p).comp (blockRegroup ℂ D.exceptional D.blockReference)
  change L = R
  refine hom_ext_cofinal (K := ℂ) (V := W) (E := D.exceptional) (e := D.coefficientReference)
    (Y := ⨂[ℂ] i, D.BlockCoefficients i) (f := L) (g := R) S ?_
  intro T hST v
  let inc := of ℂ W D.exceptional D.coefficientReference T
  have h : L.comp inc = R.comp inc := by
    refine FiniteTensor.nested_ext ℂ (fun v : T.1 => V v) (f := L.comp inc) (g := R.comp inc) ?_
    intro x
    exact D.blockRegroup_parabolic_pure p T (fun v hv => hS v (fun h => hv (hST h))) x
  exact LinearMap.congr_fun h (PiTensorProduct.tprod ℂ v)

/-- The coefficient regrouping is an equivalence for the precise adelic half
character and the genuine finite adelic block actions. -/
def parabolicCoefficientEquiv
    (hD : ∀ v ∉ D.exceptional, ∀ i, D.blockReference v i ≠ 0) :
    D.parabolicAction.Equiv D.normalizedLeviAction :=
  Representation.Equiv.mk (blockRegroupEquiv ℂ D.exceptional D.blockReference hD)
    D.blockRegroup_parabolicAction

end Langlands.Global.FiniteAdelicGL.BlockInducedReferences
