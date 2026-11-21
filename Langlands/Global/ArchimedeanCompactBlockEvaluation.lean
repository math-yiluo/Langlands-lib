import Langlands.Global.AdelicBlockCoefficientTensor
import Langlands.Representation.Archimedean.RealLeviProducts

/-! # Tensor evaluation on an archimedean compact block product -/

noncomputable section

open scoped TensorProduct

set_option autoImplicit false

namespace Langlands.Global.ArchimedeanCompactBlocks

open AdelicBlockScalarSections (indexedEvaluation indexedEvaluation_injective
  indexedEvaluation_map_apply indexedEvaluation_tprod)
open Archimedean.RealLeviProducts (mem_prodSpan prodSpan)

universe uK uJ uW uV

variable {c : ℕ} {K : Type uK} [Group K]
  {J : Fin c → Type uJ} [∀ i, Group (J i)]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {V : Fin c → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

variable (j : (∀ i, J i) →* K) (ρ : Representation ℂ K W)
  (ℓ : W →ₗ[ℂ] ℂ) (e : ∀ i, V i →ₗ[ℂ] (J i → ℂ)) (s : ∀ i, W →ₗ[ℂ] V i)
  (hs : ∀ i x w, e i (s i w) x = ℓ (ρ (j (Pi.mulSingle i x)) w))

private def orbitEvaluation (k : K) : W →ₗ[ℂ] ((∀ i, J i) → ℂ) :=
  LinearMap.pi fun q => ℓ.comp (ρ (j q * k))

private theorem update_eq_mulSingle_mul (q : ∀ i, J i) (i : Fin c) (x : J i) :
    Function.update q i x = Pi.mulSingle i x * Function.update q i 1 := by
  ext a
  by_cases h : a = i
  · subst a
    simp
  · simp [h]

include hs in
private theorem orbitEvaluation_mem_range (hf : ∀ w, FiniteVectors.IsFiniteVector ρ w)
    (k : K) (w : W) : orbitEvaluation j ρ ℓ k w ∈ LinearMap.range (indexedEvaluation e) := by
  let O := FiniteVectors.orbitSpan ρ w
  have : FiniteDimensional ℂ O := hf w
  let M (i : Fin c) := O.map ((e i).comp (s i))
  let (i : Fin c) : FiniteDimensional ℂ (M i) := by
    dsimp [M]
    infer_instance
  let f := orbitEvaluation j ρ ℓ k w
  have hm : f ∈ prodSpan M := mem_prodSpan M f fun q i => by
    refine ⟨ρ (j (Function.update q i 1) * k) w,
      FiniteVectors.action_mem_orbitSpan ρ _ _, ?_⟩
    funext x
    change e i (s i (ρ (j (Function.update q i 1) * k) w)) x =
      ℓ (ρ (j (Function.update q i x) * k) w)
    have hmul : j (Function.update q i x) * k =
        j (Pi.mulSingle i x) * (j (Function.update q i 1) * k) := by
      rw [update_eq_mulSingle_mul q i x, map_mul j, mul_assoc]
    rw [hs, hmul, map_mul ρ (j (Pi.mulSingle i x)), Module.End.mul_apply]
  refine (Submodule.span_le.mpr ?_ : prodSpan M ≤ _) hm
  rintro f' ⟨g, hg, rfl⟩
  have hpre : ∀ i, ∃ v : V i, e i v = g i := by
    intro i
    obtain ⟨p, _, hp⟩ := Submodule.mem_map.mp (hg i)
    exact ⟨s i p, hp⟩
  choose v hv using hpre
  refine ⟨PiTensorProduct.tprod ℂ v, ?_⟩
  funext q
  simp only [indexedEvaluation_tprod, hv]

variable (he : ∀ i, Function.Injective (e i))
  (hf : ∀ w, FiniteVectors.IsFiniteVector ρ w)

/-- Evaluate a compact translate as a tensor of block vectors. Each partial
evaluation comes from the finite-dimensional compact orbit of the vector. -/
def evaluation (k : K) : W →ₗ[ℂ] (⨂[ℂ] i, V i) :=
  (LinearEquiv.ofInjective _ (indexedEvaluation_injective e he)).symm.toLinearMap.comp
    ((orbitEvaluation j ρ ℓ k).codRestrict _ (orbitEvaluation_mem_range j ρ ℓ e s hs hf k))

/-- Scalar evaluation of the block tensor recovers the original compact value. -/
theorem evaluation_value (k : K) (w : W) (q : ∀ i, J i) :
    indexedEvaluation e (evaluation j ρ ℓ e s hs he hf k w) q =
      ℓ (ρ (j q * k) w) := by
  let a := LinearEquiv.ofInjective _ (indexedEvaluation_injective e he)
  let b : LinearMap.range (indexedEvaluation e) :=
    ⟨orbitEvaluation j ρ ℓ k w, orbitEvaluation_mem_range j ρ ℓ e s hs hf k w⟩
  exact congrArg (fun x : LinearMap.range (indexedEvaluation e) => x.val q) (a.apply_symm_apply b)

/-- Right compact translation is right multiplication on the evaluation argument. -/
theorem evaluation_right (k d : K) (w : W) :
    evaluation j ρ ℓ e s hs he hf k (ρ d w) = evaluation j ρ ℓ e s hs he hf (k * d) w := by
  apply indexedEvaluation_injective e he
  funext q
  rw [evaluation_value, evaluation_value, ← Module.End.mul_apply, ← map_mul, mul_assoc]

/-- Left translation by a block compact element acts on the corresponding coefficients. -/
theorem evaluation_left (σ : ∀ i, Representation ℂ (J i) (V i))
    (hσ : ∀ i (p q : J i) v, e i (σ i p v) q = e i v (q * p))
    (k : K) (p : ∀ i, J i) (w : W) :
    evaluation j ρ ℓ e s hs he hf (j p * k) w =
      PiTensorProduct.map (fun i => σ i (p i)) (evaluation j ρ ℓ e s hs he hf k w) := by
  apply indexedEvaluation_injective e he
  funext q
  rw [indexedEvaluation_map_apply e (fun i => σ i (p i)) (fun i x => x * p i)
    (fun i v x => hσ i (p i) x v), evaluation_value, evaluation_value]
  change ℓ (ρ (j q * (j p * k)) w) = ℓ (ρ (j (q * p) * k) w)
  rw [map_mul j q p, mul_assoc]

/-- A scalar compact coefficient that detects vectors makes its tensor
evaluations jointly injective. -/
theorem evaluation_separates
    (hℓ : ∀ w, (∀ k, ℓ (ρ k w) = 0) → w = 0)
    (w : W) (hw : ∀ k, evaluation j ρ ℓ e s hs he hf k w = 0) : w = 0 := by
  apply hℓ
  intro k
  have h := evaluation_value j ρ ℓ e s hs he hf k w 1
  simpa only [hw, map_zero, Pi.zero_apply, map_one, one_mul] using h.symm

end Langlands.Global.ArchimedeanCompactBlocks
