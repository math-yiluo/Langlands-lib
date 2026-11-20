import Langlands.Representation.Archimedean.ComplexJacquetBimoduleBridge
import Langlands.Representation.Archimedean.UpperVermaCharacter
import Langlands.Representation.Archimedean.ComplexPrincipalSeriesInfinitesimalCharacter
import Langlands.Representation.Archimedean.ComplexStandardNontrivialProof
import Langlands.Representation.Archimedean.ComplexSwapJacquetFunctional
import Langlands.Representation.Archimedean.ComplexSwapJacquetLie

/-!
# Central character of the complex standard module

See the paired Markdown.
-/

noncomputable section

open scoped TensorProduct Manifold Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

namespace VermaShifted

open VermaGL VermaPBW VermaCentral Kostant

variable (n : ℕ)

private theorem diag_of_lower_weight_zero (l : List (Idx n))
    (hl : ∀ c ∈ l, c.2 ≤ c.1)
    (hw : (l.map fun c => dZero n c.1 - dZero n c.2).sum = 0) :
    ∀ c ∈ l, c.1 = c.2 := by
  let distance : Idx n → ℕ := fun c => c.1.val - c.2.val
  have hsum : (l.map fun c => dZero n c.1 - dZero n c.2).sum =
      -((l.map distance).sum : ℂ) := by
    rw [Nat.cast_list_sum, List.sum_neg, List.map_map, List.map_map]
    congr 1
    refine List.map_congr_left fun c hc => ?_
    simp only [dZero, Function.comp_apply, distance, Nat.cast_sub (hl c hc)]
    ring
  rw [hsum, neg_eq_zero, Nat.cast_eq_zero] at hw
  intro c hc
  have hcast : (Multiset.map distance (l : Multiset (Idx n))).sum = 0 := hw
  have hzero := Multiset.sum_eq_zero_iff.mp hcast (distance c) (Multiset.mem_map.mpr ⟨c, hc, rfl⟩)
  exact Fin.ext (le_antisymm (Nat.sub_eq_zero_iff_le.mp hzero) (hl c hc))

/-- A functional killed on the left by the upper units evaluates the center by the
lower Verma polynomial at its diagonal weight. -/
theorem character_apply_functional (lam : Fin n → ℂ) {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A : glU n →ₐ[ℂ] Module.End ℂ V) (L : V →ₗ[ℂ] ℂ)
    (hu : ∀ p q : Fin n, p < q → ∀ v, L (A (unitU n p q) v) = 0)
    (hd : ∀ p : Fin n, ∀ v, L (A (unitU n p p) v) = lam p * L v)
    (z : VermaGL.center n) (v : V) :
    L (A z v) = character n lam z * L v := by
  let ev : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ := MvPolynomial.aeval lam
  have hDiag : ∀ (l : List (Idx n)), (∀ c ∈ l, c.1 = c.2) →
      L (A (W n l) v) = ev ((l.map (Xd n)).prod) * L v := by
    intro l
    induction l with
    | nil => simp [W_nil, Module.End.one_apply]
    | cons c l ih =>
        intro hl
        obtain ⟨p, q⟩ := c
        have hpq : p = q := hl (p, q) (List.mem_cons_self)
        subst q
        have htail := ih fun d hd => hl d (List.mem_cons_of_mem _ hd)
        rw [W_cons, map_mul, Module.End.mul_apply]
        change L (A (unitU n p p) (A (W n l) v)) = _
        rw [hd, htail, List.map_cons, List.prod_cons, map_mul, Xd, ite_eq_left rfl, mul_assoc]
        simp [ev]
  let F : glU n →ₗ[ℂ] ℂ := L.comp ((LinearMap.applyₗ (R := ℂ) v).comp A.toLinearMap)
  let G : glU n →ₗ[ℂ] ℂ := L v • ev.toLinearMap.comp (gam n)
  have heq : ∀ α ∈ ((basisU n).repr (z : glU n)).support, F (basisU n α) = G (basisU n α) := by
    intro α hα
    have hz := repr_hD_comm n (z : glU n) α
    rw [Subalgebra.mem_center_iff.mp z.2 (hD n), sub_self, map_zero, Finsupp.zero_apply] at hz
    have hw : sWt n α = 0 :=
      (mul_eq_zero.mp hz.symm).resolve_right (Finsupp.mem_support_iff.mp hα)
    change L (A (basisU n α) v) = L v * ev (gam n (basisU n α))
    rw [mul_comm (L v), gam_basisU, basisU_apply]
    rw [sWt, bsList, expand_append] at hw
    rw [bsList, expand_append]
    cases hup : expand ((upList n).map Subtype.val) α with
    | nil =>
        simp only [hup, List.nil_append] at hw
        simp only [List.nil_append]
        refine hDiag _ (diag_of_lower_weight_zero n _ (fun c hc => ?_) hw)
        obtain ⟨d, _, rfl⟩ := List.mem_map.mp (mem_expand hc)
        exact le_of_not_gt d.2
    | cons c l =>
        have hc : c ∈ expand ((upList n).map Subtype.val) α := by
          rw [hup]
          exact List.mem_cons_self
        obtain ⟨d, _, rfl⟩ := List.mem_map.mp (mem_expand hc)
        rw [List.cons_append, W_cons, map_mul, Module.End.mul_apply]
        change L (A (unitU n d.val.1 d.val.2) _) = _
        rw [hu _ _ d.2, List.map_cons, List.prod_cons, Xd, ite_eq_right d.2.ne, zero_mul, map_zero,
          zero_mul]
  have hker : (z : glU n) ∈ LinearMap.ker (F - G) := by
    refine Submodule.span_le.mpr ?_ ((basisU n).mem_span_repr_support (z : glU n))
    rintro _ ⟨α, hα, rfl⟩
    change basisU n α ∈ LinearMap.ker (F - G)
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    exact heq α hα
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hker
  simpa [F, G, ev, character_apply, MvPolynomial.aeval_eq_eval, mul_comm] using hker

end VermaShifted

namespace ComplexStandardCentralCharacter

open Langlands.LocalFactor.Archimedean Langlands.Automorphic.ComplexPlaceParameter
open ComplexGenericLarge ComplexSwapJacquet InfinitesimalCharacter VermaGL
open Langlands.Algebra.UniversalEnveloping

variable (n : ℕ)

local notation "CM" => Matrix (Fin n) (Fin n) ℂ

/-- The matrix Lie algebra in block `k` of the local complexified Lie algebra. -/
def blockLie (k : Fin 2) :
    Matrix (Fin n) (Fin n) ℂ →ₗ⁅ℂ⁆ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) :=
  tensorLieEquiv.symm.toLieHom.comp (Langlands.Archimedean.ComplexJacquetBimoduleBridge.factorHom (n := n) k)

theorem blockLie_apply (k : Fin 2) (X : Matrix (Fin n) (Fin n) ℂ) :
    blockLie n k X = tensorLieEquiv.symm (Pi.single k X) :=
  rfl

/-- The local enveloping-algebra map induced by inclusion of block `k`. -/
def blockEnveloping (k : Fin 2) :
    glU n →ₐ[ℂ] UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) :=
  UniversalEnvelopingAlgebra.lift ℂ ((UniversalEnvelopingAlgebra.ι ℂ).comp (blockLie n k))

theorem blockEnveloping_ι (k : Fin 2) (X : Matrix (Fin n) (Fin n) ℂ) :
    blockEnveloping n k (UniversalEnvelopingAlgebra.ι ℂ X) =
      UniversalEnvelopingAlgebra.ι ℂ (blockLie n k X) :=
  UniversalEnvelopingAlgebra.lift_ι_apply ℂ _ _

private theorem commute_blockEnveloping (k : Fin 2)
    (Y : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ)
    (hY : ∀ X : Matrix (Fin n) (Fin n) ℂ, ⁅Y, blockLie n k X⁆ = 0) (u : glU n) :
    Commute (UniversalEnvelopingAlgebra.ι ℂ Y) (blockEnveloping n k u) := by
  obtain ⟨d, hd⟩ := exists_mem_degreeFiltration ℂ _ u
  have hu := Kostant.degreeFiltration_le_wordSpan ℂ _ d hd
  clear hd
  induction hu using Submodule.span_induction with
  | mem u hu =>
      obtain ⟨l, -, rfl⟩ := hu
      induction l with
      | nil => simp [word_nil]
      | cons X l ih =>
          rw [word_cons, map_mul, blockEnveloping_ι]
          refine Commute.mul_right ?_ ih
          have h := congrArg (UniversalEnvelopingAlgebra.ι ℂ) (hY X)
          rw [LieHom.map_lie, map_zero, LieRing.of_associative_ring_bracket, sub_eq_zero] at h
          exact h
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact ha.add_right hb
  | smul c a _ ha => rw [map_smul]; exact ha.smul_right c

/-- Each block center maps into the center of the actual local enveloping algebra. -/
theorem blockEnveloping_mem_center (k : Fin 2) (z : VermaGL.center n) :
    blockEnveloping n k (z : glU n) ∈
      Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ)) := by
  refine Kostant.mem_center_of_commute ℂ _ fun Y => ?_
  let X := tensorLieEquiv Y k
  let T := Y - blockLie n k X
  have hT : ∀ A : Matrix (Fin n) (Fin n) ℂ, ⁅T, blockLie n k A⁆ = 0 := by
    intro A
    apply tensorLieEquiv.injective
    change tensorLieEquiv ⁅T, blockLie n k A⁆ = tensorLieEquiv 0
    rw [LieEquiv.map_lie, map_zero, blockLie_apply, LieEquiv.apply_symm_apply]
    have h : tensorLieEquiv T = tensorLieEquiv Y - Pi.single k X := by
      simp [T, blockLie_apply]
    rw [h]
    funext j
    change ⁅tensorLieEquiv Y j - (Pi.single k X : Fin 2 → CM) j,
      (Pi.single k A : Fin 2 → CM) j⁆ = 0
    by_cases hj : j = k
    · subst j
      simp [X]
    · simp [Pi.single_eq_of_ne hj]
  have h₁ : Commute (UniversalEnvelopingAlgebra.ι ℂ (blockLie n k X))
      (blockEnveloping n k (z : glU n)) := by
    rw [← blockEnveloping_ι]
    exact (show Commute (UniversalEnvelopingAlgebra.ι ℂ X) (z : glU n) from
      Subalgebra.mem_center_iff.mp z.2 _).map (blockEnveloping n k)
  have h₂ := commute_blockEnveloping n k T hT (z : glU n)
  have hY : Y = blockLie n k X + T := by simp [T]
  rw [hY, map_add]
  exact h₁.add_left h₂

private def orientation (k : Fin 2) : ℂ := if k = 0 then -Complex.I else Complex.I

private theorem blockLie_matrixUnit (k : Fin 2) (p q : Fin n) :
    blockLie n k (Matrix.single p q 1) =
      (1 / 2 : ℂ) • ((1 : ℂ) ⊗ₜ[ℝ] Matrix.single p q 1 +
        orientation k • ((1 : ℂ) ⊗ₜ[ℝ] (Complex.I • Matrix.single p q 1))) := by
  have hconj : conjMat (Matrix.single p q (1 : ℂ)) = Matrix.single p q 1 := by
    ext i j
    simp [Matrix.single_apply, apply_ite]
  rw [blockLie_apply, tensorLieEquiv_symm_apply, tensorEquiv_symm_apply, tensorInv]
  fin_cases k
  · simp [orientation, sub_eq_add_neg]
  · simp [orientation, hconj]

private abbrev evalOne (ds : List ComplexCharacterData) : KFs n ds →ₗ[ℂ] ℂ :=
  kFiniteEval (complexStandardModule n ds) 1

private theorem eval_blockLie_matrixUnit (ds : List ComplexCharacterData) (k : Fin 2)
    (p q : Fin n) (v : KFs n ds) :
    evalOne n ds (complexStandardLie n ds (blockLie n k (Matrix.single p q 1)) v) =
      (1 / 2 : ℂ) *
        (rightDerivative (matrixModel ℂ n) (Matrix.single p q 1)
          (v : Langlands.GeneralLinear n ℂ → ℂ) 1 +
        orientation k * rightDerivative (matrixModel ℂ n) (Matrix.single p q Complex.I)
          (v : Langlands.GeneralLinear n ℂ → ℂ) 1) := by
  rw [blockLie_matrixUnit, Matrix.smul_single, smul_eq_mul, mul_one]
  simp only [map_smul, map_add, LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul,
    kFiniteEval_apply, coe_lie]

private def blockExponent (ds : List ComplexCharacterData) (hlen : ds.length = n)
    (k : Fin 2) (p : Fin n) : ℂ :=
  let d := ds.get (Fin.cast hlen.symm p)
  if k = 0 then d.zExponent else d.zBarExponent

private theorem ofFn_blockExponent (ds : List ComplexCharacterData) (hlen : ds.length = n)
    (k : Fin 2) :
    List.ofFn (blockExponent n ds hlen k) =
      ds.map (if k = 0 then ComplexCharacterData.zExponent else ComplexCharacterData.zBarExponent) := by
  subst n
  rw [← List.ofFn_getElem_eq_map]
  apply congrArg List.ofFn
  funext i
  by_cases h : k = 0 <;> simp [blockExponent, h]

private abbrev blockAction (ds : List ComplexCharacterData) (k : Fin 2) :
    glU n →ₐ[ℂ] Module.End ℂ (KFs n ds) :=
  (envelopingAction (complexStandardLie n ds)).comp (blockEnveloping n k)

private theorem eval_blockAction_unitU (ds : List ComplexCharacterData) (k : Fin 2)
    (p q : Fin n) (v : KFs n ds) :
    evalOne n ds (blockAction n ds k (unitU n p q) v) =
      (1 / 2 : ℂ) *
        (rightDerivative (matrixModel ℂ n) (Matrix.single p q 1)
          (v : Langlands.GeneralLinear n ℂ → ℂ) 1 +
        orientation k * rightDerivative (matrixModel ℂ n) (Matrix.single p q Complex.I)
          (v : Langlands.GeneralLinear n ℂ → ℂ) 1) := by
  rw [AlgHom.comp_apply, blockEnveloping_ι, UniversalEnvelopingAlgebra.lift_ι_apply]
  exact eval_blockLie_matrixUnit n ds k p q v

private theorem eval_strictUpper (ds : List ComplexCharacterData) (k : Fin 2)
    (p q : Fin n) (hpq : p < q) (v : KFs n ds) :
    evalOne n ds (blockAction n ds k (unitU n p q) v) = 0 := by
  have hstrict (c : ℂ) (a b : Fin n) (hba : b ≤ a) : Matrix.single p q c a b = 0 := by
    rw [Matrix.single_apply]
    split
    · rename_i h
      obtain ⟨rfl, rfl⟩ := h
      exact (not_le_of_gt hpq hba).elim
    · rfl
  rw [eval_blockAction_unitU, rightDerivative_one_strictUpper (mem_of_mem_kFs v.2) _ (hstrict 1),
    rightDerivative_one_strictUpper (mem_of_mem_kFs v.2) _ (hstrict Complex.I)]
  ring

private theorem eval_diagonal (ds : List ComplexCharacterData) (hlen : ds.length = n) (k : Fin 2)
    (p : Fin n) (v : KFs n ds) :
    evalOne n ds (blockAction n ds k (unitU n p p) v) =
      (blockExponent n ds hlen k p + rho n p) * evalOne n ds v := by
  rw [eval_blockAction_unitU, rightDerivative_one_diag hlen (mem_of_mem_kFs v.2),
    rightDerivative_one_diag hlen (mem_of_mem_kFs v.2), kappa_one, kappa_I]
  let d := ds.get (Fin.cast hlen.symm p)
  let y := evalOne n ds v
  change (1 / 2 : ℂ) * ((2 * d.exponent + ((n : ℂ) - 1) - 2 * (p.val : ℂ)) * y +
    orientation k * ((Complex.I * (d.weight : ℂ)) * y)) =
    ((if k = 0 then d.zExponent else d.zBarExponent) + rho n p) * y
  by_cases hk : k = 0
  · simp only [orientation, hk, ite_true, ComplexCharacterData.zExponent, rho]
    linear_combination (-(d.weight : ℂ) * y / 2) * Complex.I_sq
  · simp only [orientation, hk, ite_false, ComplexCharacterData.zBarExponent, rho]
    linear_combination ((d.weight : ℂ) * y / 2) * Complex.I_sq

private theorem exists_evalOne_ne_zero (ds : List ComplexCharacterData) (hlen : ds.length = n) :
    ∃ v : KFs n ds, evalOne n ds v ≠ 0 := by
  by_contra! h
  let : Nontrivial (KFs n ds) := complexStandardNontrivial n ds hlen
  obtain ⟨v, hv⟩ := exists_ne (0 : KFs n ds)
  apply hv
  apply Subtype.ext
  change (v : Langlands.GeneralLinear n ℂ → ℂ) = 0
  apply ComplexDuality.eq_zero_of_mem_principalSeries_of_eqOn (mem_of_mem_kFs v.2)
  intro g hg
  let u : Matrix.unitaryGroup (Fin n) ℂ := ⟨(g : CM), hg⟩
  have hu : (Unitary.toUnits u : Langlands.GeneralLinear n ℂ) = g := Units.ext rfl
  have he := h (complexStandardRep n ds u v)
  rw [kFiniteEval_apply, principalSeriesRep_apply_coe] at he
  change (v : Langlands.GeneralLinear n ℂ → ℂ) (1 * Unitary.toUnits u) = 0 at he
  simpa only [one_mul, hu] using he

/-- The actual local action of the center of block `k` is the upper Verma character
of any weight whose shifted orbit is the corresponding normalized exponent list. -/
theorem envelopingAction_blockEnveloping (ds : List ComplexCharacterData) (hlen : ds.length = n)
    (k : Fin 2) (mu : Fin n → ℂ)
    (hmu : (ds.map (if k = 0 then ComplexCharacterData.zExponent
      else ComplexCharacterData.zBarExponent)).Perm (List.ofFn fun i => mu i + rho n i))
    (z : VermaGL.center n) :
    envelopingAction (complexStandardLie n ds) (blockEnveloping n k (z : glU n)) =
      algebraMap ℂ (Module.End ℂ (KFs n ds)) (VermaShifted.upperCharacter n mu z) := by
  let lam := fun i => blockExponent n ds hlen k i + rho n i
  have heval := VermaShifted.character_apply_functional n lam (blockAction n ds k) (evalOne n ds)
    (eval_strictUpper n ds k) (eval_diagonal n ds hlen k) z
  obtain ⟨c, hc⟩ := complexStandardLie_hasInfinitesimalCharacter n ds _
    (blockEnveloping_mem_center n k z)
  obtain ⟨v, hv⟩ := exists_evalOne_ne_zero n ds hlen
  have hcv := LinearMap.congr_fun hc v
  rw [Module.algebraMap_end_apply] at hcv
  have h := heval v
  change evalOne n ds (envelopingAction (complexStandardLie n ds) (blockEnveloping n k z) v) =
    VermaShifted.character n lam z * evalOne n ds v at h
  rw [hcv, map_smul, smul_eq_mul] at h
  have hchar := VermaShifted.character_add_rho_eq_upper n (blockExponent n ds hlen k) mu
    (by rwa [ofFn_blockExponent])
  rw [hc, mul_right_cancel₀ hv h, hchar]

end ComplexStandardCentralCharacter

end Langlands.Archimedean
