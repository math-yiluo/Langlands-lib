import Langlands.Automorphic.StandardBlockConstantTermFamily
import Langlands.Automorphic.ConstantTermFiltration
import Langlands.Automorphic.IrreducibleOperatorSubquotient

/-! # Cyclic selection of a standard block constant term -/

noncomputable section

universe u uR uV uW

open NumberField

set_option autoImplicit false

namespace Langlands.Automorphic

section Module

variable {R : Type uR} [Ring R] {V : Type uV} [AddCommGroup V] [Module R V]
variable {W : Type uW} [AddCommGroup W] [Module R W] [IsSimpleModule R W]

private theorem exists_cyclic_cut_quotient {r : ℕ}
    (K : Finset (Fin r) → Submodule R V) (hzero : ∀ v ∈ K ∅, v = 0)
    (q : V →ₗ[R] W) (hq : Function.Surjective q) :
    ∃ (s : Finset (Fin r)) (x : V) (p : (R ∙ (K s).mkQ x) →ₗ[R] W),
      (∀ t : Finset (Fin r), s ⊂ t → (R ∙ x) ≤ K t) ∧
      Function.Surjective p ∧
      p ⟨(K s).mkQ x, Submodule.mem_span_singleton_self _⟩ = q x ∧ q x ≠ 0 := by
  let l : List (Finset (Fin r)) := standardBlockCuts (r + 1)
  have hindex (s : Finset (Fin r)) : ∃ i : Fin l.length, l.get i = s :=
    List.mem_iff_get.mp (show s ∈ l from mem_standardBlockCuts (n := r + 1) s)
  have horder : l.Pairwise (fun s t => s.card ≤ t.card) := standardBlockCuts_pairwise (r + 1)
  let c (i : Fin l.length) : V →ₗ[R] (V ⧸ K (l.get i)) := (K (l.get i)).mkQ
  have hc : ∀ x, (∀ i, c i x = 0) → x = 0 := by
    intro x hx
    obtain ⟨i, hi⟩ := hindex ∅
    have hz : x ∈ K (l.get i) := (Submodule.Quotient.mk_eq_zero (p := K (l.get i))).mp (hx i)
    exact hzero x (hi ▸ hz)
  obtain ⟨i, x, p, hv, hp, hpx, hx⟩ := exists_cyclic_term_quotient c hc q hq
  refine ⟨l.get i, x, p, ?_, hp, hpx, hx⟩
  intro t ht
  obtain ⟨j, hj⟩ := hindex t
  have hcard : (l.get i).card < (l.get j).card := by rw [hj]; exact Finset.card_lt_card ht
  have hij : i < j := by
    rcases lt_trichotomy j i with hji | rfl | hij
    · exact (hcard.not_ge (horder.rel_get_of_lt hji)).elim
    · exact (lt_irrefl _ hcard).elim
    · exact hij
  intro y hy
  have hyz : c j y = 0 := LinearMap.mem_ker.mp (hv j hij hy)
  have hyK : y ∈ K (l.get j) := (Submodule.Quotient.mk_eq_zero (p := K (l.get j))).mp hyz
  exact hj ▸ hyK

end Module

variable (F : Type u) [Field F] [NumberField F]

local instance blockTermSelectionRationalAddCommGroup {n : ℕ} : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance blockTermSelectionContinuousAddCommGroup {n : ℕ} : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance blockTermSelectionFiniteSmoothAddCommGroup {n : ℕ} : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance blockTermSelectionFormsAddCommGroup {n : ℕ} : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance blockTermSelectionStableAddCommGroup {n : ℕ} : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance blockTermSelectionRealizationAddCommGroup {n : ℕ} (S : OperatorRealization F n) : AddCommGroup S.Space := Submodule.addCommGroup _

/-- The cyclic image of an actual block constant term, in the quotient model for
its transported operator action. -/
def cyclicBlockConstantTermImage {n : ℕ} (S : OperatorRealization F n) (e : Fin n → ℤ)
    (x : S.representation.asModule) :
    Submodule (MonoidAlgebra ℂ (automorphicOperatorAlgebra F n))
      (S.representation.asModule ⧸ realizedBlockConstantTermKernel F S e) :=
  _ ∙ (realizedBlockConstantTermKernel F S e).mkQ x

set_option maxHeartbeats 100000 in
/-- Some block constant term of a cyclic numerator still surjects onto the given
irreducible quotient. The kernels for all strict refinements contain the cyclic numerator. -/
theorem exists_cyclicBlockConstantTermQuotient {r : ℕ} (Q : IrreducibleOperatorSubquotient F r) :
    let R := MonoidAlgebra ℂ (automorphicOperatorAlgebra F (r + 1))
    let S := Q.subquotient.upper
    let K (s : Finset (Fin r)) := realizedBlockConstantTermKernel F S (standardBlockWeight s)
    ∃ (s : Finset (Fin r)) (x : S.representation.asModule)
      (p : cyclicBlockConstantTermImage F S (standardBlockWeight s) x →ₗ[R] Q.representation.asModule),
      (∀ t : Finset (Fin r), s ⊂ t → (R ∙ x) ≤ K t) ∧
      Function.Surjective p ∧
      p ⟨(K s).mkQ x, Submodule.mem_span_singleton_self _⟩ = Q.subquotient.projection x ∧
      Q.subquotient.projection x ≠ 0 := by
  let S := Q.subquotient.upper
  let K (s : Finset (Fin r)) := realizedBlockConstantTermKernel F S (standardBlockWeight s)
  let q := Representation.IntertwiningMap.equivLinearMapAsModule _ _ Q.subquotient.projection
  exact exists_cyclic_cut_quotient K
    (fun _ hx => eq_zero_of_mem_realizedBlockConstantTermKernel_empty F S hx)
    q Q.subquotient.projection_surjective

end Langlands.Automorphic
