import Langlands.Algebra.RosenlichtBoundedInversePairsStatement
import Langlands.Algebra.RosenlichtPolynomialFiniteness
import Mathlib.LinearAlgebra.Dual.Lemmas

open scoped BigOperators

namespace Langlands.Algebra.Rosenlicht

open MvPolynomial

universe u v w

variable {k : Type u} [Field k]

noncomputable def linearForm {σ : Type v} [Fintype σ] (c : σ → k) :
    MvPolynomial σ k := ∑ s, C (c s) * X s

theorem aeval_linearForm {σ : Type v} [Fintype σ] (c x : σ → k) :
    aeval x (linearForm c) = ∑ s, c s * x s := by
  classical
  simp [linearForm]

theorem linearForm_homogeneous {σ : Type v} [Fintype σ] (c : σ → k) :
    (linearForm c).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun _ _ => isHomogeneous_C_mul_X _ _

/-- A rank-at-most-one matrix whose product combination is zero must vanish. -/
theorem matrix_zero_of_minors
    {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
    {B : Type*} [CommRing B] [Algebra k B] [IsDomain B]
    (v : ι → B) (w : κ → B) (hv : LinearIndependent k v) (hw : LinearIndependent k w)
    (x : ι × κ → k)
    (hminor : ∀ i i' j j', x (i,j) * x (i',j') = x (i,j') * x (i',j))
    (hprod : ∑ s : ι × κ, x s • (v s.1 * w s.2) = 0) : x = 0 := by
  classical
  by_contra hx
  obtain ⟨⟨i₀,j₀⟩, h₀⟩ : ∃ s : ι × κ, x s ≠ 0 := by
    simpa only [funext_iff, Pi.zero_apply, not_forall] using hx
  have hmul : (∑ i, x (i,j₀) • v i) * (∑ j, x (i₀,j) • w j) = 0 := by
    calc
      _ = ∑ i, ∑ j, (x (i,j₀) * x (i₀,j)) • (v i * w j) := by
        simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm]
        rw [Finset.sum_comm]
      _ = ∑ i, ∑ j, (x (i,j) * x (i₀,j₀)) • (v i * w j) := by
        congr 1
        funext i
        congr 1
        funext j
        rw [hminor i i₀ j j₀]
      _ = x (i₀,j₀) • (∑ s : ι × κ, x s • (v s.1 * w s.2)) := by
        simp only [Fintype.sum_prod_type, Finset.smul_sum, smul_smul]
        congr 1
        funext i
        congr 1
        funext j
        rw [mul_comm]
      _ = 0 := by rw [hprod, smul_zero]
  rcases mul_eq_zero.mp hmul with h | h
  · have he := Fintype.linearIndependent_iffₛ.mp hv (fun i => x (i,j₀)) 0
      (by simpa using h) i₀
    exact h₀ he
  · have he := Fintype.linearIndependent_iffₛ.mp hw (fun j => x (i₀,j)) 0
      (by simpa using h) j₀
    exact h₀ he

theorem aeval_linear_relation
    {σ : Type v} [Fintype σ] {B : Type*} [CommRing B] [Algebra k B]
    (m : σ → B) (c x : σ → k) (φ : B →ₗ[k] k) :
    aeval x (linearForm (fun s => φ (m s) - c s * φ 1)) =
      φ (∑ s, x s • m s) - (∑ s, c s * x s) * φ 1 := by
  classical
  simp only [aeval_linearForm, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul,
    map_sum, map_smul, smul_eq_mul]
  congr 1
  · apply Finset.sum_congr rfl
    intro s _
    ring
  · apply Finset.sum_congr rfl
    intro s _
    ring

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The normalized rank-one matrices giving a scalar product form a finite set. -/
theorem finite_normalized_rankOne
    [IsAlgClosed k]
    {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
    {B : Type*} [CommRing B] [Algebra k B] [IsDomain B]
    (v : ι → B) (w : κ → B) (hv : LinearIndependent k v) (hw : LinearIndependent k w)
    (c : ι × κ → k) :
    Set.Finite {x : ι × κ → k |
      (∀ i i' j j', x (i,j) * x (i',j') = x (i,j') * x (i',j)) ∧
      (∑ s, x s • (v s.1 * w s.2)) = 1 ∧ (∑ s, c s * x s) = 1} := by
  classical
  let minor (i i' : ι) (j j' : κ) : MvPolynomial (ι × κ) k :=
    X (i,j) * X (i',j') - X (i,j') * X (i',j)
  let rel (φ : B →ₗ[k] k) : MvPolynomial (ι × κ) k :=
    linearForm (fun s => φ (v s.1 * w s.2) - c s * φ 1)
  let S : Set (MvPolynomial (ι × κ) k) :=
    {p | ∃ i i' j j', p = minor i i' j j'} ∪ Set.range rel
  let I : Ideal (MvPolynomial (ι × κ) k) := Ideal.span S
  have hminorI (i i' : ι) (j j' : κ) : minor i i' j j' ∈ I :=
    Ideal.subset_span (Or.inl ⟨i,i',j,j',rfl⟩)
  have hrelI (φ : B →ₗ[k] k) : rel φ ∈ I :=
    Ideal.subset_span (Or.inr ⟨φ,rfl⟩)
  have hI : I.IsHomogeneous (homogeneousSubmodule (ι × κ) k) := by
    apply Ideal.homogeneous_span
    intro p hp
    rcases hp with ⟨i,i',j,j',rfl⟩ | ⟨φ,rfl⟩
    · refine ⟨2, ?_⟩
      exact ((isHomogeneous_X k (i,j)).mul (isHomogeneous_X k (i',j'))).sub
        ((isHomogeneous_X k (i,j')).mul (isHomogeneous_X k (i',j)))
    · exact ⟨1, linearForm_homogeneous _⟩
  have hzero : ∀ x : ι × κ → k, (∀ p ∈ I, aeval x p = 0) →
      aeval x (linearForm c) = 0 → x = 0 := by
    intro x hx hL
    have hmin : ∀ i i' j j',
        x (i,j) * x (i',j') = x (i,j') * x (i',j) := by
      intro i i' j j'
      have h := hx _ (hminorI i i' j j')
      simpa only [minor, map_sub, map_mul, aeval_X, sub_eq_zero] using h
    have hprod : (∑ s, x s • (v s.1 * w s.2)) = 0 := by
      apply (Module.forall_dual_apply_eq_zero_iff k _).mp
      intro φ
      have h := hx _ (hrelI φ)
      change aeval x (linearForm (fun s => φ (v s.1 * w s.2) - c s * φ 1)) = 0 at h
      rw [aeval_linear_relation, ← aeval_linearForm c x, hL,
        zero_mul, sub_zero] at h
      exact h
    exact matrix_zero_of_minors v w hv hw x hmin hprod
  have hfin := finite_points_of_homogeneous_chart I hI (linearForm c)
    (linearForm_homogeneous c) hzero
  apply hfin.subset
  intro x hx
  refine ⟨?_, (aeval_linearForm c x).trans hx.2.2⟩
  have hker : I ≤ RingHom.ker (aeval x : MvPolynomial (ι × κ) k →ₐ[k] k) := by
    apply Ideal.span_le.mpr
    intro p hp
    change aeval x p = 0
    rcases hp with ⟨i,i',j,j',rfl⟩ | ⟨φ,rfl⟩
    · simpa only [minor, map_sub, map_mul, aeval_X, sub_eq_zero] using hx.1 i i' j j'
    · change aeval x (linearForm (fun s => φ (v s.1 * w s.2) - c s * φ 1)) = 0
      rw [aeval_linear_relation, hx.2.1, hx.2.2, one_mul, sub_self]
  exact fun p hp => hker hp

/-- The bounded inverse-pair statement, proved using homogeneous matrix coordinates. -/
theorem boundedInversePairs :
    Langlands.Algebra.RosenlichtBoundedInversePairsStatement.{u,v} := by
  intro k _ _ B _ _ _ epsilon V W _ _
  classical
  let bv := Module.finBasis k V
  let bw := Module.finBasis k W
  let v : Fin (Module.finrank k V) → B := fun i => (bv i : B)
  let w : Fin (Module.finrank k W) → B := fun j => (bw j : B)
  have hv : LinearIndependent k v :=
    bv.linearIndependent.map' V.subtype (Submodule.ker_subtype V)
  have hw : LinearIndependent k w :=
    bw.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  let P : Set (B × B) := {p | p.1 ∈ V ∧ p.2 ∈ W ∧ p.1 * p.2 = 1 ∧
    epsilon p.1 = 1 ∧ epsilon p.2 = 1}
  let α (p : P) : Fin (Module.finrank k V) → k := bv.repr ⟨p.1.1, p.2.1⟩
  let β (p : P) : Fin (Module.finrank k W) → k := bw.repr ⟨p.1.2, p.2.2.1⟩
  have hvsum (p : P) : ∑ i, α p i • v i = p.1.1 := by
    have h := congrArg V.subtype (bv.sum_repr ⟨p.1.1, p.2.1⟩)
    simp only [map_sum, map_smul] at h
    exact h
  have hwsum (p : P) : ∑ j, β p j • w j = p.1.2 := by
    have h := congrArg W.subtype (bw.sum_repr ⟨p.1.2, p.2.2.1⟩)
    simp only [map_sum, map_smul] at h
    exact h
  have hβ (p : P) : ∑ j, β p j * epsilon (w j) = 1 := by
    have h := congrArg epsilon (hwsum p)
    simpa only [map_sum, map_smul, smul_eq_mul, p.2.2.2.2.2] using h
  let F (p : P) (s : Fin (Module.finrank k V) × Fin (Module.finrank k W)) : k :=
    α p s.1 * β p s.2
  let c (s : Fin (Module.finrank k V) × Fin (Module.finrank k W)) : k :=
    epsilon (v s.1) * epsilon (w s.2)
  let T : Set (Fin (Module.finrank k V) × Fin (Module.finrank k W) → k) :=
    {x | (∀ i i' j j', x (i,j) * x (i',j') = x (i,j') * x (i',j)) ∧
      (∑ s, x s • (v s.1 * w s.2)) = 1 ∧ (∑ s, c s * x s) = 1}
  have hT : T.Finite := finite_normalized_rankOne v w hv hw c
  have hF (p : P) : F p ∈ T := by
    have hprod : (∑ s, F p s • (v s.1 * w s.2)) = 1 := by
      calc
        _ = (∑ i, α p i • v i) * (∑ j, β p j • w j) := by
          simp only [Fintype.sum_prod_type, F, Finset.sum_mul, Finset.mul_sum,
            smul_mul_smul_comm]
          rw [Finset.sum_comm]
        _ = 1 := by rw [hvsum, hwsum, p.2.2.2.1]
    refine ⟨?_, hprod, ?_⟩
    · intro i i' j j'
      dsimp only [F]
      ring
    · have h := congrArg epsilon hprod
      simp only [map_sum, map_smul, map_mul, map_one, smul_eq_mul] at h
      convert h using 1
      apply Finset.sum_congr rfl
      intro s _
      exact mul_comm _ _
  let g : P → T := fun p => ⟨F p, hF p⟩
  have hg : Function.Injective g := by
    intro p q hpq
    have hFpq : F p = F q := congrArg Subtype.val hpq
    have hαpq : α p = α q := by
      funext i
      calc
        α p i = ∑ j, F p (i,j) * epsilon (w j) := by
          simp only [F, mul_assoc, ← Finset.mul_sum, hβ, mul_one]
        _ = ∑ j, F q (i,j) * epsilon (w j) := by rw [hFpq]
        _ = α q i := by
          simp only [F, mul_assoc, ← Finset.mul_sum, hβ, mul_one]
    have hfst : p.1.1 = q.1.1 := by
      rw [← hvsum p, ← hvsum q, hαpq]
    have hsnd : p.1.2 = q.1.2 := by
      apply mul_left_cancel₀ (left_ne_zero_of_mul_eq_one p.2.2.2.1)
      rw [p.2.2.2.1, hfst, q.2.2.2.1]
    exact Subtype.ext (Prod.ext hfst hsnd)
  let : Finite T := Set.finite_coe_iff.mpr hT
  exact Set.finite_coe_iff.mp (Finite.of_injective g hg)

end Langlands.Algebra.Rosenlicht
