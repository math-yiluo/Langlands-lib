import Langlands.GroupScheme.IntegralModel.Smoothening.Hopf
import Langlands.GroupScheme.IntegralModel.Smoothening.TerminationDilatation
import Langlands.GroupScheme.IntegralModel.Smoothening.TerminationTensor

/-! # The smoothening sequence inside the integral functions

Let `R` be a discrete valuation ring with uniformizer `ϖ` and fraction field `K`, and let `A` be
a flat commutative Hopf algebra over `R`. Inside `B = integralFunctions R K A` define `C 0` to be
the image of `A` and `C (n+1) = C n [J n / ϖ]`, where `J n` consists of the elements of `C n`
whose values at all `R`-points of `A` lie in the maximal ideal. This is the ring form of the
sequence of dilatations of Kaletha–Prasad, Construction A.6.1. Every element of `B` lies in some
`C n`. -/

noncomputable section

universe u

open scoped TensorProduct
open IsLocalRing

namespace Langlands.GroupScheme.IntegralModel.Smoothening.Termination

variable {R : Type u} {K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K] {A : Type u} [CommRing A] [HopfAlgebra R A]

variable (R K A) in
/-- The ideal of elements of a subalgebra of the integral functions whose values at all
`R`-points lie in the maximal ideal. -/
def jIdeal (C : Subalgebra R (integralFunctions R K A)) : Ideal C where
  carrier := {c | ∀ φ : A →ₐ[R] R, point φ (c : integralFunctions R K A) ∈ maximalIdeal R}
  add_mem' ha hb φ := by
    rw [Subalgebra.coe_add, map_add]
    exact Ideal.add_mem _ (ha φ) (hb φ)
  zero_mem' φ := by
    rw [Subalgebra.coe_zero, map_zero]
    exact Ideal.zero_mem _
  smul_mem' c d hd φ := by
    rw [smul_eq_mul, Subalgebra.coe_mul, map_mul]
    exact Ideal.mul_mem_left _ _ (hd φ)

theorem mem_jIdeal {C : Subalgebra R (integralFunctions R K A)} {c : C} :
    c ∈ jIdeal R K A C ↔ ∀ φ : A →ₐ[R] R, point φ (c : integralFunctions R K A) ∈ maximalIdeal R :=
  Iff.rfl

variable (R K A) in
/-- The smoothening sequence. -/
def chain (ϖ : R) : ℕ → Subalgebra R (integralFunctions R K A)
  | 0 => (incl R K A).range
  | n + 1 => dilat ϖ (jIdeal R K A (chain ϖ n))

theorem chain_zero (ϖ : R) : chain R K A ϖ 0 = (incl R K A).range := rfl

theorem chain_succ (ϖ : R) (n : ℕ) :
    chain R K A ϖ (n + 1) = dilat ϖ (jIdeal R K A (chain R K A ϖ n)) := rfl

theorem chain_le_succ (ϖ : R) (n : ℕ) : chain R K A ϖ n ≤ chain R K A ϖ (n + 1) :=
  le_dilat _

theorem chain_mono (ϖ : R) {m n : ℕ} (h : m ≤ n) : chain R K A ϖ m ≤ chain R K A ϖ n := by
  induction n, h using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih => exact ih.trans (chain_le_succ ϖ n)

theorem range_incl_le_chain (ϖ : R) (n : ℕ) : (incl R K A).range ≤ chain R K A ϖ n :=
  chain_mono ϖ (Nat.zero_le n)

/-- If `ϖ b` lies in `C n`, then `b` lies in `C (n+1)`. -/
theorem mem_chain_succ_of_smul_mem {ϖ : R} (hϖ : Irreducible ϖ) {n : ℕ}
    {b : integralFunctions R K A} (hb : ϖ • b ∈ chain R K A ϖ n) :
    b ∈ chain R K A ϖ (n + 1) := by
  rw [chain_succ]
  apply divSet_subset_dilat
  refine ⟨⟨ϖ • b, hb⟩, ?_, rfl⟩
  rw [mem_jIdeal]
  intro φ
  rw [point_smul, hϖ.maximalIdeal_eq]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self ϖ)

theorem mem_chain_add_of_pow_smul_mem {ϖ : R} (hϖ : Irreducible ϖ) :
    ∀ (m n : ℕ) {b : integralFunctions R K A}, ϖ ^ m • b ∈ chain R K A ϖ n →
      b ∈ chain R K A ϖ (n + m) := by
  intro m
  induction m with
  | zero => intro n b hb; simpa using hb
  | succ m ih =>
    intro n b hb
    rw [pow_succ', mul_smul] at hb
    have h1 := mem_chain_succ_of_smul_mem hϖ hb
    have h2 := ih (n + 1) h1
    rwa [show n + 1 + m = n + (m + 1) by omega] at h2

/-- Every integral function lies in some member of the smoothening sequence. -/
theorem exists_mem_chain {ϖ : R} (hϖ : Irreducible ϖ) (b : integralFunctions R K A) :
    ∃ n, b ∈ chain R K A ϖ n := by
  obtain ⟨s, a, hs, hsa⟩ := exists_smul_eq_one_tmul K A (b : K ⊗[R] A)
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hs hϖ
  refine ⟨0 + m, mem_chain_add_of_pow_smul_mem hϖ m 0 ?_⟩
  have h : ϖ ^ m • b = (↑u⁻¹ : R) • incl R K A a := by
    apply Subtype.ext
    rw [Subalgebra.coe_smul, Subalgebra.coe_smul, coe_incl, ← hsa, smul_smul,
      ← mul_assoc, Units.inv_mul, one_mul]
  rw [h, chain_zero]
  exact Subalgebra.smul_mem _ (AlgHom.mem_range_self _ a) _

section Comul

open Coalgebra Bialgebra

/-- Values at pairs of points of the comultiplication are values at the product point. -/
theorem lift_point_comp_comul (φ ψ : A →ₐ[R] R) :
    (Algebra.TensorProduct.lift (point (K := K) φ) (point (K := K) ψ)
        (fun _ _ => .all _ _)).comp (comulAlgHom R (integralFunctions R K A)) =
      point ((Algebra.TensorProduct.lift φ ψ (fun _ _ => .all _ _)).comp (comulAlgHom R A)) := by
  rw [eq_point ((Algebra.TensorProduct.lift (point (K := K) φ) (point (K := K) ψ)
        (fun _ _ => .all _ _)).comp (comulAlgHom R (integralFunctions R K A)))]
  congr 1
  apply AlgHom.ext
  intro a
  rw [AlgHom.comp_apply, AlgHom.comp_apply, comulAlgHom_int, comulInt_incl, comulAux,
    AlgHom.comp_apply, AlgHom.comp_apply]
  induction (comulAlgHom R A a) using TensorProduct.inductionOn with
  | tmul x y => simp [point_incl]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

/-- The value at a pair of points of an element of `B ⊗ B`. -/
abbrev pairValue (φ ψ : A →ₐ[R] R) :
    integralFunctions R K A ⊗[R] integralFunctions R K A →ₐ[R] R :=
  Algebra.TensorProduct.lift (point (K := K) φ) (point (K := K) ψ) (fun _ _ => .all _ _)

theorem pairValue_comul_mem {C : Subalgebra R (integralFunctions R K A)} {j : C}
    (hj : j ∈ jIdeal R K A C) (φ ψ : A →ₐ[R] R) :
    pairValue (K := K) φ ψ (comulAlgHom R (integralFunctions R K A) (j : integralFunctions R K A))
      ∈ maximalIdeal R := by
  rw [← AlgHom.comp_apply, lift_point_comp_comul]
  exact hj _

variable (R K A) in
/-- The span in `B ⊗ B` of the tensors `c ⊗ c'` with `c, c' ∈ S`. -/
def pureSpan (S T : Set (integralFunctions R K A)) :
    Submodule R (integralFunctions R K A ⊗[R] integralFunctions R K A) :=
  Submodule.span R {t | ∃ c ∈ S, ∃ c' ∈ T, t = c ⊗ₜ c'}

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
theorem tmul_mem_pureSpan {S T : Set (integralFunctions R K A)} {c c'}
    (hc : c ∈ S) (hc' : c' ∈ T) : c ⊗ₜ c' ∈ pureSpan R K A S T :=
  Submodule.subset_span ⟨c, hc, c', hc', rfl⟩

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
theorem pureSpan_mono {S S' T T' : Set (integralFunctions R K A)} (hS : S ⊆ S') (hT : T ⊆ T') :
    pureSpan R K A S T ≤ pureSpan R K A S' T' :=
  Submodule.span_mono fun _ ⟨c, hc, c', hc', h⟩ => ⟨c, hS hc, c', hT hc', h⟩

/-- The elements of a subalgebra with values in the maximal ideal, as a subset of `B`. -/
def jSet (C : Subalgebra R (integralFunctions R K A)) : Set (integralFunctions R K A) :=
  {b | b ∈ C ∧ ∀ φ : A →ₐ[R] R, point φ b ∈ maximalIdeal R}

/-- **Tensor density in span form.** -/
theorem mem_sup_of_pairValue (C : Subalgebra R (integralFunctions R K A))
    {X : integralFunctions R K A ⊗[R] integralFunctions R K A}
    (hX : X ∈ pureSpan R K A C C)
    (hval : ∀ φ ψ, pairValue (K := K) φ ψ X ∈ maximalIdeal R) :
    X ∈ pureSpan R K A C (jSet C) ⊔ pureSpan R K A (jSet C) C := by
  set M : Submodule R (integralFunctions R K A) := Subalgebra.toSubmodule C
  have hrange : pureSpan R K A C C ≤ LinearMap.range (TensorProduct.map M.subtype M.subtype) := by
    rw [pureSpan, Submodule.span_le]
    rintro _ ⟨c, hc, c', hc', rfl⟩
    exact ⟨(⟨c, hc⟩ : M) ⊗ₜ (⟨c', hc'⟩ : M), by simp⟩
  obtain ⟨F, rfl⟩ := hrange hX
  set Fφ : (A →ₐ[R] R) → M →ₗ[R] R := fun φ => (point (K := K) φ).toLinearMap ∘ₗ M.subtype
  have hprod : ∀ φ ψ (G : M ⊗[R] M), productForm (C := M) (D := M) (Fφ φ) (Fφ ψ) G =
      pairValue (K := K) φ ψ (TensorProduct.map M.subtype M.subtype G) := by
    intro φ ψ G
    induction G using TensorProduct.inductionOn with
    | tmul x y => simp [Fφ]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
  have hsup := mem_sup_of_productForm (C := M) (D := M) Fφ Fφ F fun φ ψ => by
    rw [hprod]
    exact hval φ ψ
  have hJ : ∀ j : maxLocus (C := M) Fφ, ((j : M) : integralFunctions R K A) ∈ jSet C :=
    fun j => ⟨(j : M).2, j.2⟩
  obtain ⟨u, ⟨G₁, rfl⟩, w, ⟨G₂, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hsup
  clear hX hval hsup
  rw [map_add]
  refine Submodule.add_mem_sup ?_ ?_
  · induction G₁ using TensorProduct.inductionOn with
    | tmul m j =>
      rw [LinearMap.lTensor_tmul, TensorProduct.map_tmul]
      exact tmul_mem_pureSpan m.2 (hJ j)
    | add x y hx hy => rw [map_add, map_add]; exact Submodule.add_mem _ hx hy
  · induction G₂ using TensorProduct.inductionOn with
    | tmul j m =>
      rw [LinearMap.rTensor_tmul, TensorProduct.map_tmul]
      exact tmul_mem_pureSpan (hJ j) m.2
    | add x y hx hy => rw [map_add, map_add]; exact Submodule.add_mem _ hx hy

end Comul

section ChainHopf

open Coalgebra Bialgebra

variable {ϖ : R} (hϖ : Irreducible ϖ)

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
theorem mul_mem_pureSpan (C : Subalgebra R (integralFunctions R K A))
    {x y : integralFunctions R K A ⊗[R] integralFunctions R K A}
    (hx : x ∈ pureSpan R K A C C) (hy : y ∈ pureSpan R K A C C) :
    x * y ∈ pureSpan R K A C C := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, c', hc', rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨d, hd, d', hd', rfl⟩ := hy
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      exact tmul_mem_pureSpan (C.mul_mem hc hd) (C.mul_mem hc' hd')
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
    | smul r y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hy
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add x z _ _ hx hz => rw [add_mul]; exact Submodule.add_mem _ hx hz
  | smul r x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r hx

include hϖ in
/-- Elements of `J ⊗ C + C ⊗ J` are `ϖ` times elements of the tensor span of the dilatation. -/
theorem sup_le_map_smul (C : Subalgebra R (integralFunctions R K A)) :
    pureSpan R K A C (jSet C) ⊔ pureSpan R K A (jSet C) C ≤
      (pureSpan R K A (dilat ϖ (jIdeal R K A C)) (dilat ϖ (jIdeal R K A C))).map
        (LinearMap.lsmul R _ ϖ) := by
  have hdiv : ∀ j ∈ jSet C, ∃ b ∈ dilat ϖ (jIdeal R K A C), j = ϖ • b := by
    rintro j ⟨hjC, hj⟩
    obtain ⟨b, hb⟩ := exists_eq_smul_of_dvd hϖ.ne_zero j fun φ => by
      have := hj φ
      rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at this
      exact this
    exact ⟨b, divSet_subset_dilat _ ⟨⟨j, hjC⟩, hj, hb.symm⟩, hb⟩
  have hC : (C : Set (integralFunctions R K A)) ⊆ dilat ϖ (jIdeal R K A C) := le_dilat _
  refine sup_le ?_ ?_
  · rw [pureSpan, Submodule.span_le]
    rintro _ ⟨c, hc, j, hj, rfl⟩
    obtain ⟨b, hb, rfl⟩ := hdiv j hj
    exact ⟨c ⊗ₜ b, tmul_mem_pureSpan (hC hc) hb, by
      rw [LinearMap.lsmul_apply, TensorProduct.tmul_smul]⟩
  · rw [pureSpan, Submodule.span_le]
    rintro _ ⟨j, hj, c, hc, rfl⟩
    obtain ⟨b, hb, rfl⟩ := hdiv j hj
    exact ⟨b ⊗ₜ c, tmul_mem_pureSpan hb (hC hc), by
      rw [LinearMap.lsmul_apply, TensorProduct.smul_tmul']⟩

include hϖ in
/-- The comultiplication of `B` maps each member of the smoothening sequence into the span of
its tensor square. -/
theorem comul_mem_pureSpan (n : ℕ) {c : integralFunctions R K A} (hc : c ∈ chain R K A ϖ n) :
    comulAlgHom R (integralFunctions R K A) c ∈
      pureSpan R K A (chain R K A ϖ n) (chain R K A ϖ n) := by
  induction n generalizing c with
  | zero =>
    obtain ⟨a, rfl⟩ := (AlgHom.mem_range _).mp hc
    rw [comulAlgHom_int, comulInt_incl, comulAux, AlgHom.comp_apply]
    induction (comulAlgHom R A a) using TensorProduct.inductionOn with
    | tmul x y =>
      rw [Algebra.TensorProduct.map_tmul]
      exact tmul_mem_pureSpan (AlgHom.mem_range_self _ x) (AlgHom.mem_range_self _ y)
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | succ n ih =>
    set C := chain R K A ϖ n
    change comulAlgHom R (integralFunctions R K A) c ∈
      pureSpan R K A (dilat ϖ (jIdeal R K A C)) (dilat ϖ (jIdeal R K A C))
    let P : Subalgebra R (integralFunctions R K A) :=
      { carrier := {y | comulAlgHom R (integralFunctions R K A) y ∈
          pureSpan R K A (dilat ϖ (jIdeal R K A C)) (dilat ϖ (jIdeal R K A C))}
        mul_mem' := fun {a b} ha hb => by
          simp only [Set.mem_ofPred_eq, map_mul] at ha hb ⊢
          exact mul_mem_pureSpan _ ha hb
        add_mem' := fun {a b} ha hb => by
          simp only [Set.mem_ofPred_eq, map_add] at ha hb ⊢
          exact Submodule.add_mem _ ha hb
        algebraMap_mem' := fun r => by
          simp only [Set.mem_ofPred_eq, AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply]
          exact tmul_mem_pureSpan (Subalgebra.algebraMap_mem _ r) (Subalgebra.one_mem _) }
    suffices hle : dilat ϖ (jIdeal R K A C) ≤ P from hle hc
    apply Algebra.adjoin_le
    rintro x (hx | ⟨j, hj, hjx⟩)
    · exact pureSpan_mono (le_dilat (jIdeal R K A C)) (le_dilat (jIdeal R K A C)) (ih hx)
    · have hsup := mem_sup_of_pairValue C (ih j.2) fun φ ψ => pairValue_comul_mem hj φ ψ
      obtain ⟨Y, hY, hYeq⟩ := sup_le_map_smul hϖ C hsup
      change comulAlgHom R (integralFunctions R K A) x ∈
        pureSpan R K A (dilat ϖ (jIdeal R K A C)) (dilat ϖ (jIdeal R K A C))
      have : comulAlgHom R (integralFunctions R K A) x = Y := by
        apply smul_right_injective _ hϖ.ne_zero
        change ϖ • _ = ϖ • _
        rw [← map_smul, hjx, ← hYeq, LinearMap.lsmul_apply]
      rw [this]
      exact hY

/-- The values of a point after the antipode. -/
theorem point_comp_antipodeInt (φ : A →ₐ[R] R) :
    (point (K := K) φ).comp antipodeInt = point (φ.comp (HopfAlgebra.antipodeAlgHom R A)) := by
  rw [eq_point ((point (K := K) φ).comp antipodeInt)]
  congr 1
  apply AlgHom.ext
  intro a
  rw [AlgHom.comp_apply, AlgHom.comp_apply, antipodeInt_incl, point_incl]
  rfl

/-- The antipode of `B` preserves each member of the smoothening sequence. -/
theorem antipodeInt_mem (n : ℕ) {c : integralFunctions R K A} (hc : c ∈ chain R K A ϖ n) :
    antipodeInt c ∈ chain R K A ϖ n := by
  induction n generalizing c with
  | zero =>
    obtain ⟨a, rfl⟩ := (AlgHom.mem_range _).mp hc
    rw [antipodeInt_incl]
    exact AlgHom.mem_range_self _ _
  | succ n ih =>
    set C := chain R K A ϖ n
    change antipodeInt c ∈ dilat ϖ (jIdeal R K A C)
    suffices hle : dilat ϖ (jIdeal R K A C) ≤ (dilat ϖ (jIdeal R K A C)).comap antipodeInt from
      hle hc
    apply Algebra.adjoin_le
    rintro x (hx | ⟨j, hj, hjx⟩)
    · exact le_dilat (jIdeal R K A C) (ih hx)
    · show antipodeInt x ∈ dilat ϖ (jIdeal R K A C)
      apply divSet_subset_dilat
      refine ⟨⟨antipodeInt (j : integralFunctions R K A), ih j.2⟩, fun φ => ?_, ?_⟩
      · change point φ (antipodeInt (j : integralFunctions R K A)) ∈ maximalIdeal R
        rw [← AlgHom.comp_apply, point_comp_antipodeInt]
        exact hj _
      · change ϖ • antipodeInt x = antipodeInt (j : integralFunctions R K A)
        rw [← map_smul, hjx]

end ChainHopf

end Langlands.GroupScheme.IntegralModel.Smoothening.Termination
