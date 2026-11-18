import Mathlib

/-!
# Galois descent for semilinear actions of a finite Galois group

For a finite Galois extension `N/K` and an `N`-module `V` with a semilinear action of
`Gal(N/K)`, the comparison map `N ⊗[K] V^G → V` is an isomorphism. For an `N`-algebra with
an action by ring automorphisms the fixed points form a `K`-subalgebra, the comparison map is an
`N`-algebra isomorphism, and central simplicity descends.
-/

universe u v w

open TensorProduct

namespace Langlands.GaloisDescent

section Matrix

variable (K : Type u) (N : Type v) [Field K] [Field N] [Algebra K N]
  [FiniteDimensional K N] [IsGalois K N]

/-- A `K`-basis of `N` indexed by the Galois group (the two have the same cardinality). -/
noncomputable def galBasis : Module.Basis (N ≃ₐ[K] N) K N :=
  (Module.finBasisOfFinrankEq K N (IsGalois.card_aut_eq_finrank K N).symm).reindex
    (Finite.equivFin _).symm

/-- The Galois matrix `M g h = g (b h)` of the basis `galBasis`. -/
noncomputable def galMatrix : Matrix (N ≃ₐ[K] N) (N ≃ₐ[K] N) N :=
  fun g h => g (galBasis K N h)

open Classical in
theorem galMatrix_isUnit : IsUnit (galMatrix K N) := by
  classical
  rw [← Matrix.linearIndependent_rows_iff_isUnit, Fintype.linearIndependent_iff]
  intro c hc g
  have hind : LinearIndependent N
      (fun g : N ≃ₐ[K] N => ((g : N →ₐ[K] N) : N →ₗ[K] N)) :=
    (linearIndependent_toLinearMap K N N).comp _
      (fun a b h => AlgEquiv.coe_toAlgHom_injective h)
  rw [Fintype.linearIndependent_iff] at hind
  refine hind c ?_ g
  refine (galBasis K N).ext fun h => ?_
  have := congrFun hc h
  simpa [galMatrix, Matrix.row, Finset.sum_apply] using this

open Classical in
theorem galMatrix_det_isUnit : IsUnit (galMatrix K N).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp (galMatrix_isUnit K N)

open Classical in
/-- The coefficients `c h = M⁻¹ h 1`, so that `∑ h, g (b h) * c h = δ g 1`. -/
noncomputable def galCoeff (h : N ≃ₐ[K] N) : N :=
  (galMatrix K N)⁻¹ h 1

open Classical in
theorem sum_galBasis_mul_galCoeff (g : N ≃ₐ[K] N) :
    ∑ h, g (galBasis K N h) * galCoeff K N h = if g = 1 then 1 else 0 := by
  classical
  have := congrFun (congrFun (Matrix.mul_nonsing_inv _ (galMatrix_det_isUnit K N)) g) 1
  simpa [Matrix.mul_apply, Matrix.one_apply, galMatrix, galCoeff] using this

open Classical in
theorem sum_inv_mul_galBasis (h' h : N ≃ₐ[K] N) :
    ∑ g, (galMatrix K N)⁻¹ h' g * g (galBasis K N h) = if h' = h then 1 else 0 := by
  classical
  have := congrFun (congrFun (Matrix.nonsing_inv_mul _ (galMatrix_det_isUnit K N)) h') h
  simpa [Matrix.mul_apply, Matrix.one_apply, galMatrix] using this

end Matrix

variable (K : Type u) (N : Type v) [Field K] [Field N] [Algebra K N]

/-- A semilinear action of the Galois group `Gal(N/K)` on an `N`-module `V`:
`act g (x • v) = g x • act g v`. -/
structure SemilinearAction (V : Type w) [AddCommGroup V] [Module N V] where
  /-- The action of a Galois automorphism, as an additive map. -/
  act : (N ≃ₐ[K] N) → V →+ V
  one_act : ∀ v, act 1 v = v
  mul_act : ∀ g h v, act (g * h) v = act g (act h v)
  act_smul : ∀ g (x : N) v, act g (x • v) = g x • act g v

namespace SemilinearAction

variable {K N} {V : Type w} [AddCommGroup V] [Module K V] [Module N V] [IsScalarTower K N V]
variable (ρ : SemilinearAction K N V)

theorem act_algebraMap_smul (g : N ≃ₐ[K] N) (k : K) (v : V) :
    ρ.act g (k • v) = k • ρ.act g v := by
  rw [← algebraMap_smul N k v, ρ.act_smul, AlgEquiv.commutes, algebraMap_smul]

/-- The `K`-subspace of Galois-fixed vectors. -/
def fixed : Submodule K V where
  carrier := {v | ∀ g, ρ.act g v = v}
  add_mem' := by
    intro a b ha hb g
    simp [map_add, ha g, hb g]
  zero_mem' := by
    intro g
    simp
  smul_mem' := by
    intro k v hv g
    simp [ρ.act_algebraMap_smul, hv g]

theorem mem_fixed {v : V} : v ∈ ρ.fixed ↔ ∀ g, ρ.act g v = v := Iff.rfl

/-- The descent comparison map `N ⊗[K] V^G → V`, `x ⊗ v ↦ x • v`. -/
noncomputable def descentMap : N ⊗[K] ρ.fixed →ₗ[N] V :=
  ρ.fixed.subtype.liftBaseChange N

@[simp] theorem descentMap_tmul (x : N) (v : ρ.fixed) :
    ρ.descentMap (x ⊗ₜ v) = x • (v : V) := rfl

section Finite

variable [FiniteDimensional K N]

/-- The trace (Reynolds) operator `v ↦ ∑ g, g • v`. -/
noncomputable def trace : V →+ V := ∑ g, ρ.act g

omit [Module K V] [IsScalarTower K N V] in
theorem trace_apply (v : V) : ρ.trace v = ∑ g, ρ.act g v := by
  simp [trace]

theorem trace_mem_fixed (v : V) : ρ.trace v ∈ ρ.fixed := by
  intro g
  rw [trace_apply, map_sum]
  simp_rw [← ρ.mul_act]
  exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun h => rfl)

omit [FiniteDimensional K N] in
theorem act_smul_of_mem_fixed (g : N ≃ₐ[K] N) (x : N) {v : V} (hv : v ∈ ρ.fixed) :
    ρ.act g (x • v) = g x • v := by
  rw [ρ.act_smul, hv g]

variable [IsGalois K N]

omit [Module K V] [IsScalarTower K N V] in
/-- Every vector is an `N`-combination of traces. -/
theorem eq_sum_galCoeff_smul_trace (v : V) :
    v = ∑ h, galCoeff K N h • ρ.trace (galBasis K N h • v) := by
  classical
  simp_rw [trace_apply, Finset.smul_sum, ρ.act_smul, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, mul_comm (galCoeff K N _), sum_galBasis_mul_galCoeff]
  simp [ite_smul, ρ.one_act]

/-- General form of Galois descent: if `ι : F → V` is injective with range the fixed vectors,
then `N ⊗[K] F → V` is bijective. -/
theorem bijective_liftBaseChange {F : Type*} [AddCommGroup F] [Module K F] (ι : F →ₗ[K] V)
    (hι : Function.Injective ι) (hrange : LinearMap.range ι = ρ.fixed) :
    Function.Bijective (ι.liftBaseChange N) := by
  classical
  constructor
  · intro w₁ w₂ hw
    rw [← sub_eq_zero] at hw ⊢
    rw [← map_sub] at hw
    generalize w₁ - w₂ = w at hw ⊢
    obtain ⟨f, rfl⟩ := TensorProduct.eq_repr_basis_left (galBasis K N) w
    have hfix : ∀ h, ι (f h) ∈ ρ.fixed := fun h => hrange ▸ LinearMap.mem_range_self ι (f h)
    have h0 : ∑ h, galBasis K N h • ι (f h) = 0 := by
      simpa [Finsupp.sum_fintype, map_sum] using hw
    have hg : ∀ g : N ≃ₐ[K] N, ∑ h, g (galBasis K N h) • ι (f h) = 0 := by
      intro g
      have := congrArg (ρ.act g) h0
      rw [map_sum, map_zero] at this
      simpa [ρ.act_smul_of_mem_fixed g _ (hfix _)] using this
    have hf : f = 0 := by
      ext h'
      apply hι
      rw [Finsupp.coe_zero, Pi.zero_apply, map_zero]
      have : ∑ g, (galMatrix K N)⁻¹ h' g • ∑ h, g (galBasis K N h) • ι (f h) = 0 := by
        simp [hg]
      simp_rw [Finset.smul_sum, smul_smul] at this
      rw [Finset.sum_comm] at this
      simp_rw [← Finset.sum_smul, sum_inv_mul_galBasis] at this
      simpa using this
    simp [hf]
  · intro v
    have hmem : ∀ h, ρ.trace (galBasis K N h • v) ∈ LinearMap.range ι := fun h =>
      hrange ▸ ρ.trace_mem_fixed _
    choose f hf using hmem
    refine ⟨∑ h, galCoeff K N h ⊗ₜ f h, ?_⟩
    rw [map_sum]
    conv_rhs => rw [ρ.eq_sum_galCoeff_smul_trace v]
    simp [hf]

theorem descentMap_bijective : Function.Bijective ρ.descentMap :=
  ρ.bijective_liftBaseChange ρ.fixed.subtype Subtype.val_injective (Submodule.range_subtype _)

/-- Galois descent: `N ⊗[K] V^G ≃ V` as `N`-modules. -/
noncomputable def descentEquiv : N ⊗[K] ρ.fixed ≃ₗ[N] V :=
  LinearEquiv.ofBijective ρ.descentMap ρ.descentMap_bijective

@[simp] theorem descentEquiv_tmul (x : N) (v : ρ.fixed) :
    ρ.descentEquiv (x ⊗ₜ v) = x • (v : V) := rfl

end Finite

end SemilinearAction

/-- A semilinear action of `Gal(N/K)` on an `N`-algebra by ring automorphisms. -/
structure SemilinearAlgAction (A : Type w) [Ring A] [Algebra N A]
    extends SemilinearAction K N A where
  act_one : ∀ g, act g 1 = 1
  act_mul : ∀ g x y, act g (x * y) = act g x * act g y

namespace SemilinearAlgAction

variable {K N} {A : Type w} [Ring A] [Algebra N A] [Algebra K A] [IsScalarTower K N A]
variable (ρ : SemilinearAlgAction K N A)

omit [Algebra K A] [IsScalarTower K N A] in
theorem act_algebraMap (g : N ≃ₐ[K] N) (x : N) :
    ρ.act g (algebraMap N A x) = algebraMap N A (g x) := by
  rw [Algebra.algebraMap_eq_smul_one, ρ.act_smul, ρ.act_one, ← Algebra.algebraMap_eq_smul_one]

/-- The fixed `K`-subalgebra. -/
def fixedSubalgebra : Subalgebra K A where
  carrier := ρ.fixed
  add_mem' := ρ.fixed.add_mem
  zero_mem' := ρ.fixed.zero_mem
  mul_mem' := by
    intro a b ha hb g
    rw [ρ.act_mul, ha g, hb g]
  one_mem' := ρ.act_one
  algebraMap_mem' := by
    intro k g
    rw [Algebra.algebraMap_eq_smul_one, ρ.act_algebraMap_smul, ρ.act_one]

theorem mem_fixedSubalgebra {a : A} : a ∈ ρ.fixedSubalgebra ↔ ∀ g, ρ.act g a = a := Iff.rfl

/-- The descent comparison algebra map `N ⊗[K] A^G → A`. -/
noncomputable def descentAlgHom : N ⊗[K] ρ.fixedSubalgebra →ₐ[N] A :=
  Algebra.TensorProduct.lift (Algebra.ofId N A) ρ.fixedSubalgebra.val
    (fun x y => show Commute (Algebra.ofId N A x) (ρ.fixedSubalgebra.val y) from
      Algebra.commute_algebraMap_left x (y : A))

@[simp] theorem descentAlgHom_tmul (x : N) (a : ρ.fixedSubalgebra) :
    ρ.descentAlgHom (x ⊗ₜ a) = x • (a : A) := by
  simp [descentAlgHom, Algebra.smul_def]

theorem descentAlgHom_toLinearMap :
    ρ.descentAlgHom.toLinearMap =
      (ρ.fixedSubalgebra.val.toLinearMap).liftBaseChange N := by
  ext x
  simp

variable [FiniteDimensional K N] [IsGalois K N]

theorem descentAlgHom_bijective : Function.Bijective ρ.descentAlgHom := by
  have := ρ.bijective_liftBaseChange ρ.fixedSubalgebra.val.toLinearMap Subtype.val_injective
    (by ext a; simp [mem_fixedSubalgebra, SemilinearAction.mem_fixed])
  rw [← ρ.descentAlgHom_toLinearMap] at this
  exact this

/-- Galois descent for algebras: `N ⊗[K] A^G ≃ₐ[N] A`. -/
noncomputable def descentAlgEquiv : N ⊗[K] ρ.fixedSubalgebra ≃ₐ[N] A :=
  AlgEquiv.ofBijective ρ.descentAlgHom ρ.descentAlgHom_bijective

@[simp] theorem descentAlgEquiv_tmul (x : N) (a : ρ.fixedSubalgebra) :
    ρ.descentAlgEquiv (x ⊗ₜ a) = x • (a : A) := by
  simp [descentAlgEquiv]

theorem mem_span_fixedSubalgebra (a : A) :
    a ∈ Submodule.span N (Set.range ((↑) : ρ.fixedSubalgebra → A)) := by
  obtain ⟨w, rfl⟩ := ρ.descentAlgHom_bijective.2 a
  induction w using TensorProduct.inductionOn with
  | tmul x b =>
    rw [descentAlgHom_tmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
  | add w₁ w₂ h₁ h₂ =>
    rw [map_add]
    exact Submodule.add_mem _ h₁ h₂

theorem finrank_fixedSubalgebra :
    Module.finrank K ρ.fixedSubalgebra = Module.finrank N A := by
  rw [← ρ.descentAlgEquiv.toLinearEquiv.finrank_eq, Module.finrank_baseChange]

omit [IsGalois K N] in
theorem finiteDimensional_fixedSubalgebra [FiniteDimensional N A] :
    FiniteDimensional K ρ.fixedSubalgebra := by
  have : Module.Finite K A := Module.Finite.trans N A
  infer_instance

/-- Central simplicity descends: centrality. -/
theorem isCentral_fixedSubalgebra [Nontrivial A] [Algebra.IsCentral N A] :
    Algebra.IsCentral K ρ.fixedSubalgebra := by
  constructor
  intro z hz
  rw [Subalgebra.mem_center_iff] at hz
  have hzA : (z : A) ∈ Subalgebra.center N A := by
    rw [Subalgebra.mem_center_iff]
    intro a
    have ha := ρ.mem_span_fixedSubalgebra a
    induction ha using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, rfl⟩ := hy
      exact congrArg Subtype.val (hz b)
    | zero => simp
    | add y₁ y₂ _ _ h₁ h₂ => rw [add_mul, mul_add, h₁, h₂]
    | smul c y _ h => rw [smul_mul_assoc, mul_smul_comm, h]
  obtain ⟨x, hx⟩ := Algebra.mem_bot.mp (Algebra.IsCentral.out hzA)
  have hfix : ∀ g : N ≃ₐ[K] N, g x = x := by
    intro g
    apply (algebraMap N A).injective
    rw [← ρ.act_algebraMap, hx]
    exact z.2 g
  obtain ⟨k, hk⟩ := IntermediateField.mem_bot.mp ((IsGalois.mem_bot_iff_fixed x).mpr hfix)
  refine Algebra.mem_bot.mpr ⟨k, Subtype.ext ?_⟩
  rw [← hx, ← hk, ← IsScalarTower.algebraMap_apply]
  rfl

/-- Central simplicity descends: simplicity. -/
theorem isSimpleRing_fixedSubalgebra [IsSimpleRing A] :
    IsSimpleRing ρ.fixedSubalgebra := by
  classical
  have hnt : Nontrivial ρ.fixedSubalgebra := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    exact zero_ne_one (congrArg Subtype.val h)
  refine IsSimpleRing.of_eq_bot_or_eq_top fun I => ?_
  -- the `N`-span of `I` inside `A`
  let S : Set A := (↑) '' (I : Set ρ.fixedSubalgebra)
  let P : Submodule N A := Submodule.span N S
  have hspan : ∀ a ∈ Submodule.span N (Set.range ((↑) : ρ.fixedSubalgebra → A)),
      ∀ p ∈ P, a * p ∈ P ∧ p * a ∈ P := by
    intro a ha p hp
    induction ha using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, rfl⟩ := hy
      induction hp using Submodule.span_induction with
      | mem q hq =>
        obtain ⟨i, hi, rfl⟩ := hq
        exact ⟨Submodule.subset_span ⟨b * i, I.mul_mem_left b i hi, rfl⟩,
          Submodule.subset_span ⟨i * b, I.mul_mem_right i b hi, rfl⟩⟩
      | zero => simp
      | add q₁ q₂ _ _ h₁ h₂ =>
        rw [mul_add, add_mul]
        exact ⟨P.add_mem h₁.1 h₂.1, P.add_mem h₁.2 h₂.2⟩
      | smul c q _ h =>
        rw [mul_smul_comm, smul_mul_assoc]
        exact ⟨P.smul_mem c h.1, P.smul_mem c h.2⟩
    | zero => simp
    | add y₁ y₂ _ _ h₁ h₂ =>
      rw [add_mul, mul_add]
      exact ⟨P.add_mem h₁.1 h₂.1, P.add_mem h₁.2 h₂.2⟩
    | smul c y _ h =>
      rw [smul_mul_assoc, mul_smul_comm]
      exact ⟨P.smul_mem c h.1, P.smul_mem c h.2⟩
  let J : TwoSidedIdeal A := TwoSidedIdeal.mk' (P : Set A) P.zero_mem P.add_mem P.neg_mem
    (fun {x y} hy => (hspan x (ρ.mem_span_fixedSubalgebra x) y hy).1)
    (fun {x y} hx => (hspan y (ρ.mem_span_fixedSubalgebra y) x hx).2)
  have hJ : ∀ a, a ∈ J ↔ a ∈ P := fun a => TwoSidedIdeal.mem_mk' _ _ _ _ _ _ a
  rcases eq_bot_or_eq_top J with hbot | htop
  · left
    rw [eq_bot_iff]
    intro i hi
    have : (i : A) ∈ J := (hJ _).mpr (Submodule.subset_span ⟨i, hi, rfl⟩)
    rw [hbot] at this
    exact (TwoSidedIdeal.mem_bot _).mpr (Subtype.ext ((TwoSidedIdeal.mem_bot _).mp this))
  · right
    rw [eq_top_iff]
    intro b _
    -- the trace of `y • p` lies in `I` for all `p ∈ P`
    have htr : ∀ p ∈ P, ∀ y : N, ∃ i ∈ I, (i : A) = ρ.trace (y • p) := by
      intro p hp
      induction hp using Submodule.span_induction with
      | mem q hq =>
        obtain ⟨i, hi, rfl⟩ := hq
        intro y
        refine ⟨Algebra.trace K N y • i, ?_, ?_⟩
        · rw [Algebra.smul_def]
          exact I.mul_mem_left _ _ hi
        rw [ρ.trace_apply]
        simp_rw [ρ.act_smul_of_mem_fixed _ _ i.2]
        rw [← Finset.sum_smul, ← trace_eq_sum_automorphisms, algebraMap_smul]
        rfl
      | zero => intro y; exact ⟨0, I.zero_mem, by simp⟩
      | add q₁ q₂ _ _ h₁ h₂ =>
        intro y
        obtain ⟨i₁, hi₁, e₁⟩ := h₁ y
        obtain ⟨i₂, hi₂, e₂⟩ := h₂ y
        exact ⟨i₁ + i₂, I.add_mem hi₁ hi₂, by simp [e₁, e₂, smul_add]⟩
      | smul c q _ h =>
        intro y
        obtain ⟨i, hi, e⟩ := h (y * c)
        exact ⟨i, hi, by rw [e, smul_smul]⟩
    have h1 : (1 : A) ∈ P := (hJ 1).mp (by rw [htop]; exact TwoSidedIdeal.mem_top _)
    obtain ⟨y, hy⟩ := Algebra.trace_surjective (K := K) (L := N) 1
    obtain ⟨i, hi, e⟩ := htr 1 h1 y
    have hi1 : i = 1 := by
      apply Subtype.ext
      rw [e, ρ.trace_apply]
      simp_rw [ρ.act_smul, ρ.act_one]
      rw [← Finset.sum_smul, ← trace_eq_sum_automorphisms, hy, map_one, one_smul]
      rfl
    have : (1 : ρ.fixedSubalgebra) ∈ I := hi1 ▸ hi
    have := I.mul_mem_left b 1 this
    rwa [mul_one] at this

end SemilinearAlgAction

end Langlands.GaloisDescent
