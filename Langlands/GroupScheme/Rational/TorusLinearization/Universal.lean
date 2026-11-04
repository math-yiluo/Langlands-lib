import Langlands.GroupScheme.Rational.TorusLinearization.Descent

/-! # Stable subspaces, fixed polynomials and the universal point -/

noncomputable section

universe u

open MvPolynomial TensorProduct

namespace Langlands.GroupScheme.TorusLinearization

section Scalar

variable {k B S : Type*} [CommRing k] [CommRing B] [CommRing S] [Algebra k B] [Algebra k S]
  {σ : Type*}

theorem coeffMap_smul_map (l : B →ₗ[k] S) (b : B) (w : MvPolynomial σ k) :
    coeffMap l (b • MvPolynomial.map (algebraMap k B) w) =
      l b • MvPolynomial.map (algebraMap k S) w := by
  refine MvPolynomial.ext _ _ fun m => ?_
  rw [coeff_coeffMap, coeff_smul, coeff_smul, coeff_map, coeff_map, smul_eq_mul, smul_eq_mul,
    mul_comm b, ← Algebra.smul_def, map_smul, Algebra.smul_def, mul_comm]

/-- Coefficientwise linear maps carry spans of polynomials from the base to spans of the
same polynomials. -/
theorem coeffMap_mem_span (l : B →ₗ[k] S) {W : Set (MvPolynomial σ k)}
    {x : MvPolynomial σ B}
    (hx : x ∈ Submodule.span B (MvPolynomial.map (algebraMap k B) '' W)) :
    coeffMap l x ∈ Submodule.span S (MvPolynomial.map (algebraMap k S) '' W) := by
  have key : ∀ b : B, coeffMap l (b • x) ∈
      Submodule.span S (MvPolynomial.map (algebraMap k S) '' W) := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, hw, rfl⟩ := hx
      intro b
      rw [coeffMap_smul_map]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨w, hw, rfl⟩)
    | zero => intro b; rw [smul_zero, map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => intro b; rw [smul_add, map_add]; exact Submodule.add_mem _ (hx b) (hy b)
    | smul c x _ hx => intro b; rw [smul_smul]; exact hx (b * c)
  simpa using key 1

end Scalar

section Theta

variable {k K : Type*} [Field k] [Field K] [Algebra k K] {σ : Type*}

theorem coeffMap_map_of_eq_one (θ : K →ₗ[k] k) (hθ : θ 1 = 1) (f : MvPolynomial σ k) :
    coeffMap θ (MvPolynomial.map (algebraMap k K) f) = f := by
  refine MvPolynomial.ext _ _ fun m => ?_
  rw [coeff_coeffMap, coeff_map, Algebra.algebraMap_eq_smul_one, map_smul, hθ, smul_eq_mul,
    mul_one]

/-- Descent of membership: a polynomial over `k` in the `K`-span of a `k`-subspace lies in the
subspace. -/
theorem mem_of_map_mem_span {N : Submodule k (MvPolynomial σ k)} {f : MvPolynomial σ k}
    (hf : MvPolynomial.map (algebraMap k K) f ∈
      Submodule.span K (MvPolynomial.map (algebraMap k K) '' (N : Set (MvPolynomial σ k)))) :
    f ∈ N := by
  obtain ⟨θ, hθ⟩ := exists_theta k K
  have h := coeffMap_mem_span θ hf
  rw [coeffMap_map_of_eq_one θ hθ] at h
  have e : (MvPolynomial.map (algebraMap k k) '' (N : Set (MvPolynomial σ k))) = N := by
    ext g
    simp [MvPolynomial.map_id]
  rwa [e, Submodule.span_eq] at h

end Theta

namespace PointAction

variable {k K : Type u} [Field k] [Field K] [Algebra k K] {I : Type u} {n : ℕ}
  (a : PointAction k K I n)

/-- A subspace of polynomials over `k` is stable when the pullback along every point lies in
the span of the subspace. -/
def Stable (W : Submodule k (MvPolynomial (Fin n) k)) : Prop :=
  ∀ (B : Type u) [CommRing B] [Algebra k B] (t : a.Pt B), ∀ w ∈ W,
    a.pull t w ∈ Submodule.span B
      (MvPolynomial.map (algebraMap k B) '' (W : Set (MvPolynomial (Fin n) k)))

/-- The fixed additive polynomials over `k`. -/
def fixed (p : ℕ) : Submodule k (MvPolynomial (Fin n) k) where
  carrier := {f | f ∈ addSpan n k p ∧ ∀ (B : Type u) [CommRing B] [Algebra k B] (t : a.Pt B),
    a.pull t f = MvPolynomial.map (algebraMap k B) f}
  add_mem' {f g} hf hg := ⟨add_mem hf.1 hg.1, fun B _ _ t => by
    simp only [map_add, hf.2 B t, hg.2 B t]⟩
  zero_mem' := ⟨zero_mem _, fun B _ _ t => by simp⟩
  smul_mem' c f hf := ⟨Submodule.smul_mem _ c hf.1, fun B _ _ t => by
    rw [map_smul, hf.2 B t, map_smul_eq, algebraMap_smul]⟩

theorem stable_fixed (p : ℕ) : a.Stable (a.fixed p) := fun B _ _ t w hw => by
  rw [hw.2 B t]
  exact Submodule.subset_span ⟨w, hw, rfl⟩

section Universal

variable [Fintype I] [DecidableEq I]

theorem charOf_unitsOf {C : Type u} [CommRing C] (χ : Multiplicative (I → ℤ) →* Cˣ) :
    charOf (unitsOf χ) = χ := by
  refine MonoidHom.ext fun ψ => ?_
  change ∏ i, χ (Multiplicative.ofAdd (Pi.single i 1)) ^ (Multiplicative.toAdd ψ i) = χ ψ
  simp_rw [← map_zpow, ← map_prod]
  congr 1
  apply Multiplicative.toAdd.injective
  rw [toAdd_prod]
  simp_rw [toAdd_zpow, toAdd_ofAdd]
  conv_rhs => rw [← Finset.univ_sum_single (Multiplicative.toAdd ψ)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Pi.single_smul, smul_eq_mul, mul_one]

variable (K I) in
/-- The coordinate units of the universal point, over the group algebra of the characters. -/
def univUnits : I → (AddMonoidAlgebra K (I → ℤ))ˣ :=
  unitsOf (AddMonoidAlgebra.of K (I → ℤ)).toHomUnits

theorem charOf_univUnits (χ : I → ℤ) :
    ((charOf (univUnits K I) (Multiplicative.ofAdd χ) : (AddMonoidAlgebra K (I → ℤ))ˣ) :
      AddMonoidAlgebra K (I → ℤ)) = AddMonoidAlgebra.single χ 1 := by
  rw [univUnits, charOf_unitsOf, MonoidHom.coe_toHomUnits, AddMonoidAlgebra.of_apply]
  rfl

variable (K I) in
/-- The coefficient of a character in the group algebra. -/
def coeffAt (χ : I → ℤ) : AddMonoidAlgebra K (I → ℤ) →ₗ[K] K :=
  Finsupp.lapply χ ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv K).toLinearMap

omit [Fintype I] [DecidableEq I] in
theorem coeffAt_apply (χ : I → ℤ) (x : AddMonoidAlgebra K (I → ℤ)) :
    coeffAt K I χ x = x.coeff χ := rfl

/-- Extraction of the components from the universal point. -/
theorem coeffMap_pullK_univ (ψ : I → ℤ) (h : MvPolynomial (Fin n) K) :
    coeffMap (coeffAt K I ψ) (a.pullK (a.σ (univUnits K I)) h) = a.comp ψ h := by
  classical
  rw [a.pullK_σ (univUnits K I) h (Finset.subset_insert ψ _), map_sum,
    Finset.sum_eq_single_of_mem ψ (Finset.mem_insert_self _ _)]
  · rw [charOf_univUnits, ← smul_eq_C_mul, coeffMap_smul_map, coeffAt_apply,
      AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same, one_smul]
    exact MvPolynomial.map_id _
  · intro χ _ hχ
    rw [charOf_univUnits, ← smul_eq_C_mul, coeffMap_smul_map, coeffAt_apply,
      AddMonoidAlgebra.coeff_single, Finsupp.single_eq_of_ne hχ.symm, zero_smul]

/-- The components of a stable subspace lie in its `K`-span. -/
theorem comp_map_mem_span {W : Submodule k (MvPolynomial (Fin n) k)} (hW : a.Stable W)
    (χ : I → ℤ) {w : MvPolynomial (Fin n) k} (hw : w ∈ W) :
    a.comp χ (MvPolynomial.map (algebraMap k K) w) ∈
      Submodule.span K (MvPolynomial.map (algebraMap k K) '' (W : Set _)) := by
  rw [← a.coeffMap_pullK_univ χ, a.pullK_map]
  exact coeffMap_mem_span ((coeffAt K I χ).restrictScalars k)
    (hW (AddMonoidAlgebra K (I → ℤ)) (a.σ (univUnits K I)) w hw)

/-- Fixed polynomials have weight zero. -/
theorem comp_map_fixed (p : ℕ) {χ : I → ℤ} (hχ : χ ≠ 0) {f : MvPolynomial (Fin n) k}
    (hf : f ∈ a.fixed p) : a.comp χ (MvPolynomial.map (algebraMap k K) f) = 0 := by
  rw [← a.coeffMap_pullK_univ χ, a.pullK_map, hf.2,
    ← one_smul (AddMonoidAlgebra K (I → ℤ)) (MvPolynomial.map _ f)]
  change coeffMap ((coeffAt K I χ).restrictScalars k) _ = 0
  rw [coeffMap_smul_map, LinearMap.restrictScalars_apply, coeffAt_apply,
    AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_of_ne hχ,
    zero_smul]

/-- Coefficientwise images of weight-zero additive polynomials are fixed. -/
theorem coeffMap_mem_fixed (p : ℕ) (l : K →ₗ[k] k) {h : MvPolynomial (Fin n) K}
    (hh : h ∈ addSpan n K p) (h0 : ∀ χ, χ ≠ 0 → a.comp χ h = 0) :
    coeffMap l h ∈ a.fixed p := by
  refine ⟨coeffMap_mem_restrictSupport l hh, fun B _ _ t => ?_⟩
  obtain ⟨τ, hτ⟩ := a.σ_surj (a.ext t)
  have hs : (a.coact h).coeff.support ⊆ {0} := by
    intro χ hχ
    rw [Finset.mem_singleton]
    by_contra hne
    exact (Finsupp.mem_support_iff.mp hχ) (h0 χ hne)
  have hsum : a.comp 0 h = h := by
    have := a.sum_comp h hs
    rwa [Finset.sum_singleton] at this
  rw [a.pull_coeffMap l t h, ← hτ, a.pullK_σ τ h hs, Finset.sum_singleton, hsum, ofAdd_zero,
    map_one, Units.val_one, C_1, one_mul]
  refine MvPolynomial.ext _ _ fun m => ?_
  have h1 : ∀ c : K, algebraMap K (K ⊗[k] B) c = c ⊗ₜ 1 := fun c => by
    simp [Algebra.TensorProduct.algebraMap_apply]
  rw [coeff_coeffMap, coeff_map, coeff_map, coeff_coeffMap, h1, tens_tmul,
    Algebra.algebraMap_eq_smul_one]

/-- Weight-zero additive polynomials over `K` lie in the `K`-span of the fixed ones. -/
theorem mem_span_fixed (p : ℕ) {h : MvPolynomial (Fin n) K} (hh : h ∈ addSpan n K p)
    (h0 : ∀ χ, χ ≠ 0 → a.comp χ h = 0) :
    h ∈ Submodule.span K (MvPolynomial.map (algebraMap k K) '' (a.fixed p : Set _)) := by
  classical
  let b := Module.Basis.ofVectorSpace k K
  let T := h.support.biUnion fun m => (b.repr (h.coeff m)).support
  have key : h = ∑ ι ∈ T, b ι • MvPolynomial.map (algebraMap k K) (coeffMap (b.coord ι) h) := by
    refine MvPolynomial.ext _ _ fun m => ?_
    rw [coeff_sum]
    simp only [coeff_smul, coeff_map, coeff_coeffMap, Module.Basis.coord_apply, smul_eq_mul]
    have hsub : (b.repr (h.coeff m)).support ⊆ T := by
      by_cases hm : m ∈ h.support
      · exact Finset.subset_biUnion_of_mem (fun m => (b.repr (h.coeff m)).support) hm
      · rw [notMem_support_iff.mp hm, map_zero]
        simp
    conv_lhs => rw [← b.linearCombination_repr (h.coeff m)]
    rw [Finsupp.linearCombination_apply,
      Finsupp.sum_of_support_subset _ hsub (fun i c => c • b i) (fun i _ => zero_smul k (b i))]
    refine Finset.sum_congr rfl fun ι _ => ?_
    rw [Algebra.smul_def, mul_comm]
  rw [key]
  exact Submodule.sum_mem _ fun ι _ => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨_, a.coeffMap_mem_fixed p (b.coord ι) hh h0, rfl⟩)

end Universal

end PointAction

end Langlands.GroupScheme.TorusLinearization
