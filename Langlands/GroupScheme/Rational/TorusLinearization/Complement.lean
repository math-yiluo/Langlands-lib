import Langlands.GroupScheme.Rational.TorusLinearization.Universal
import Langlands.GroupScheme.Rational.TorusLinearization.GradedProjection

/-! # A stable complement of the fixed and higher additive polynomials -/

noncomputable section

universe u

open MvPolynomial TensorProduct

namespace Langlands.GroupScheme.TorusLinearization

section Powers

variable {n : ℕ} {p : ℕ} [hp : Fact p.Prime]

omit hp in
theorem natCast_eq_zero_of_algebra (k : Type u) [Field k] [CharP k p] (B : Type u) [CommRing B]
    [Algebra k B] : (p : B) = 0 := by
  rw [← map_natCast (algebraMap k B), CharP.cast_eq_zero, map_zero]

/-- Iterated Frobenius maps additive polynomials into every subspace that contains the
corresponding powers of the variables. -/
theorem pow_mem_of_mem_addSpan {B : Type u} [CommRing B] (h0 : (p : B) = 0)
    {N : Submodule B (MvPolynomial (Fin n) B)} {r : ℕ}
    (hN : ∀ l s, r ≤ s → (X l : MvPolynomial (Fin n) B) ^ p ^ s ∈ N)
    {g : MvPolynomial (Fin n) B} (hg : g ∈ addSpan n B p) : g ^ p ^ r ∈ N := by
  have h0' : (p : MvPolynomial (Fin n) B) = 0 := by
    rw [← map_natCast (C : B →+* MvPolynomial (Fin n) B), h0, map_zero]
  rw [addSpan_eq_span] at hg
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨l, s⟩, rfl⟩ := hx
    rw [← pow_mul, ← pow_add]
    exact hN l (s + r) (by omega)
  | zero => rw [zero_pow (pow_ne_zero _ hp.out.ne_zero)]; exact zero_mem _
  | add x y _ _ hx hy =>
    rw [add_pow_prime_pow_of_natCast_eq_zero p h0' x y r]
    exact add_mem hx hy
  | smul c x _ hx => rw [smul_pow]; exact Submodule.smul_mem _ _ hx

/-- Substituting additive polynomials into an additive polynomial gives an additive
polynomial. -/
theorem aeval_mem_addSpan {R C : Type u} [CommRing R] [CommRing C] [Algebra R C]
    (h0 : (p : C) = 0) {x : Fin n → MvPolynomial (Fin n) C} (hx : ∀ j, x j ∈ addSpan n C p)
    {f : MvPolynomial (Fin n) R} (hf : f ∈ addSpan n R p) : aeval x f ∈ addSpan n C p := by
  rw [addSpan_eq_span] at hf
  induction hf using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨⟨j, r⟩, rfl⟩ := hy
    rw [map_pow, aeval_X]
    exact pow_mem_of_mem_addSpan h0 (fun l s _ => X_pow_mem_addSpan l s) (hx j)
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | smul c y _ hy => rw [map_smul]; exact Submodule.smul_of_tower_mem _ c hy

end Powers

section Higher

variable (n : ℕ) (k : Type u) [Field k] (p : ℕ)

/-- The span of the `X_j ^ p ^ r` with `r ≥ 1`: the additive polynomials without linear
terms. -/
def higher : Submodule k (MvPolynomial (Fin n) k) :=
  frobSpan k p 1 (Set.range (X : Fin n → MvPolynomial (Fin n) k))

variable {n k p}

theorem higher_le_addSpan : higher n k p ≤ addSpan n k p := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨_, ⟨j, rfl⟩, r, -, rfl⟩
  exact X_pow_mem_addSpan j r

theorem X_pow_mem_span_higher (B : Type u) [CommRing B] [Algebra k B] (l : Fin n) {s : ℕ}
    (hs : 1 ≤ s) : (X l : MvPolynomial (Fin n) B) ^ p ^ s ∈
      Submodule.span B (MvPolynomial.map (algebraMap k B) '' (higher n k p : Set _)) :=
  Submodule.subset_span ⟨X l ^ p ^ s, pow_mem_frobSpan ⟨l, rfl⟩ hs, by simp⟩

end Higher

section Linear

variable {k : Type u} [Field k] {σ : Type*}

theorem span_map_id (N : Submodule k (MvPolynomial σ k)) :
    Submodule.span k (MvPolynomial.map (algebraMap k k) '' (N : Set (MvPolynomial σ k))) = N := by
  have e : (MvPolynomial.map (algebraMap k k) '' (N : Set (MvPolynomial σ k))) = N := by
    ext g
    simp [MvPolynomial.map_id]
  rw [e, Submodule.span_eq]

/-- Subtracting the extension of a linear map `ψ` from a polynomial supported on `s` gives an
element of the span of the `X^m - ψ X^m`, `m ∈ s`. -/
theorem sub_extend_mem_span (B : Type u) [CommRing B] [Algebra k B]
    (ψ : MvPolynomial σ k →ₗ[k] MvPolynomial σ k) {N : Submodule k (MvPolynomial σ k)}
    {s : Set (σ →₀ ℕ)} (hN : ∀ m ∈ s, monomial m 1 - ψ (monomial m 1) ∈ N)
    {g : MvPolynomial σ B} (hg : g ∈ restrictSupport B s) :
    g - extend B ψ g ∈ Submodule.span B (MvPolynomial.map (algebraMap k B) '' (N : Set _)) := by
  classical
  rw [g.as_sum, map_sum, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun m hm => ?_
  have hms : m ∈ s := (show (↑g.support : Set _) ⊆ s from hg) hm
  have e : monomial m (g.coeff m) - extend B ψ (monomial m (g.coeff m)) =
      g.coeff m • MvPolynomial.map (algebraMap k B) (monomial m 1 - ψ (monomial m 1)) := by
    rw [extend_monomial, map_sub, smul_sub, map_monomial, _root_.map_one (algebraMap k B),
      smul_monomial, smul_eq_mul, mul_one]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hN m hms, rfl⟩)

variable {K : Type u} [Field K] [Algebra k K]

/-- The descent to `k` of a `K`-linear map of polynomials, through a linear form `θ`. -/
def descend (θ : K →ₗ[k] k) (π' : MvPolynomial σ K →ₗ[K] MvPolynomial σ K) :
    MvPolynomial σ k →ₗ[k] MvPolynomial σ k where
  toFun f := coeffMap θ (π' (MvPolynomial.map (algebraMap k K) f))
  map_add' f g := by rw [map_add, map_add, map_add]
  map_smul' c f := by
    rw [map_smul_eq K c f, map_smul, algebraMap_smul, map_smul]
    rfl

theorem descend_apply (θ : K →ₗ[k] k) (π' : MvPolynomial σ K →ₗ[K] MvPolynomial σ K)
    (f : MvPolynomial σ k) :
    descend θ π' f = coeffMap θ (π' (MvPolynomial.map (algebraMap k K) f)) := rfl

/-- Extending first to `K ⊗ B` and then applying `θ` agrees with extending the descended map. -/
theorem coeffMap_tens_extend_map (θ : K →ₗ[k] k) (π' : MvPolynomial σ K →ₗ[K] MvPolynomial σ K)
    (B : Type u) [CommRing B] [Algebra k B] (g : MvPolynomial σ B) :
    coeffMap (tens B θ) (extend (K ⊗[k] B) π' (MvPolynomial.map
      ((Algebra.TensorProduct.includeRight : B →ₐ[k] K ⊗[k] B) : B →+* K ⊗[k] B) g)) =
      extend B (descend θ π') g := by
  induction g using MvPolynomial.induction_on' with
  | monomial m b =>
    rw [map_monomial, extend_monomial, extend_monomial]
    refine MvPolynomial.ext _ _ fun m' => ?_
    rw [coeff_coeffMap, coeff_smul, coeff_smul, coeff_map, coeff_map, descend_apply,
      coeff_coeffMap, map_monomial, _root_.map_one (algebraMap k K)]
    simp [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
      tens_tmul, Algebra.smul_def, mul_comm]
  | add g h hg hh => rw [map_add, map_add, map_add, hg, hh, map_add]

/-- The kernel of a descended map on the additive polynomials. -/
def complement {n : ℕ} (p : ℕ) (θ : K →ₗ[k] k)
    (π' : MvPolynomial (Fin n) K →ₗ[K] MvPolynomial (Fin n) K) :
    Submodule k (MvPolynomial (Fin n) k) :=
  LinearMap.ker (descend θ π') ⊓ addSpan n k p

end Linear

namespace PointAction

variable {k K : Type u} [Field k] [Field K] [Algebra k K] {I : Type u} {n : ℕ}
  (a : PointAction k K I n)

theorem pull_X {B : Type u} [CommRing B] [Algebra k B] (t : a.Pt B) (j : Fin n) :
    a.pull t (X j) = a.poly t j :=
  aeval_X _ _

theorem pull_map {B D : Type u} [CommRing B] [Algebra k B] [CommRing D] [Algebra k D]
    (g : B →ₐ[k] D) (t : a.Pt B) (f : MvPolynomial (Fin n) k) :
    a.pull (a.map g t) f = MvPolynomial.map (g : B →+* D) (a.pull t f) := by
  have hp : a.poly (a.map g t) = fun i => MvPolynomial.map (g : B →+* D) (a.poly t i) :=
    funext fun i => a.poly_map g t i
  have h := MvPolynomial.comp_aeval_apply (a.poly t) (MvPolynomial.mapAlgHom (σ := Fin n) g) f
  simp only [MvPolynomial.mapAlgHom_apply] at h
  rw [pull, pull, hp, ← h]

theorem Stable.sup {W W' : Submodule k (MvPolynomial (Fin n) k)} (hW : a.Stable W)
    (hW' : a.Stable W') : a.Stable (W ⊔ W') := fun B _ _ t w hw => by
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hw
  rw [map_add]
  refine add_mem (Submodule.span_mono ?_ (hW B t x hx)) (Submodule.span_mono ?_ (hW' B t y hy))
  · exact Set.image_mono (SetLike.coe_mono le_sup_left)
  · exact Set.image_mono (SetLike.coe_mono le_sup_right)

variable (p : ℕ) [hp : Fact p.Prime] [CharP k p]

theorem pull_mem_addSpan {B : Type u} [CommRing B] [Algebra k B] (t : a.Pt B)
    {f : MvPolynomial (Fin n) k} (hf : f ∈ addSpan n k p) : a.pull t f ∈ addSpan n B p :=
  aeval_mem_addSpan (natCast_eq_zero_of_algebra k B)
    (fun j => (a.isAddPoly_poly t j).mem_addSpan k) hf

theorem pullK_mem_addSpan {C : Type u} [CommRing C] [Algebra k C] [Algebra K C]
    [IsScalarTower k K C] (t : a.Pt C) {h : MvPolynomial (Fin n) K}
    (hh : h ∈ addSpan n K p) : a.pullK t h ∈ addSpan n C p :=
  aeval_mem_addSpan (natCast_eq_zero_of_algebra k C)
    (fun j => (a.isAddPoly_poly t j).mem_addSpan k) hh

/-- The higher additive polynomials form a stable subspace. -/
theorem stable_higher : a.Stable (higher n k p) := fun B _ _ t w hw => by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨_, ⟨j, rfl⟩, r, hr, rfl⟩ := hx
    rw [map_pow, pull_X]
    exact pow_mem_of_mem_addSpan (natCast_eq_zero_of_algebra k B)
      (fun l s hs => X_pow_mem_span_higher B l (le_trans hr hs))
      ((a.isAddPoly_poly t j).mem_addSpan k)
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_of_tower_mem _ c hx

/-- The fixed and the higher additive polynomials together. -/
def fixHigher : Submodule k (MvPolynomial (Fin n) k) := higher n k p ⊔ a.fixed p

theorem stable_fixHigher : a.Stable (a.fixHigher p) :=
  Stable.sup a (a.stable_higher p) (a.stable_fixed p)

omit hp [CharP k p] in
theorem fixHigher_le_addSpan : a.fixHigher p ≤ addSpan n k p :=
  sup_le higher_le_addSpan fun _ hf => hf.1

section Graded

variable [Fintype I] [DecidableEq I]

theorem comp_mem_addSpan (χ : I → ℤ) {h : MvPolynomial (Fin n) K}
    (hh : h ∈ addSpan n K p) : a.comp χ h ∈ addSpan n K p := by
  rw [← a.coeffMap_pullK_univ χ h]
  exact coeffMap_mem_restrictSupport _ (a.pullK_mem_addSpan p _ hh)

omit [CharP k p] hp in
/-- The `K`-span of a stable subspace is graded. -/
theorem comp_mem_span_of_stable {W : Submodule k (MvPolynomial (Fin n) k)} (hW : a.Stable W)
    (χ : I → ℤ) {v : MvPolynomial (Fin n) K}
    (hv : v ∈ Submodule.span K (MvPolynomial.map (algebraMap k K) '' (W : Set _))) :
    a.comp χ v ∈ Submodule.span K (MvPolynomial.map (algebraMap k K) '' (W : Set _)) := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    exact a.comp_map_mem_span hW χ hw
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

omit [CharP k p] hp in
/-- A `K`-linear map commuting with the components commutes with the action of split points. -/
theorem extend_pullK_σ (π' : MvPolynomial (Fin n) K →ₗ[K] MvPolynomial (Fin n) K)
    (hπ : ∀ χ v, π' (a.comp χ v) = a.comp χ (π' v)) {C : Type u} [CommRing C] [Algebra k C]
    [Algebra K C] [IsScalarTower k K C] (τ : I → Cˣ) (h : MvPolynomial (Fin n) K) :
    extend C π' (a.pullK (a.σ τ) h) = a.pullK (a.σ τ) (π' h) := by
  have hs' : (a.coact (π' h)).coeff.support ⊆ (a.coact h).coeff.support := by
    intro χ hχ
    rw [Finsupp.mem_support_iff] at hχ ⊢
    intro h0
    have e1 : a.comp χ (π' h) = 0 := by
      rw [← hπ, show a.comp χ h = 0 from h0, map_zero]
    exact hχ e1
  rw [a.pullK_σ τ h subset_rfl, a.pullK_σ τ (π' h) hs', map_sum]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [← smul_eq_C_mul, ← smul_eq_C_mul, map_smul, extend_map, hπ]

omit [CharP k p] hp in
/-- Equivariance of the descended map. -/
theorem pull_descend (θ : K →ₗ[k] k) (π' : MvPolynomial (Fin n) K →ₗ[K] MvPolynomial (Fin n) K)
    (hπ : ∀ χ v, π' (a.comp χ v) = a.comp χ (π' v)) {B : Type u} [CommRing B] [Algebra k B]
    (t : a.Pt B) (f : MvPolynomial (Fin n) k) :
    a.pull t (descend θ π' f) = extend B (descend θ π') (a.pull t f) := by
  obtain ⟨τ, hτ⟩ := a.σ_surj (a.ext t)
  rw [descend_apply, a.pull_coeffMap θ t, ← hτ, ← a.extend_pullK_σ π' hπ τ, hτ, a.pullK_map,
    a.pull_map, coeffMap_tens_extend_map]

/-- A projection onto the `K`-span of the fixed and higher parts that commutes with the
components. -/
theorem exists_projection : ∃ π' : MvPolynomial (Fin n) K →ₗ[K] MvPolynomial (Fin n) K,
    (∀ y ∈ Submodule.span K (MvPolynomial.map (algebraMap k K) '' (a.fixHigher p : Set _)),
      π' y = y) ∧
    (∀ v, π' v ∈ Submodule.span K (MvPolynomial.map (algebraMap k K) '' (a.fixHigher p : Set _))) ∧
    ∀ χ v, π' (a.comp χ v) = a.comp χ (π' v) :=
  exists_graded_projection a.comp (fun χ ψ v => by convert a.comp_comp χ ψ v)
    (fun v => ⟨_, a.sum_comp v subset_rfl⟩) _
    (fun χ _ hy => a.comp_mem_span_of_stable (a.stable_fixHigher p) χ hy)

section Projection

variable (θ : K →ₗ[k] k) (π' : MvPolynomial (Fin n) K →ₗ[K] MvPolynomial (Fin n) K)

omit [CharP k p] hp [Fintype I] [DecidableEq I] in
theorem descend_of_mem_fixHigher (hθ : θ 1 = 1)
    (hπ1 : ∀ y ∈ Submodule.span K (MvPolynomial.map (algebraMap k K) '' (a.fixHigher p : Set _)),
      π' y = y)
    {f : MvPolynomial (Fin n) k} (hf : f ∈ a.fixHigher p) : descend θ π' f = f := by
  rw [descend_apply, hπ1 _ (Submodule.subset_span ⟨f, hf, rfl⟩), coeffMap_map_of_eq_one θ hθ]

omit [CharP k p] hp [Fintype I] [DecidableEq I] in
theorem descend_mem_fixHigher
    (hπ2 : ∀ v, π' v ∈
      Submodule.span K (MvPolynomial.map (algebraMap k K) '' (a.fixHigher p : Set _)))
    (f : MvPolynomial (Fin n) k) : descend θ π' f ∈ a.fixHigher p := by
  have h := coeffMap_mem_span θ (hπ2 (MvPolynomial.map (algebraMap k K) f))
  rwa [span_map_id] at h

variable (hθ : θ 1 = 1)
  (hπ1 : ∀ y ∈ Submodule.span K (MvPolynomial.map (algebraMap k K) '' (a.fixHigher p : Set _)),
    π' y = y)
  (hπ2 : ∀ v, π' v ∈
    Submodule.span K (MvPolynomial.map (algebraMap k K) '' (a.fixHigher p : Set _)))

include hθ hπ1 hπ2

omit hp [CharP k p] [Fintype I] [DecidableEq I] in
theorem sub_descend_mem_complement {f : MvPolynomial (Fin n) k} (hf : f ∈ addSpan n k p) :
    f - descend θ π' f ∈ complement p θ π' := by
  have hd := a.descend_mem_fixHigher p θ π' hπ2 f
  refine Submodule.mem_inf.mpr ⟨?_, sub_mem hf (a.fixHigher_le_addSpan p hd)⟩
  rw [LinearMap.mem_ker, map_sub, a.descend_of_mem_fixHigher p θ π' hθ hπ1 hd, sub_self]

omit hp [CharP k p] [Fintype I] [DecidableEq I] in
theorem addSpan_le_complement_sup : addSpan n k p ≤ complement p θ π' ⊔ a.fixHigher p :=
  fun f hf => Submodule.mem_sup.mpr ⟨_, a.sub_descend_mem_complement p θ π' hθ hπ1 hπ2 hf, _,
    a.descend_mem_fixHigher p θ π' hπ2 f, sub_add_cancel f _⟩

omit [CharP k p] hp [Fintype I] [DecidableEq I] hπ2 in
theorem complement_inf_fixHigher : complement p θ π' ⊓ a.fixHigher p = ⊥ := by
  refine eq_bot_iff.mpr fun f hf => ?_
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.mp hf
  rw [Submodule.mem_bot, ← a.descend_of_mem_fixHigher p θ π' hθ hπ1 h2]
  exact LinearMap.mem_ker.mp (Submodule.mem_inf.mp h1).1

/-- The complement is stable. -/
theorem stable_complement (hπ3 : ∀ χ v, π' (a.comp χ v) = a.comp χ (π' v)) :
    a.Stable (complement p θ π') := fun B _ _ t f hf => by
  have hf' := Submodule.mem_inf.mp hf
  have h0 : extend B (descend θ π') (a.pull t f) = 0 := by
    rw [← a.pull_descend θ π' hπ3 t f, LinearMap.mem_ker.mp hf'.1, map_zero]
  have hN : ∀ m ∈ addExponents n p, monomial m 1 - descend θ π' (monomial m 1) ∈
      complement p θ π' := fun m hm => by
    refine a.sub_descend_mem_complement p θ π' hθ hπ1 hπ2 ?_
    show (↑(monomial m (1 : k)).support : Set _) ⊆ addExponents n p
    intro x hx
    rw [Finset.mem_coe] at hx
    rw [Finset.mem_singleton.mp (support_monomial_subset hx)]
    exact hm
  have h := sub_extend_mem_span B (descend θ π') hN (a.pull_mem_addSpan p t hf'.2)
  rwa [h0, sub_zero] at h

end Projection

end Graded

end PointAction

end Langlands.GroupScheme.TorusLinearization
