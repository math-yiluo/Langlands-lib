import Langlands.CommutativeAlgebra.DiagonalCoalgebraImage
import Langlands.CommutativeAlgebra.DiagonalCoalgebraLocus
import Mathlib.RingTheory.Ideal.IdempotentFG
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! # Bialgebra maps into group algebras: surjectivity and integrality of coefficients -/

noncomputable section

open TensorProduct

namespace Langlands.Algebra.HopfPointIntegralClosure

open CommutativeAlgebra

section Surjectivity

variable {R : Type*} [CommRing R] {B : Type*} [CommRing B] [Bialgebra R B]
  {M : Type*} [AddCommGroup M]

/-- The ideal of degree-`m` coefficients of the values of a bialgebra map `B → R[M]`. -/
def coeffIdeal (φ : B →ₐc[R] AddMonoidAlgebra R M) (m : M) : Ideal R :=
  LinearMap.range
    ((DiagonalCoalgebraImage.coefficient m).comp (φ : B →ₗ[R] AddMonoidAlgebra R M))

theorem coeff_mem_coeffIdeal (φ : B →ₐc[R] AddMonoidAlgebra R M) (m : M) (b : B) :
    (φ b).coeff m ∈ coeffIdeal φ m :=
  ⟨b, rfl⟩

/-- Multiply the degree-`m` coefficients of the two tensor factors. -/
def coeffPair (m : M) : AddMonoidAlgebra R M ⊗[R] AddMonoidAlgebra R M →ₗ[R] R :=
  LinearMap.mul' R R ∘ₗ
    TensorProduct.map (DiagonalCoalgebraImage.coefficient m)
      (DiagonalCoalgebraImage.coefficient m)

omit [AddCommGroup M] in
theorem coeffPair_tmul (m : M) (x y : AddMonoidAlgebra R M) :
    coeffPair m (x ⊗ₜ[R] y) = x.coeff m * y.coeff m := by
  simp [coeffPair]

omit [AddCommGroup M] in
theorem coeffPair_comul (m : M) (x : AddMonoidAlgebra R M) :
    coeffPair m (Coalgebra.comul x) = x.coeff m := by
  classical
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hx, hy]
  | single n r =>
    simp only [AddMonoidAlgebra.comul_single]
    simp only [CommSemiring.comul_apply, TensorProduct.map_tmul,
      AddMonoidAlgebra.lsingle_apply]
    rw [coeffPair_tmul]
    by_cases h : n = m
    · subst n
      simp
    · simp [AddMonoidAlgebra.coeff_single, Ne.symm h]

private theorem mul'_map_mem_mul (f : B →ₗ[R] R) (t : B ⊗[R] B) :
    LinearMap.mul' R R (TensorProduct.map f f t) ∈
      LinearMap.range f * LinearMap.range f := by
  induction t with
  | tmul x y =>
    simp only [TensorProduct.map_tmul, LinearMap.mul'_apply]
    exact Ideal.mul_mem_mul ⟨x, rfl⟩ ⟨y, rfl⟩
  | add x y hx hy => rw [map_add, map_add]; exact add_mem hx hy

/-- For a bialgebra map, each coefficient ideal is contained in its square. -/
theorem coeffIdeal_le_mul (φ : B →ₐc[R] AddMonoidAlgebra R M) (m : M) :
    coeffIdeal φ m ≤ coeffIdeal φ m * coeffIdeal φ m := by
  rintro _ ⟨b, rfl⟩
  have h : coeffPair m (TensorProduct.map (φ : B →ₗ[R] AddMonoidAlgebra R M)
      (φ : B →ₗ[R] AddMonoidAlgebra R M) (Coalgebra.comul b)) = (φ b).coeff m := by
    rw [CoalgHomClass.map_comp_comul_apply, coeffPair_comul]
  change (φ b).coeff m ∈ _
  rw [← h, coeffPair, LinearMap.comp_apply, ← LinearMap.comp_apply (TensorProduct.map _ _),
    ← TensorProduct.map_comp]
  exact mul'_map_mem_mul _ _

theorem isIdempotentElem_coeffIdeal (φ : B →ₐc[R] AddMonoidAlgebra R M) (m : M) :
    IsIdempotentElem (coeffIdeal φ m) :=
  le_antisymm Ideal.mul_le_left (coeffIdeal_le_mul φ m)

/-- Over a noetherian domain, a nonzero coefficient ideal of a bialgebra map is the unit
ideal. -/
theorem coeffIdeal_eq_top [IsDomain R] [IsNoetherianRing R]
    (φ : B →ₐc[R] AddMonoidAlgebra R M) (m : M)
    (hm : ∃ b : B, (φ b).coeff m ≠ 0) : coeffIdeal φ m = ⊤ := by
  rcases (Ideal.isIdempotentElem_iff_eq_bot_or_top _
    (IsNoetherian.noetherian (coeffIdeal φ m))).mp (isIdempotentElem_coeffIdeal φ m) with h | h
  · obtain ⟨b, hb⟩ := hm
    exact absurd (by simpa [h] using coeff_mem_coeffIdeal φ m b) hb
  · exact h

/-- **Surjectivity of a bialgebra map into a group algebra** (the Hopf step of
Kaletha–Prasad Lemma B.2.3 for split tori). Over a noetherian domain `R`, a bialgebra map
`B → R[M]` all of whose coefficient forms are nonzero is surjective. -/
theorem surjective_of_coeff_ne_zero [IsDomain R] [IsNoetherianRing R]
    (φ : B →ₐc[R] AddMonoidAlgebra R M) (hne : ∀ m : M, ∃ b : B, (φ b).coeff m ≠ 0) :
    Function.Surjective φ := by
  refine DiagonalCoalgebraLocus.surjective_of_generators_mem φ.toAlgHom Set.univ
    AddSubmonoid.closure_univ fun m _ => ?_
  have h1 : (1 : R) ∈ coeffIdeal φ m := by
    rw [coeffIdeal_eq_top φ m (hne m)]; exact Submodule.mem_top
  obtain ⟨b, hb⟩ := h1
  have h := DiagonalCoalgebraImage.single_coefficient_mem_range φ b m
  have hb' : (φ b).coeff m = 1 := hb
  rwa [hb'] at h

end Surjectivity

section Evaluation

variable {I : Type*} [Fintype I]

/-- The character `m ↦ ∏ᵢ tᵢ ^ mᵢ` of `ℤ^I` attached to an `I`-indexed family of units. -/
def unitChar {B : Type*} [CommMonoid B] (t : I → Bˣ) : Multiplicative (I → ℤ) →* Bˣ where
  toFun m := ∏ i, t i ^ (m.toAdd i)
  map_one' := by simp
  map_mul' m n := by
    simp only [toAdd_mul, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]

theorem unitChar_apply {B : Type*} [CommMonoid B] (t : I → Bˣ) (m : Multiplicative (I → ℤ)) :
    unitChar t m = ∏ i, t i ^ (m.toAdd i) :=
  rfl

theorem unitChar_map {A B : Type*} [CommMonoid A] [CommMonoid B] (f : A →* B) (t : I → Aˣ)
    (m : Multiplicative (I → ℤ)) :
    unitChar (fun i => Units.map f (t i)) m = Units.map f (unitChar t m) := by
  simp only [unitChar_apply, map_prod, map_zpow]

/-- Evaluation of a Laurent polynomial in the variables `I` at a family of units. -/
def evalUnits (R : Type*) {B : Type*} [CommRing R] [CommRing B] [Algebra R B] (t : I → Bˣ) :
    AddMonoidAlgebra R (I → ℤ) →ₐ[R] B :=
  AddMonoidAlgebra.lift R B (I → ℤ) ((Units.coeHom B).comp (unitChar t))

theorem evalUnits_single (R : Type*) {B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    (t : I → Bˣ) (m : I → ℤ) (r : R) :
    evalUnits R t (AddMonoidAlgebra.single m r) =
      algebraMap R B r * ((unitChar t (.ofAdd m) : Bˣ) : B) := by
  rw [evalUnits, AddMonoidAlgebra.lift_single, Algebra.smul_def]
  rfl

theorem evalUnits_apply (R : Type*) {B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    (t : I → Bˣ) (P : AddMonoidAlgebra R (I → ℤ)) :
    evalUnits R t P =
      P.coeff.sum fun m c => algebraMap R B c * ((unitChar t (.ofAdd m) : Bˣ) : B) :=
  AddMonoidAlgebra.lift_apply' _ _

/-- Evaluation commutes with a ring homomorphism applied to coefficients and values. -/
theorem evalUnits_mapRingHom {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (t : I → Aˣ) (P : AddMonoidAlgebra A (I → ℤ)) :
    evalUnits B (fun i => Units.map (f : A →* B) (t i))
        (AddMonoidAlgebra.mapRingHom (I → ℤ) f P) = f (evalUnits A t P) := by
  induction P using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single m r =>
    rw [AddMonoidAlgebra.mapRingHom_single, evalUnits_single, evalUnits_single, unitChar_map,
      map_mul, Algebra.algebraMap_self, RingHom.id_apply, Units.coe_map]
    rfl

/-- Evaluating a Laurent polynomial over `K` at units of a `K`-algebra `L` is the same as
first extending its coefficients to `L`. -/
theorem evalUnits_mapRingHom_algebraMap {K L : Type*} [CommRing K] [CommRing L] [Algebra K L]
    (t : I → Lˣ) (P : AddMonoidAlgebra K (I → ℤ)) :
    evalUnits L t (AddMonoidAlgebra.mapRingHom (I → ℤ) (algebraMap K L) P) =
      evalUnits K t P := by
  induction P using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single m r =>
    rw [AddMonoidAlgebra.mapRingHom_single, evalUnits_single, evalUnits_single,
      Algebra.algebraMap_self, RingHom.id_apply]

/-- A Laurent polynomial over `K` all of whose coefficients come from `R` comes from `R`. -/
theorem mem_range_mapAlgHom_of_coeff {R K : Type*} [CommRing R] [CommRing K] [Algebra R K]
    (P : AddMonoidAlgebra K (I → ℤ))
    (h : ∀ m, P.coeff m ∈ Set.range (algebraMap R K)) :
    P ∈ (AddMonoidAlgebra.mapAlgHom (I → ℤ) (Algebra.ofId R K)).range := by
  classical
  choose c hc using h
  refine ⟨∑ m ∈ P.coeff.support, AddMonoidAlgebra.single m (c m), ?_⟩
  apply AddMonoidAlgebra.coeff_injective
  ext n
  change (AddMonoidAlgebra.mapAlgHom (I → ℤ) (Algebra.ofId R K) _).coeff n = _
  rw [AddMonoidAlgebra.coeff_mapAlgHom, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  by_cases hn : n ∈ P.coeff.support
  · rw [Finset.sum_eq_single n (fun b _ hb => by
        simp [AddMonoidAlgebra.coeff_single, hb])
      (fun h => absurd hn h)]
    simp [AddMonoidAlgebra.coeff_single, hc]
  · rw [Finset.sum_eq_zero fun b hb => ?_, map_zero, Finsupp.notMem_support_iff.mp hn]
    have hbn : b ≠ n := fun h => hn (h ▸ hb)
    simp [AddMonoidAlgebra.coeff_single, hbn]

/-- The characters `t ↦ ∏ᵢ tᵢ ^ mᵢ` of the group `(kˣ)^I`, with values in `k`. -/
def evalChar (k : Type*) [Field k] (m : I → ℤ) : (I → kˣ) →* k :=
  (Units.coeHom k).comp
    { toFun := fun t => unitChar t (.ofAdd m)
      map_one' := by simp [unitChar_apply]
      map_mul' := fun s t => by
        simp only [unitChar_apply, toAdd_ofAdd, Pi.mul_apply, mul_zpow,
          Finset.prod_mul_distrib] }

theorem evalChar_apply (k : Type*) [Field k] (m : I → ℤ) (t : I → kˣ) :
    evalChar k m t = ((unitChar t (.ofAdd m) : kˣ) : k) :=
  rfl

/-- Over an infinite field, distinct exponents give distinct characters of `(kˣ)^I`. -/
theorem evalChar_injective (k : Type*) [Field k] [Infinite k] [DecidableEq I] :
    Function.Injective (evalChar (I := I) k) := by
  classical
  intro m m' hmm'
  funext i
  by_contra hne
  have hn : m i - m' i ≠ 0 := sub_ne_zero.mpr hne
  have hN : 0 < (m i - m' i).natAbs := Int.natAbs_pos.mpr hn
  obtain ⟨s, hs⟩ := Infinite.exists_notMem_finset
    (insert (0 : k) (Polynomial.nthRoots (m i - m' i).natAbs (1 : k)).toFinset)
  rw [Finset.mem_insert, not_or, Multiset.mem_toFinset, Polynomial.mem_nthRoots hN] at hs
  let u : kˣ := Units.mk0 s hs.1
  have hprod : ∀ n : I → ℤ, unitChar (Pi.mulSingle i u) (.ofAdd n) = u ^ n i := by
    intro n
    rw [unitChar_apply, Finset.prod_eq_single i]
    · simp
    · intro j _ hj
      simp [Pi.mulSingle_eq_of_ne hj]
    · simp
  have h := congrArg (fun χ : (I → kˣ) →* k => χ (Pi.mulSingle i u)) hmm'
  simp only [evalChar_apply, hprod] at h
  have hu : u ^ (m i - m' i) = 1 := by
    rw [zpow_sub, mul_inv_eq_one]
    exact Units.ext h
  rw [← pow_natAbs_eq_one] at hu
  apply hs.2
  have := congrArg Units.val hu
  simpa [u] using this

/-- **Laurent polynomials are determined by their values on units over an infinite field.** -/
theorem eq_zero_of_forall_evalUnits_eq_zero {k : Type*} [Field k] [Infinite k]
    (Q : AddMonoidAlgebra k (I → ℤ)) (h : ∀ t : I → kˣ, evalUnits k t Q = 0) : Q = 0 := by
  classical
  have hli := (linearIndependent_monoidHom (I → kˣ) k).comp (evalChar k)
    (evalChar_injective k)
  rw [← AddMonoidAlgebra.coeff_eq_zero]
  refine linearIndependent_iff.mp hli Q.coeff ?_
  funext t
  rw [Finsupp.linearCombination_apply, Pi.zero_apply, ← h t, evalUnits_apply]
  simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul,
    evalChar_apply, Algebra.algebraMap_self, RingHom.id_apply]

/-- **Integrality of coefficients from integrality of values** (the evaluation step of
Kaletha–Prasad Lemma B.2.3 for split tori). Let `A` be a valuation ring with fraction field
`K` and infinite residue field. If a Laurent polynomial over `K` takes integral values at every
family of units of `A`, then all of its coefficients are integral. -/
theorem coeff_mem_range_of_forall_evalUnits_mem {A K : Type*} [CommRing A] [IsDomain A]
    [ValuationRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    [Infinite (IsLocalRing.ResidueField A)] (P : AddMonoidAlgebra K (I → ℤ))
    (h : ∀ t : I → Aˣ,
      evalUnits K (fun i => Units.map (algebraMap A K : A →* K) (t i)) P ∈
        Set.range (algebraMap A K))
    (m : I → ℤ) : P.coeff m ∈ Set.range (algebraMap A K) := by
  classical
  let v := ValuationRing.valuation A K
  have hint : ∀ x : K, x ∈ Set.range (algebraMap A K) ↔ v x ≤ 1 := fun x => by
    rw [← Valuation.mem_integer_iff, ValuationRing.mem_integer_iff]
    rfl
  by_cases hP : P.coeff.support = ∅
  · rw [Finsupp.support_eq_empty.mp hP, Finsupp.zero_apply]
    exact ⟨0, map_zero _⟩
  obtain ⟨m₀, hm₀, hmax⟩ := Finset.exists_max_image P.coeff.support (fun m => v (P.coeff m))
    (Finset.nonempty_iff_ne_empty.mpr hP)
  set c := P.coeff m₀ with hc_def
  have hc : c ≠ 0 := Finsupp.mem_support_iff.mp hm₀
  have hvc : v c ≠ 0 := (Valuation.ne_zero_iff v).mpr hc
  -- normalized coefficients
  have hnorm : ∀ m, ∃ a : A, algebraMap A K a = P.coeff m * c⁻¹ := by
    intro m
    rw [← Set.mem_range, hint, map_mul, map_inv₀]
    by_cases hm : m ∈ P.coeff.support
    · exact mul_inv_le_one_of_le₀ (hmax m hm) zero_le
    · rw [Finsupp.notMem_support_iff.mp hm, map_zero, zero_mul]
      exact zero_le
  choose a ha using hnorm
  have ha₀ : a m₀ = 1 := by
    apply IsFractionRing.injective A K
    rw [ha, ← hc_def, mul_inv_cancel₀ hc, map_one]
  let k := IsLocalRing.ResidueField A
  let Q : AddMonoidAlgebra k (I → ℤ) :=
    ∑ m ∈ P.coeff.support, AddMonoidAlgebra.single m (IsLocalRing.residue A (a m))
  have hQ : Q ≠ 0 := by
    intro hQ
    have h0 := congrArg (fun x : AddMonoidAlgebra k (I → ℤ) => x.coeff m₀) hQ
    simp only [Q, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
      AddMonoidAlgebra.coeff_single, Finsupp.single_apply] at h0
    rw [Finset.sum_eq_single m₀ (fun b _ hb => by simp [hb]) (fun h => absurd hm₀ h)] at h0
    simp [ha₀] at h0
  obtain ⟨tbar, htbar⟩ : ∃ tbar : I → kˣ, evalUnits k tbar Q ≠ 0 := by
    by_contra hcon
    exact hQ (eq_zero_of_forall_evalUnits_eq_zero Q fun t =>
      not_not.mp fun h' => hcon ⟨t, h'⟩)
  have hlift : ∀ i, ∃ r : A, IsLocalRing.residue A r = tbar i :=
    fun i => IsLocalRing.residue_surjective _
  choose r hr using hlift
  have hru : ∀ i, IsUnit (r i) := fun i =>
    (IsLocalRing.residue_ne_zero_iff_isUnit _).mp (by rw [hr]; exact (tbar i).ne_zero)
  let t : I → Aˣ := fun i => (hru i).unit
  have ht : ∀ i, Units.map (IsLocalRing.residue A : A →* k) (t i) = tbar i := fun i =>
    Units.ext (hr i)
  let E : A := ∑ m ∈ P.coeff.support, a m * ((unitChar t (.ofAdd m) : Aˣ) : A)
  have hE : IsLocalRing.residue A E = evalUnits k tbar Q := by
    simp only [E, Q, map_sum, map_mul, evalUnits_single, Algebra.algebraMap_self,
      RingHom.id_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    congr 1
    have htbar' : tbar = fun i => Units.map (IsLocalRing.residue A : A →* k) (t i) :=
      funext fun i => (ht i).symm
    rw [htbar', unitChar_map, Units.coe_map]
    rfl
  have hEu : IsUnit E :=
    (IsLocalRing.residue_ne_zero_iff_isUnit _).mp (by rw [hE]; exact htbar)
  have hev : evalUnits K (fun i => Units.map (algebraMap A K : A →* K) (t i)) P =
      c * algebraMap A K E := by
    rw [evalUnits_apply, Finsupp.sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Algebra.algebraMap_self, RingHom.id_apply, unitChar_map, Units.coe_map, map_mul, ha]
    simp only [MonoidHom.coe_coe]
    field_simp
  obtain ⟨b, hb⟩ := h t
  rw [hev] at hb
  have hcint : c ∈ Set.range (algebraMap A K) := by
    refine ⟨b * hEu.unit⁻¹, ?_⟩
    rw [map_mul, hb, mul_assoc, ← map_mul]
    simp
  rw [hint] at hcint ⊢
  by_cases hm : m ∈ P.coeff.support
  · exact (hmax m hm).trans hcint
  · rw [Finsupp.notMem_support_iff.mp hm, map_zero]
    exact zero_le

end Evaluation

end Langlands.Algebra.HopfPointIntegralClosure
