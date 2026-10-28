import Langlands.Representation.RankinSelberg.IwasawaTorusPartitionStatement

/-!
# Proof of the measurable uniformizer-coset partition of the diagonal torus

The valuation lemmas decompose every field unit uniquely as an integer power of
a uniformizing element times an integral unit. A group-theoretic lemma turns
such a decomposition, for a left-invariant measure giving the units mass one,
into the full coset partition of the finite product. The resulting countable
coset cover also supplies σ-finiteness of the normalized multiplicative Haar
measure.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory GeneralLinear

universe uF

section Valuation

variable {E : Type*} [Field E] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation E Γ₀)

/-- An actual integral unit has valuation one. -/
theorem valuation_eq_one_of_mem_integralUnits {a : Eˣ} (ha : a ∈ integralUnits v.integer) :
    v (a : E) = 1 := by
  obtain ⟨h, hi⟩ := (mem_integralUnits v.integer a).mp ha
  rw [Valuation.mem_integer_iff] at h hi
  rw [Units.val_inv_eq_inv_val, map_inv₀] at hi
  exact le_antisymm h ((inv_le_one₀ (Iwasawa.valuation_pos v a)).mp hi)

/-- A unit of valuation one is an actual integral unit. -/
theorem mem_integralUnits_of_valuation_eq_one {a : Eˣ} (ha : v (a : E) = 1) :
    a ∈ integralUnits v.integer := by
  rw [mem_integralUnits, Valuation.mem_integer_iff, Valuation.mem_integer_iff,
    Units.val_inv_eq_inv_val, map_inv₀, ha, inv_one]
  exact ⟨le_rfl, le_rfl⟩

variable {v}

/-- Uniqueness: the exponent of a uniformizer coset of the integral units is determined
by the coset. -/
theorem zpow_eq_of_mul_integralUnits {ϖ : Eˣ} (hϖ : Iwasawa.IsUniformizingElement v ϖ)
    {k k' : ℤ} {u u' : Eˣ} (hu : u ∈ integralUnits v.integer)
    (hu' : u' ∈ integralUnits v.integer) (h : ϖ ^ k * u = ϖ ^ k' * u') : k = k' := by
  have h1 := congrArg (fun x : Eˣ => v (x : E)) h
  simp only [Units.val_mul, map_mul, Units.val_zpow_eq_zpow_val, map_zpow₀,
    valuation_eq_one_of_mem_integralUnits v hu, valuation_eq_one_of_mem_integralUnits v hu',
    mul_one] at h1
  exact (zpow_right_strictAnti₀ (Iwasawa.valuation_pos v ϖ) hϖ.1).injective h1

/-- Existence: every unit lies in a uniformizer coset of the integral units. -/
theorem exists_zpow_mul_integralUnits {ϖ : Eˣ} (hϖ : Iwasawa.IsUniformizingElement v ϖ)
    (a : Eˣ) : ∃ k : ℤ, ∃ u ∈ integralUnits v.integer, a = ϖ ^ k * u := by
  obtain ⟨k, hk⟩ := hϖ.2 (a : E) a.ne_zero
  refine ⟨k, (ϖ ^ k)⁻¹ * a, mem_integralUnits_of_valuation_eq_one v ?_,
    (mul_inv_cancel_left _ _).symm⟩
  rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, Units.val_zpow_eq_zpow_val,
    map_zpow₀, hk, inv_mul_cancel₀ (zpow_ne_zero _ (Iwasawa.valuation_pos v ϖ).ne')]

end Valuation

section Group

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]

/-- A left-invariant measure is σ-finite when the integer-power translates of one set of
finite measure cover the group. -/
theorem sigmaFinite_of_zpow_cover (μ : Measure G) [μ.IsMulLeftInvariant] (K : Set G)
    (hK : μ K ≠ ⊤) (ϖ : G) (hcover : ∀ a : G, ∃ k : ℤ, ∃ u ∈ K, a = ϖ ^ k * u) :
    SigmaFinite μ := by
  refine Measure.sigmaFinite_of_countable
    (S := Set.range fun k : ℤ => (fun x : G => (ϖ ^ k)⁻¹ * x) ⁻¹' K)
    (Set.countable_range _) ?_ ?_
  · rintro _ ⟨k, rfl⟩
    rw [measure_preimage_mul]
    exact hK.lt_top
  · rw [Set.sUnion_range, Set.eq_univ_iff_forall]
    intro a
    obtain ⟨k, u, hu, rfl⟩ := hcover a
    exact Set.mem_iUnion.2 ⟨k, by simpa using hu⟩

/-- The coset partition of a finite product, for a left-invariant σ-finite measure, a
measurable set `K` of mass one, and an element `ϖ` such that every element is uniquely
`ϖ ^ k * u` with `u ∈ K`. -/
theorem zpow_coset_partition (μ : Measure G) [μ.IsMulLeftInvariant] [SigmaFinite μ]
    (K : Set G) (hK : MeasurableSet K) (hK1 : μ K = 1) (ϖ : G)
    (hex : ∀ a : G, ∃ k : ℤ, ∃ u ∈ K, a = ϖ ^ k * u)
    (huniq : ∀ (k k' : ℤ) (u u' : G), u ∈ K → u' ∈ K → ϖ ^ k * u = ϖ ^ k' * u' → k = k')
    (m : ℕ) :
    let A := Fin m → G
    let da : Measure A := Measure.pi fun _ : Fin m => μ
    let U : Set A := {u : A | ∀ i, u i ∈ K}
    let t : (Fin m → ℤ) → A := fun lam i => ϖ ^ lam i
    let C : (Fin m → ℤ) → Set A := fun lam => (fun u : A => t lam * u) '' U
    MeasurableSet U ∧ da U = 1 ∧
      (∀ lam : Fin m → ℤ, MeasurableSet (C lam) ∧ da (C lam) = 1 ∧
        Measure.map (fun u : A => t lam * u) (da.restrict U) = da.restrict (C lam)) ∧
      Pairwise (fun lam lam' : Fin m → ℤ => Disjoint (C lam) (C lam')) ∧
      (⋃ lam : Fin m → ℤ, C lam) = Set.univ := by
  intro A da U t C
  have hUpi : U = Set.univ.pi fun _ : Fin m => K := by
    ext u
    exact Set.mem_univ_pi.symm
  have hU : MeasurableSet U := hUpi ▸ MeasurableSet.univ_pi fun _ => hK
  have hUone : da U = 1 := by
    rw [hUpi]
    change (Measure.pi fun _ : Fin m => μ) (Set.univ.pi fun _ : Fin m => K) = 1
    rw [Measure.pi_pi, hK1, Finset.prod_const_one]
  have hCpre (lam : Fin m → ℤ) : C lam = (fun a : A => (t lam)⁻¹ * a) ⁻¹' U :=
    Set.image_mul_left
  have hC (lam : Fin m → ℤ) : MeasurableSet (C lam) := by
    rw [hCpre]
    exact measurable_const_mul _ hU
  refine ⟨hU, hUone, fun lam => ⟨hC lam, ?_, ?_⟩, ?_, ?_⟩
  · rw [hCpre, measure_preimage_mul, hUone]
  · have hpre : (fun u : A => t lam * u) ⁻¹' C lam = U :=
      Set.preimage_image_eq U (mul_right_injective (t lam))
    have h := Measure.restrict_map (μ := da) (measurable_const_mul (t lam)) (hC lam)
    rw [map_mul_left_eq_self, hpre] at h
    exact h.symm
  · intro lam lam' hne
    rw [Set.disjoint_left]
    rintro _ ⟨u, hu, rfl⟩ ⟨u', hu', h⟩
    apply hne
    funext i
    exact (huniq _ _ _ _ (hu' i) (hu i) (congrFun h i)).symm
  · rw [Set.eq_univ_iff_forall]
    intro a
    choose k u hu ha using fun i => hex (a i)
    exact Set.mem_iUnion.2 ⟨k, u, hu, funext fun i => (ha i).symm⟩

end Group

/-- The diagonal torus is the disjoint union of the measurable uniformizer cosets of its
integral units, each of normalized product Haar mass one. -/
theorem iwasawaTorusPartition : IwasawaTorusPartitionStatement.{uF} := by
  intro p _ F T m
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let : MeasurableSpace F.Carrierˣ := borel F.Carrierˣ
  have : BorelSpace F.Carrierˣ := ⟨rfl⟩
  intro ϖ hϖ
  have hK : MeasurableSet
      (integralUnits (ValuativeRel.valuation F.Carrier).integer : Set F.Carrierˣ) :=
    (integralUnits_isOpen _ Valuation.isOpen_integer).measurableSet
  have hcover := exists_zpow_mul_integralUnits hϖ
  have : SigmaFinite (localMultiplicativeHaar F.Carrier) :=
    sigmaFinite_of_zpow_cover _ _ (by rw [localMultiplicativeHaar_integerUnits]; simp) ϖ
      hcover
  exact zpow_coset_partition (localMultiplicativeHaar F.Carrier) _ hK
    (localMultiplicativeHaar_integerUnits F.Carrier) ϖ hcover
    (fun _ _ _ _ hu hu' h => zpow_eq_of_mul_integralUnits hϖ hu hu' h) m

end Langlands.RankinSelberg
