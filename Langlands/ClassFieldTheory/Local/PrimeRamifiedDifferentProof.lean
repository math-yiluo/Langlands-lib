import Langlands.ClassFieldTheory.Local.PrimeRamifiedDifferentStatement
import Langlands.LocalFactor.Ramification.UniformizerCriterionProof
import Langlands.ClassFieldTheory.Local.NYLL.RelativeIntegerStructureProof
import Langlands.ClassFieldTheory.Local.TotallyRamifiedIntegerMonogeneityProof
import Langlands.ClassFieldTheory.Local.PrimeBreakUnramifiedBaseChangeSupport
import Mathlib.RingTheory.Adjoin.PowerBasis
import Mathlib.RingTheory.Coprime.Lemmas

noncomputable section

open scoped Classical

namespace Langlands.LocalClassField

universe u v

/-- The supplied single-break pattern gives the exact order of the displacement
of every uniformizer by a nonidentity automorphism. -/
theorem uniformizer_displacement_ord_of_single_break
    {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} {L : PadicField.{v} p}
    [Algebra F.Carrier L.Carrier] [IsScalarTower (Padic p) F.Carrier L.Carrier]
    (T : F.TopologicalData) (S : L.TopologicalData)
    (hsurj : Function.Surjective (PadicField.TopologicalData.relativeResidueMap T S))
    (t : ℕ)
    (hpat : ∀ i : ℕ, Ramification.Padic.lowerRamificationGroup S F.Carrier i =
      if i ≤ t then ⊤ else ⊥)
    (π : L.Carrier) (hπ : S.ord π = 1)
    (σ : L.Carrier ≃ₐ[F.Carrier] L.Carrier) (hσ : σ ≠ 1) :
    σ π - π ≠ 0 ∧ S.ord (σ π - π) = (t + 1 : ℤ) := by
  have hbelow : σ ∈ Ramification.Padic.lowerRamificationGroup S F.Carrier t := by
    simp only [hpat t, le_refl, ite_true, Subgroup.mem_top]
  have habove : σ ∉ Ramification.Padic.lowerRamificationGroup S F.Carrier (t + 1) := by
    simp only [hpat (t + 1), Nat.not_succ_le_self, ite_false, Subgroup.mem_bot]
    exact hσ
  rw [Ramification.Padic.mem_lowerRamificationGroup_iff_uniformizer T S hsurj π hπ σ t]
    at hbelow
  rw [Ramification.Padic.mem_lowerRamificationGroup_iff_uniformizer T S hsurj π hπ σ
    (t + 1)] at habove
  have hne : σ π - π ≠ 0 := fun hz => habove (Or.inl hz)
  have hlo := hbelow.resolve_left hne
  have hhi : ¬ ((t + 1 : ℕ) + 1 : ℤ) ≤ S.ord (σ π - π) :=
    fun h => habove (Or.inr h)
  exact ⟨hne, by push_cast at hhi; omega⟩

section PrimitiveElement

open Polynomial

variable {K E : Type*} [Field K] [Field E] [Algebra K E]
  [FiniteDimensional K E] [IsGalois K E]

/-- The minimal polynomial of a primitive element is the product of its actual
Galois conjugates. -/
theorem minpoly_map_eq_prod_automorphisms_of_adjoin (x : E)
    (hx : Algebra.adjoin K {x} = ⊤) :
    (minpoly K x).map (algebraMap K E) =
      ∏ σ : E ≃ₐ[K] E, (X - C (σ x)) := by
  classical
  let pb := PowerBasis.ofAdjoinEqTop (Algebra.IsIntegral.isIntegral x) hx
  have hinj : Function.Injective (fun σ : E ≃ₐ[K] E => σ x) := by
    intro σ τ h
    ext z
    exact congrArg (fun f : E →ₐ[K] E => f z)
      (pb.algHom_ext (f := σ.toAlgHom) (g := τ.toAlgHom) (by simpa [pb] using h))
  have hdvd : (∏ σ : E ≃ₐ[K] E, (X - C (σ x))) ∣
      (minpoly K x).map (algebraMap K E) := by
    apply Fintype.prod_dvd_of_coprime (pairwise_coprime_X_sub_C hinj)
    intro σ
    rw [dvd_iff_isRoot, IsRoot.def, eval_map_algebraMap, aeval_algHom_apply,
      minpoly.aeval, map_zero]
  apply eq_of_monic_of_dvd_of_natDegree_le
    (monic_prod_of_monic _ _ fun σ _ => monic_X_sub_C (σ x))
    ((minpoly.monic (Algebra.IsIntegral.isIntegral x)).map _) hdvd
  simp only [natDegree_map, natDegree_finsetProd_X_sub_C_eq_card, Finset.card_univ,
    Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank]
  exact le_of_eq (by simpa [pb] using pb.natDegree_minpoly.trans pb.finrank.symm)

/-- At a primitive element, the derivative of the minimal polynomial is the
product of differences from the nonidentity Galois conjugates. -/
theorem aeval_derivative_minpoly_eq_prod_automorphisms_of_adjoin (x : E)
    (hx : Algebra.adjoin K {x} = ⊤) :
    aeval x (derivative (minpoly K x)) =
      ∏ σ ∈ Finset.univ.erase (1 : E ≃ₐ[K] E), (x - σ x) := by
  classical
  have hfact : (minpoly K x).map (algebraMap K E) =
      (X - C x) * ∏ σ ∈ Finset.univ.erase (1 : E ≃ₐ[K] E), (X - C (σ x)) := by
    rw [minpoly_map_eq_prod_automorphisms_of_adjoin x hx,
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ (1 : E ≃ₐ[K] E))]
    rfl
  rw [← eval_map_algebraMap, ← derivative_map, hfact, derivative_mul]
  simp [eval_prod]

end PrimitiveElement

section FractionGenerator

variable {A B K E : Type*} [CommRing A] [CommRing B] [Field K] [Field E]
  [Algebra A B] [Algebra A K] [Algebra A E] [Algebra B E] [Algebra K E]
  [IsScalarTower A B E] [IsScalarTower A K E] [IsFractionRing B E]
  [FiniteDimensional K E]

/-- Generation of an integer ring implies generation of its fraction field
over the base field. -/
theorem adjoin_fractionField_eq_top_of_integer_adjoin (x : B)
    (hx : Algebra.adjoin A {x} = ⊤) :
    Algebra.adjoin K {algebraMap B E x} = ⊤ := by
  let C := Algebra.adjoin K {algebraMap B E x}
  have hle : Algebra.adjoin A {x} ≤
      (C.restrictScalars A).comap (IsScalarTower.toAlgHom A B E) := by
    apply Algebra.adjoin_le
    intro z hz
    rcases Set.mem_singleton_iff.mp hz with rfl
    exact Algebra.subset_adjoin (Set.mem_singleton _)
  have hmem (b : B) : algebraMap B E b ∈ C := by
    exact hle (by simp [hx])
  apply top_unique
  intro y _
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective B y
  simpa only [div_eq_mul_inv] using C.mul_mem (hmem a)
    ((Algebra.IsIntegral.isIntegral (R := K) (algebraMap B E b)).inv_mem (hmem b))

end FractionGenerator

/-- For the actual relative integer rings, an integer generator gives the
different as the product of its differences from the nonidentity conjugates. -/
theorem different_eq_span_prod_automorphisms_of_integer_adjoin
    {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} {L : PadicField.{v} p}
    [Algebra F.Carrier L.Carrier] [IsScalarTower (Padic p) F.Carrier L.Carrier]
    [FiniteDimensional F.Carrier L.Carrier] [IsGalois F.Carrier L.Carrier]
    (T : F.TopologicalData) (S : L.TopologicalData) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := S.topology
    letI := S.valuativeRel
    letI := S.localField
    letI := PadicField.TopologicalData.relativeIntegerAlgebra T S
    letI := PadicField.TopologicalData.relativeIntegerFieldAlgebra (E := L) T
    haveI := PadicField.TopologicalData.relativeIntegerFieldTower (E := L) T
    haveI := PadicField.TopologicalData.relativeIntegerTower T S
    haveI := PadicField.TopologicalData.relativeIntegerAlgebra_isTorsionFree T S
    ∀ x : S.Integers, Algebra.adjoin T.Integers {x} = ⊤ →
      differentIdeal T.Integers S.Integers =
        Ideal.span {∏ σ ∈ Finset.univ.erase (1 : L.Carrier ≃ₐ[F.Carrier] L.Carrier),
          (x - Ramification.Padic.integerAutomorphism S F.Carrier σ x)} := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := S.topology
  let := S.valuativeRel
  let := S.localField
  let := PadicField.TopologicalData.relativeIntegerAlgebra T S
  let := PadicField.TopologicalData.relativeIntegerFieldAlgebra (E := L) T
  have := PadicField.TopologicalData.relativeIntegerFieldTower (E := L) T
  have := PadicField.TopologicalData.relativeIntegerTower T S
  have := PadicField.TopologicalData.relativeIntegerAlgebra_isTorsionFree T S
  have := (NYLL.relativeIntegerStructure p F L T S).1
  have := (NYLL.relativeIntegerStructure p F L T S).2
  intro x hx
  have hfield := adjoin_fractionField_eq_top_of_integer_adjoin
    (K := F.Carrier) (E := L.Carrier) x hx
  have hder :
      Polynomial.aeval x (Polynomial.derivative (minpoly T.Integers x)) =
        ∏ σ ∈ Finset.univ.erase (1 : L.Carrier ≃ₐ[F.Carrier] L.Carrier),
          (x - Ramification.Padic.integerAutomorphism S F.Carrier σ x) := by
    apply (IsFractionRing.injective S.Integers L.Carrier)
    rw [← Polynomial.aeval_algebraMap_apply,
      ← Polynomial.aeval_map_algebraMap F.Carrier, ← Polynomial.derivative_map,
      ← minpoly.isIntegrallyClosed_eq_field_fractions F.Carrier L.Carrier
        (IsIntegralClosure.isIntegral T.Integers L.Carrier x),
      aeval_derivative_minpoly_eq_prod_automorphisms_of_adjoin _ hfield]
    simp only [map_prod, map_sub]
    rfl
  have hcon := conductor_mul_differentIdeal T.Integers F.Carrier L.Carrier x hfield
  rw [conductor_eq_top_of_adjoin_eq_top hx, Ideal.top_mul, hder] at hcon
  exact hcon

/-- The principal ideal of a nonzero integer is the maximal-ideal power given
by its supplied normalized order. -/
theorem span_singleton_eq_maximalIdeal_pow_of_ord
    {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)
    (d : T.Integers) (hd : (d : F.Carrier) ≠ 0) (n : ℕ)
    (hord : T.ord (d : F.Carrier) = n) :
    Ideal.span {d} = IsLocalRing.maximalIdeal T.Integers ^ n := by
  ext a
  rw [Ideal.mem_span_singleton,
    T.mem_maximalIdeal_pow_iff_ord T.uniformizer T.ord_uniformizer n]
  constructor
  · rintro ⟨c, rfl⟩
    by_cases hc : (c : F.Carrier) = 0
    · left
      change (d : F.Carrier) * (c : F.Carrier) = 0
      rw [hc, mul_zero]
    · right
      change (n : ℤ) ≤ T.ord ((d : F.Carrier) * (c : F.Carrier))
      rw [T.ord_mul hd hc, hord]
      have := (T.mem_integers_iff_zero_le_ord hc).mp c.property
      omega
  · intro ha
    rcases ha with ha | ha
    · rw [show a = 0 from Subtype.ext ha]
      exact dvd_zero _
    · by_cases ha0 : (a : F.Carrier) = 0
      · rw [show a = 0 from Subtype.ext ha0]
        exact dvd_zero _
      have hq : (a : F.Carrier) / (d : F.Carrier) ∈ T.Integers := by
        rw [T.mem_integers_iff_zero_le_ord (div_ne_zero ha0 hd), div_eq_mul_inv,
          T.ord_mul ha0 (inv_ne_zero hd), T.ord_inv, hord]
        omega
      refine ⟨⟨_, hq⟩, Subtype.ext ?_⟩
      change (a : F.Carrier) = (d : F.Carrier) * ((a : F.Carrier) / (d : F.Carrier))
      exact (mul_div_cancel₀ _ hd).symm

/-- The different formula assembled from actual integer generation and the
supplied single-break pattern. -/
theorem different_eq_of_integer_adjoin_and_single_break
    {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} {L : PadicField.{v} p}
    [Algebra F.Carrier L.Carrier] [IsScalarTower (Padic p) F.Carrier L.Carrier]
    [FiniteDimensional F.Carrier L.Carrier] [IsGalois F.Carrier L.Carrier]
    (T : F.TopologicalData) (S : L.TopologicalData)
    (hsurj : Function.Surjective (PadicField.TopologicalData.relativeResidueMap T S))
    (t : ℕ)
    (hpat : ∀ i : ℕ, Ramification.Padic.lowerRamificationGroup S F.Carrier i =
      if i ≤ t then ⊤ else ⊥)
    (π : L.Carrier) (hπ : S.ord π = 1) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := S.topology
    letI := S.valuativeRel
    letI := S.localField
    letI := PadicField.TopologicalData.relativeIntegerAlgebra T S
    letI := PadicField.TopologicalData.relativeIntegerFieldAlgebra (E := L) T
    haveI := PadicField.TopologicalData.relativeIntegerFieldTower (E := L) T
    haveI := PadicField.TopologicalData.relativeIntegerTower T S
    haveI := PadicField.TopologicalData.relativeIntegerAlgebra_isTorsionFree T S
    Algebra.adjoin T.Integers {S.coordinateUniformizer π hπ} = ⊤ →
      differentIdeal T.Integers S.Integers =
        IsLocalRing.maximalIdeal S.Integers ^
          ((t + 1) * (Module.finrank F.Carrier L.Carrier - 1)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := S.topology
  let := S.valuativeRel
  let := S.localField
  let := PadicField.TopologicalData.relativeIntegerAlgebra T S
  let := PadicField.TopologicalData.relativeIntegerFieldAlgebra (E := L) T
  have := PadicField.TopologicalData.relativeIntegerFieldTower (E := L) T
  have := PadicField.TopologicalData.relativeIntegerTower T S
  have := PadicField.TopologicalData.relativeIntegerAlgebra_isTorsionFree T S
  intro hgen
  let w := S.coordinateUniformizer π hπ
  let G := Finset.univ.erase (1 : L.Carrier ≃ₐ[F.Carrier] L.Carrier)
  have hfactor (σ : L.Carrier ≃ₐ[F.Carrier] L.Carrier) (hσ : σ ∈ G) :
      Ideal.span {w - Ramification.Padic.integerAutomorphism S F.Carrier σ w} =
        IsLocalRing.maximalIdeal S.Integers ^ (t + 1) := by
    have hσne : σ ≠ 1 := (Finset.mem_erase.mp hσ).1
    obtain ⟨hne, hord⟩ :=
      uniformizer_displacement_ord_of_single_break T S hsurj t hpat π hπ σ hσne
    have hcoe : ((Ramification.Padic.integerAutomorphism S F.Carrier σ w - w :
        S.Integers) : L.Carrier) = σ π - π := by
      change σ (w : L.Carrier) - (w : L.Carrier) = _
      simp only [w, S.coordinateUniformizer_coe]
    rw [← neg_sub (Ramification.Padic.integerAutomorphism S F.Carrier σ w) w,
      Ideal.span_singleton_neg]
    exact span_singleton_eq_maximalIdeal_pow_of_ord S _ (by rwa [hcoe]) (t + 1)
      (by simpa only [hcoe, Nat.cast_add, Nat.cast_one] using hord)
  rw [different_eq_span_prod_automorphisms_of_integer_adjoin T S w hgen,
    ← Ideal.prod_span_singleton]
  change (∏ σ ∈ G, Ideal.span
    {w - Ramification.Padic.integerAutomorphism S F.Carrier σ w}) = _
  rw [Finset.prod_eq_pow_card hfactor, ← pow_mul]
  congr 2
  simp only [G, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank]

/-- The actual different at the supplied prime ramification break. -/
theorem primeRamifiedDifferent : PrimeRamifiedDifferent.{u,v} := by
  intro p hp F L hFL hbase hfinite hgalois
  let TF := F.canonicalTopologicalData
  let TL := L.canonicalTopologicalData
  let := TF.topology
  let := TF.valuativeRel
  let := TF.localField
  let := TL.topology
  let := TL.valuativeRel
  let := TL.localField
  let := PadicField.TopologicalData.relativeIntegerAlgebra TF TL
  let := PadicField.TopologicalData.relativeIntegerFieldAlgebra (E := L) TF
  have := PadicField.TopologicalData.relativeIntegerFieldTower (E := L) TF
  have := PadicField.TopologicalData.relativeIntegerTower TF TL
  have := PadicField.TopologicalData.relativeIntegerAlgebra_isTorsionFree TF TL
  dsimp only
  intro _hprime htotal t hpat
  apply different_eq_of_integer_adjoin_and_single_break TF TL
    (primeBreakResidueMap_surjective_of_total F L htotal) t hpat
    TL.uniformizer TL.ord_uniformizer
  exact totallyRamifiedIntegerMonogeneity p F L htotal TL.uniformizer TL.ord_uniformizer

end Langlands.LocalClassField
