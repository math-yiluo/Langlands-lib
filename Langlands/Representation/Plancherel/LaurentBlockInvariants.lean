import Langlands.Representation.Plancherel.RationalUnramifiedDensity
import Mathlib.RingTheory.Localization.FractionRing

/-! # Laurent fractions invariant under scaling a block of variables -/

noncomputable section

namespace Langlands.Plancherel.LaurentBlockInvariants

open AddMonoidAlgebra

variable {r n : ℕ}

local notation "FirstLaurent" => AddMonoidAlgebra ℂ (Fin r → ℤ)
local notation "ProductLaurent" => AddMonoidAlgebra ℂ ((Fin r → ℤ) × (Fin n → ℤ))
local notation "ProductField" => FractionRing ProductLaurent

/-- Include Laurent polynomials on the first block as functions independent of
the second block. -/
def firstBlock : FirstLaurent →ₐ[ℂ] ProductLaurent :=
  AddMonoidAlgebra.mapDomainAlgHom ℂ ℂ (AddMonoidHom.inl (Fin r → ℤ) (Fin n → ℤ))

@[simp]
theorem firstBlock_single (a : Fin r → ℤ) (x : ℂ) :
    firstBlock (n := n) (single a x) = single (a, 0) x := by
  simp [firstBlock]

/-- Substitute complex units for the coordinates in the second block. -/
def specialize (c : Fin n → ℂˣ) : ProductLaurent →+* FirstLaurent :=
  (AddMonoidAlgebra.mapRingHom (Fin r → ℤ) (finiteLaurentEvaluation c).toRingHom).comp
    AddMonoidAlgebra.curryRingEquiv.toRingHom

private theorem specialize_single (c : Fin n → ℂˣ)
    (a : Fin r → ℤ) (b : Fin n → ℤ) (x : ℂ) :
    specialize c (single (a, b) x) = single a (x * ((∏ i, c i ^ b i : ℂˣ) : ℂ)) := by
  simp [specialize, AddMonoidAlgebra.curryRingEquiv_single]

@[simp]
theorem specialize_firstBlock (c : Fin n → ℂˣ) (p : FirstLaurent) :
    specialize c (firstBlock p) = p := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp [hp, hq]
  | single a x => simp [specialize_single]

theorem firstBlock_injective : Function.Injective (firstBlock (r := r) (n := n)) :=
  (show Function.LeftInverse (specialize (1 : Fin n → ℂˣ)) firstBlock from
    specialize_firstBlock 1).injective

private theorem eq_zero_of_specialize {p : ProductLaurent}
    (hp : ∀ c, specialize c p = 0) : p = 0 := by
  apply AddMonoidAlgebra.curryRingEquiv.injective
  rw [map_zero]
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro a
  rw [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  apply finiteLaurent_eq_zero_of_eval_on_open _ isOpen_univ Set.univ_nonempty
  intro c _
  have hc := congrArg (fun q : FirstLaurent => q.coeff a) (hp c)
  simp only [specialize, RingHom.comp_apply, AddMonoidAlgebra.coeff_mapRingHom,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hc
  exact hc

private theorem specialize_scaling
    (s : (Fin n → ℂˣ) → ProductLaurent ≃ₐ[ℂ] ProductLaurent)
    (hs : ∀ c (m : (Fin r → ℤ) × (Fin n → ℤ)) (a : ℂ),
      s c (single m a) = single m (a * ((∏ i, c i ^ m.2 i : ℂˣ) : ℂ)))
    (a c : Fin n → ℂˣ) (p : ProductLaurent) :
    specialize a (s c p) = specialize (c * a) p := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp [hp, hq]
  | single m x =>
    rcases m with ⟨u, v⟩
    rw [hs, specialize_single, specialize_single]
    simp only [Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib, Units.val_mul, mul_assoc]

/-- A Laurent fraction fixed by every scaling of the second block has a
presentation by Laurent polynomials on the first block. The actions on the
Laurent algebra and on its fraction field can come from any compatible chart. -/
theorem exists_firstBlock_fraction_of_fixed
    (s : (Fin n → ℂˣ) → ProductLaurent ≃ₐ[ℂ] ProductLaurent)
    (hs : ∀ c (m : (Fin r → ℤ) × (Fin n → ℤ)) (a : ℂ),
      s c (single m a) = single m (a * ((∏ i, c i ^ m.2 i : ℂˣ) : ℂ)))
    (σ : (Fin n → ℂˣ) → ProductField ≃+* ProductField)
    (hσ : ∀ c p, σ c (algebraMap ProductLaurent ProductField p) =
      algebraMap ProductLaurent ProductField (s c p))
    (f : ProductField) (hf : ∀ c, σ c f = f) :
    ∃ p q : FirstLaurent, q ≠ 0 ∧
      f = algebraMap ProductLaurent ProductField (firstBlock p) /
        algebraMap ProductLaurent ProductField (firstBlock q) := by
  let ι := algebraMap ProductLaurent ProductField
  have hι : Function.Injective ι := IsFractionRing.injective _ _
  obtain ⟨p, q, hq, hpq⟩ := IsFractionRing.div_surjective ProductLaurent f
  have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
  have hqι : ι q ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hq
  have hcross (c : Fin n → ℂˣ) : s c p * q = p * s c q := by
    have he := hf c
    rw [← hpq, map_div₀, hσ, hσ] at he
    have hq' : ι (s c q) ≠ 0 := by
      simpa only [ne_eq, map_eq_zero_iff _ hι, map_eq_zero_iff _ (s c).injective] using hq0
    exact hι (by simpa only [map_mul] using (div_eq_div_iff hq' hqι).mp he)
  obtain ⟨a, ha⟩ : ∃ c : Fin n → ℂˣ, specialize c q ≠ 0 := by
    by_contra! h
    exact hq0 (eq_zero_of_specialize h)
  refine ⟨specialize a p, specialize a q, ha, ?_⟩
  have hprod : p * firstBlock (specialize a q) = firstBlock (specialize a p) * q := by
    apply sub_eq_zero.mp
    apply eq_zero_of_specialize
    intro d
    have he := congrArg (specialize a) (hcross (d * a⁻¹))
    simp only [map_mul, specialize_scaling s hs, inv_mul_cancel_right] at he
    simpa only [map_sub, map_mul, specialize_firstBlock, sub_eq_zero] using he
  have ha' : ι (firstBlock (specialize a q)) ≠ 0 := by
    simpa only [Function.comp_apply, map_zero] using (hι.comp firstBlock_injective).ne ha
  rw [← hpq]
  apply (div_eq_div_iff hqι ha').2
  simpa only [map_mul] using congrArg ι hprod

end Langlands.Plancherel.LaurentBlockInvariants
