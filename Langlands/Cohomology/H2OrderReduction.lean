import Langlands.Cohomology.H2InflationProof
import Langlands.Cohomology.SylowDetectionProof
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.Sylow

/-! # Order bounds for second cohomology from prime-index sections -/

noncomputable section

open CategoryTheory

namespace Langlands.Cohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]

/-- Cohomology restricted to a subgroup of a subgroup is cohomology restricted to its image. -/
def resSubgroupMapIso (A : Rep.{u} k G) (H : Subgroup G) (K : Subgroup H) (n : ℕ) :
    groupCohomology (Rep.res K.subtype (Rep.res H.subtype A)) n ≅
      groupCohomology (Rep.res (K.map H.subtype).subtype A) n :=
  groupCohomology.mapIso (K.equivMapOfInjective H.subtype H.subtype_injective)
    (LinearEquiv.refl k _) (fun _ => rfl) n

/-- In an exact sequence `0 → X₁ → X₂ → X₃` with finite ends, the middle term is finite and
its order divides the product of the outer orders. -/
theorem finite_card_dvd_of_exact {R X₁ X₂ X₃ : Type*} [Ring R] [AddCommGroup X₁]
    [AddCommGroup X₂] [AddCommGroup X₃] [Module R X₁] [Module R X₂] [Module R X₃]
    (f : X₁ →ₗ[R] X₂) (g : X₂ →ₗ[R] X₃) (hf : Function.Injective f)
    (hfg : LinearMap.range f = LinearMap.ker g) [Finite X₁] [Finite X₃] :
    Finite X₂ ∧ Nat.card X₂ ∣ Nat.card X₁ * Nat.card X₃ := by
  have hker : Nat.card (LinearMap.ker g) = Nat.card X₁ := by
    rw [← hfg]
    exact (Nat.card_congr (LinearEquiv.ofInjective f hf).toEquiv).symm
  have hquot : Nat.card (X₂ ⧸ (LinearMap.ker g).toAddSubgroup) =
      Nat.card (LinearMap.range g) :=
    Nat.card_congr (g.quotKerEquivRange).toEquiv
  have hcard : Nat.card X₂ = Nat.card (LinearMap.range g) * Nat.card X₁ := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (LinearMap.ker g).toAddSubgroup,
      hquot, ← hker]
    rfl
  have hrange : Nat.card (LinearMap.range g) ∣ Nat.card X₃ :=
    AddSubgroup.card_addSubgroup_dvd_card (LinearMap.range g).toAddSubgroup
  have hpos : Nat.card X₂ ≠ 0 := by
    rw [hcard]
    exact mul_ne_zero (ne_zero_of_dvd_ne_zero Nat.card_pos.ne' hrange) Nat.card_pos.ne'
  refine ⟨(Nat.card_ne_zero.mp hpos).2, ?_⟩
  rw [hcard, mul_comm]
  exact mul_dvd_mul_left _ hrange

variable (A : Rep.{u} k G)

/-- Degree-one vanishing on every subgroup. -/
def H1VanishesOnSubgroups : Prop :=
  ∀ H : Subgroup G, Subsingleton (groupCohomology (Rep.res H.subtype A) 1)

/-- The prime-index layer bound: for every subgroup and every normal subgroup of prime index,
the degree-two cohomology of the quotient with coefficients in the invariants is finite with
order dividing the index. -/
def H2PrimeLayerBound : Prop :=
  ∀ (H : Subgroup G) (N : Subgroup H) [N.Normal], N.index.Prime →
    Finite (groupCohomology ((Rep.res H.subtype A).quotientToInvariants N) 2) ∧
      Nat.card (groupCohomology ((Rep.res H.subtype A).quotientToInvariants N) 2) ∣ N.index

variable {A}

/-- The `p`-subgroup case, by induction through normal subgroups of index `p`. -/
theorem finite_card_dvd_of_isPGroup [Finite G] (h1 : H1VanishesOnSubgroups A)
    (hcyc : H2PrimeLayerBound A) (p : ℕ) [hp : Fact p.Prime] (H : Subgroup G)
    (hH : IsPGroup p H) :
    Finite (groupCohomology (Rep.res H.subtype A) 2) ∧
      Nat.card (groupCohomology (Rep.res H.subtype A) 2) ∣ Nat.card H := by
  induction hm : Nat.card H using Nat.strong_induction_on generalizing H with
  | _ m ih =>
  rcases hH.card_eq_or_dvd with h1H | hpH
  · have : Subsingleton H := (Nat.card_eq_one_iff_unique.mp h1H).1
    have : Subsingleton (groupCohomology (Rep.res H.subtype A) 2) :=
      ModuleCat.subsingleton_of_isZero
        (isZero_groupCohomology_succ_of_subsingleton (Rep.res H.subtype A) 1)
    refine ⟨inferInstance, ?_⟩
    rw [Nat.card_of_subsingleton (0 : groupCohomology (Rep.res H.subtype A) 2)]
    exact one_dvd _
  · have : Group.IsNilpotent H := hH.isNilpotent
    obtain ⟨N, hNidx, hNnormal⟩ := Group.IsNilpotent.exists_normal_index_eq_of_dvd_card hpH
    let N' : Subgroup G := N.map H.subtype
    have hN1 : Subsingleton (groupCohomology (Rep.res N.subtype (Rep.res H.subtype A)) 1) :=
      (resSubgroupMapIso A H N 1).toLinearEquiv.toEquiv.subsingleton_congr.mpr (h1 N')
    obtain ⟨hinj, hex⟩ :=
      h2InflationRestrictionExactness k H (Rep.res H.subtype A) N hN1
    have hcardN : Nat.card N' = Nat.card N :=
      (Nat.card_congr (N.equivMapOfInjective H.subtype H.subtype_injective).toEquiv).symm
    have hHN : Nat.card H = Nat.card N * p := by
      rw [← hNidx, Subgroup.card_mul_index]
    have hlt : Nat.card N' < m := by
      rw [hcardN, ← hm, hHN]
      exact lt_mul_of_one_lt_right Nat.card_pos hp.out.one_lt
    obtain ⟨fin3, dvd3⟩ := ih _ hlt N' ((hH.to_subgroup N).map H.subtype) rfl
    have e3 := (resSubgroupMapIso A H N 2).toLinearEquiv.toEquiv
    have : Finite (groupCohomology (Rep.res N.subtype (Rep.res H.subtype A)) 2) :=
      Finite.of_equiv _ e3.symm
    obtain ⟨fin1, dvd1⟩ := hcyc H N (hNidx ▸ hp.out)
    have : Finite (groupCohomology.HInfRes (Rep.res H.subtype A) N 2).X₁ := fin1
    have : Finite (groupCohomology.HInfRes (Rep.res H.subtype A) N 2).X₃ := ‹Finite _›
    obtain ⟨fin2, dvd2⟩ := finite_card_dvd_of_exact
      (groupCohomology.HInfRes (Rep.res H.subtype A) N 2).f.hom
      (groupCohomology.HInfRes (Rep.res H.subtype A) N 2).g.hom hinj hex
    have h3 : Nat.card (groupCohomology.HInfRes (Rep.res H.subtype A) N 2).X₃ ∣ Nat.card N := by
      change Nat.card (groupCohomology (Rep.res N.subtype (Rep.res H.subtype A)) 2) ∣ _
      rw [Nat.card_congr e3, ← hcardN]
      exact dvd3
    have h1' : Nat.card (groupCohomology.HInfRes (Rep.res H.subtype A) N 2).X₁ ∣ p :=
      hNidx ▸ dvd1
    refine ⟨fin2, dvd2.trans ?_⟩
    rw [← hm, hHN, mul_comm (Nat.card N)]
    exact mul_dvd_mul h1' h3

/-- **Order bound from prime-index layers.** If degree-one cohomology vanishes on every
subgroup and every prime-index layer has degree-two cohomology of order dividing the index,
then the degree-two cohomology of the finite group is finite of order dividing the group order.
-/
theorem finite_card_dvd_of_primeLayers [Finite G] (h1 : H1VanishesOnSubgroups A)
    (hcyc : H2PrimeLayerBound A) :
    Finite (groupCohomology A 2) ∧ Nat.card (groupCohomology A 2) ∣ Nat.card G := by
  classical
  let ι := (Nat.card G).primeFactors
  have hfact : ∀ p : ι, Fact (p : ℕ).Prime := fun p => ⟨Nat.prime_of_mem_primeFactors p.2⟩
  let P : ∀ p : ι, Sylow (p : ℕ) G := fun p => have := hfact p; Classical.arbitrary _
  let X : ι → Type u := fun p => groupCohomology (Rep.res (P p).1.subtype A) 2
  have hX : ∀ p : ι, Finite (X p) ∧ Nat.card (X p) ∣ (p : ℕ) ^ (Nat.card G).factorization p :=
    fun p => by
      have := hfact p
      rw [← Sylow.card_eq_multiplicity (P p)]
      exact finite_card_dvd_of_isPGroup h1 hcyc p (P p).1 (P p).isPGroup'
  let φ : groupCohomology A 2 →+ ∀ p : ι, X p :=
    AddMonoidHom.pi fun p =>
      (groupCohomology.map (P p).1.subtype (𝟙 (Rep.res (P p).1.subtype A)) 2).hom.toAddMonoidHom
  -- every class is killed by the group order
  have hG : ∀ x : groupCohomology A 2, Nat.card G • x = 0 := by
    intro x
    have hres : groupCohomology.map (⊥ : Subgroup G).subtype
        (𝟙 (Rep.res (⊥ : Subgroup G).subtype A)) 2 x = 0 := by
      have : Subsingleton (groupCohomology (Rep.res (⊥ : Subgroup G).subtype A) 2) :=
        ModuleCat.subsingleton_of_isZero
          (isZero_groupCohomology_succ_of_subsingleton _ 1)
      exact Subsingleton.elim _ _
    simpa [Subgroup.index_bot] using
      index_nsmul_eq_zero_of_restriction_eq_zero A ⊥ 2 x hres
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    apply AddMonoid.addOrderOf_eq_one_iff.mp
    apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
    intro q hq hqx
    have hqG : q ∈ (Nat.card G).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hq, hqx.trans (addOrderOf_dvd_of_nsmul_eq_zero (hG x)),
        Nat.card_pos.ne'⟩
    let q' : ι := ⟨q, hqG⟩
    have := hfact q'
    have hres := congrFun hx q'
    have hidx : (P q').1.index • x = 0 :=
      index_nsmul_eq_zero_of_restriction_eq_zero A (P q').1 2 x hres
    exact (P q').not_dvd_index (hqx.trans (addOrderOf_dvd_of_nsmul_eq_zero hidx))
  have : ∀ p : ι, Finite (X p) := fun p => (hX p).1
  refine ⟨Finite.of_injective φ hφ, ?_⟩
  have h1 : Nat.card (groupCohomology A 2) = Nat.card φ.range :=
    Nat.card_congr (Equiv.ofInjective φ hφ)
  have h2 : Nat.card φ.range ∣ Nat.card (∀ p : ι, X p) :=
    AddSubgroup.card_addSubgroup_dvd_card φ.range
  have h3 : ∏ p : ι, Nat.card (X p) ∣ ∏ p : ι, (p : ℕ) ^ (Nat.card G).factorization p :=
    Finset.prod_dvd_prod_of_dvd _ _ fun p _ => (hX p).2
  rw [h1]
  refine h2.trans ?_
  rw [Nat.card_pi]
  exact h3.trans (dvd_of_eq (Nat.prod_primeFactors_coe_pow_factorization Nat.card_pos.ne').symm)

end Langlands.Cohomology
