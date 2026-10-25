import Langlands.Global.Arithmetic.CyclicPrimePowerLocalDegreeReductionStatement
import Langlands.ClassField.Global.CompletionTower
import Mathlib.GroupTheory.SpecificGroups.Cyclic

noncomputable section

namespace Langlands.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField AdelicFunctoriality.FiniteExtension
open AdelicFunctoriality

universe u v

/-- The degree-prime subfield detects full local degree. -/
theorem cyclicPrimePowerLocalDegreeReductionStatement :
    CyclicPrimePowerLocalDegreeReductionStatement.{u,v} := by
  classical
  intro F _ _ E _ _ _ _ _ ℓ r hℓ hr hdeg
  obtain ⟨g, hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp
    (inferInstance : IsCyclic (E ≃ₐ[F] E))
  have horder : orderOf g = ℓ ^ r := by
    rw [← Nat.card_zpowers, hg, Nat.card_congr (Subgroup.topEquiv).toEquiv,
      IsGalois.card_aut_eq_finrank, hdeg]
  let H : Subgroup (E ≃ₐ[F] E) := Subgroup.zpowers (g ^ (ℓ : ℤ))
  have hindex : H.index = ℓ := by
    change (Subgroup.zpowers (g ^ (ℓ : ℤ))).index = ℓ
    rw [Subgroup.index_zpowers_zpow hg, horder]
    exact Nat.gcd_eq_left (dvd_pow_self ℓ hr.ne')
  have hproper (D : Subgroup (E ≃ₐ[F] E)) (hD : D ≠ ⊤) : D ≤ H := by
    rw [IsCyclic.subgroup_le_iff_index_dvd, hindex]
    have hdiv := D.index_dvd_card
    rw [IsGalois.card_aut_eq_finrank, hdeg] at hdiv
    obtain ⟨k, hk, hcard⟩ := (Nat.dvd_prime_pow hℓ).mp hdiv
    have hk0 : k ≠ 0 := by
      intro hk0
      have : D.index = 1 := by simpa [hk0] using hcard
      exact hD (Subgroup.index_eq_one.mp this)
    rw [hcard]
    exact dvd_pow_self ℓ hk0
  have : H.Normal := inferInstance
  let K := IntermediateField.fixedField H
  have : IsGalois F K := inferInstance
  have hcyclic : IsCyclic (K ≃ₐ[F] K) :=
    isCyclic_of_surjective (AlgEquiv.restrictNormalHom K)
      (AlgEquiv.restrictNormalHom_surjective E)
  have hKdeg : Module.finrank F K = ℓ := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index,
      IntermediateField.fixingSubgroup_fixedField, hindex]
  refine ⟨K, inferInstance, hcyclic, hKdeg, ?_⟩
  intro v q hq
  let := hq
  intro hlocal
  obtain ⟨w, hwq⟩ := exists_place_above (L := E) q
  let := hwq
  have hwv : w.asIdeal.LiesOver v.asIdeal := Ideal.LiesOver.trans _ q.asIdeal _
  refine ⟨w, hwq, hwv, ?_⟩
  let d : (w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E) →*
      (E ≃ₐ[F] E) :=
    (AlgEquiv.restrictNormalHom E).comp (AlgEquiv.restrictScalarsHom F)
  have hd (σ : w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E) (x : E) :
      algebraMap E (w.adicCompletion E) (d σ x) = σ (algebraMap E _ x) := by
    simp only [d, MonoidHom.comp_apply, AlgEquiv.restrictNormalHom,
      MonoidHom.mk'_apply, AlgEquiv.restrictNormal_commutes]
    rfl
  have hinj : Function.Injective d := by
    intro σ τ h
    have heq := subalgebra_eq_top_of_algebraMap_mem v w
      (AlgHom.equalizer σ.toAlgHom τ.toAlgHom) (fun x => by
        change σ (algebraMap E _ x) = τ (algebraMap E _ x)
        rw [← hd, ← hd, h])
    exact AlgEquiv.ext fun x => DFunLike.congr_fun (AlgHom.equalizer_eq_top.mp heq) x
  have : IsGalois (v.adicCompletion F) (w.adicCompletion E) := isGalois_adicCompletion v w
  have : IsGalois (v.adicCompletion F) (q.adicCompletion K) := isGalois_adicCompletion v q
  have htop : d.range = ⊤ := by
    by_contra hne
    have hle := hproper d.range hne
    have hone (τ : q.adicCompletion K ≃ₐ[v.adicCompletion F] q.adicCompletion K) : τ = 1 := by
      obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective
        (F := v.adicCompletion F) (K₁ := q.adicCompletion K) (w.adicCompletion E) τ
      have hfix : d σ ∈ K.fixingSubgroup := by
        rw [IntermediateField.fixingSubgroup_fixedField]
        exact hle ⟨σ, rfl⟩
      have heq := subalgebra_eq_top_of_algebraMap_mem v q
        (AlgHom.equalizer τ.toAlgHom (1 : q.adicCompletion K ≃ₐ[v.adicCompletion F]
          q.adicCompletion K).toAlgHom) (fun x => by
          change τ (algebraMap K _ x) = algebraMap K _ x
          apply (algebraMap (q.adicCompletion K) (w.adicCompletion E)).injective
          rw [← hσ]
          change algebraMap (q.adicCompletion K) (w.adicCompletion E)
            (σ.restrictNormal (q.adicCompletion K) (algebraMap K _ x)) = _
          rw [AlgEquiv.restrictNormal_commutes]
          rw [← IsScalarTower.algebraMap_apply K (q.adicCompletion K) (w.adicCompletion E)]
          rw [IsScalarTower.algebraMap_apply K E (w.adicCompletion E), ← hd]
          rw [IntermediateField.mem_fixingSubgroup_iff] at hfix
          exact congrArg (algebraMap E (w.adicCompletion E)) (hfix x x.property))
      exact AlgEquiv.ext fun x => DFunLike.congr_fun (AlgHom.equalizer_eq_top.mp heq) x
    have : Subsingleton (q.adicCompletion K ≃ₐ[v.adicCompletion F] q.adicCompletion K) :=
      ⟨fun σ τ => (hone σ).trans (hone τ).symm⟩
    apply hlocal
    rw [← IsGalois.card_aut_eq_finrank]
    exact Nat.card_unique
  have hsurj : Function.Surjective d := MonoidHom.range_eq_top.mp htop
  rw [← IsGalois.card_aut_eq_finrank, ← IsGalois.card_aut_eq_finrank]
  exact Nat.card_congr (Equiv.ofBijective d ⟨hinj, hsurj⟩)

end Langlands.Global
