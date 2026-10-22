import Langlands.Global.AdelicFunctoriality.CompletedLocalDegreeProof
import Langlands.Global.AdelicFunctoriality.FiniteComparisonReduction
import Mathlib.NumberTheory.RamificationInertia.Galois

/-! # Local degrees and Galois completions at finite places -/

noncomputable section

namespace Langlands.Global.AdelicFunctoriality

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField FiniteExtension

universe u v w

section Places

variable {K : Type u} {L : Type v} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]

/-- Every finite place of `K` lies under a finite place of `L`. -/
instance finitePlacesAbove_nonempty (p : HeightOneSpectrum (𝓞 K)) :
    Nonempty (FinitePlacesAbove L p) := by
  obtain ⟨⟨Q, hQ, hQo⟩⟩ := Ideal.nonempty_primesOver (S := 𝓞 L) p.asIdeal
  exact ⟨⟨⟨Q, hQ, Ideal.ne_bot_of_mem_primesOver p.ne_bot ⟨hQ, hQo⟩⟩, hQo⟩⟩

variable (L) in
/-- A chosen finite place of `L` above the finite place `p` of `K`. -/
def placeAbove (p : HeightOneSpectrum (𝓞 K)) : FinitePlacesAbove L p :=
  Classical.arbitrary _

omit [NumberField K] in
theorem exists_place_above (p : HeightOneSpectrum (𝓞 K)) :
    ∃ q : HeightOneSpectrum (𝓞 L), q.asIdeal.LiesOver p.asIdeal :=
  ⟨(placeAbove L p).1, (placeAbove L p).2⟩

end Places

section LocalDegree

variable {K : Type u} {L : Type v} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]

/-- The local degree at a finite place is the product of ramification index and inertia
degree. -/
theorem localDegree_eq (p : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L))
    [q.asIdeal.LiesOver p.asIdeal] :
    Module.finrank (p.adicCompletion K) (q.adicCompletion L) =
      q.asIdeal.ramificationIdx (𝓞 K) * q.asIdeal.inertiaDeg (𝓞 K) := by
  classical
  have hle : ∀ r : FinitePlacesAbove L p,
      r.1.asIdeal.ramificationIdx (𝓞 K) * r.1.asIdeal.inertiaDeg (𝓞 K) ≤
        Module.finrank (p.adicCompletion K) (r.1.adicCompletion L) := fun r =>
    completedLocalDegreeLowerBound K L p r.1
  have hsum := finitePlacesAbove_sum_ramification_inertia (L := L) p
  have hsum2 := finiteLocalDegree_sum_le (L := L) p
  have heq := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (fun r _ => hle r)).1
    (le_antisymm (Finset.sum_le_sum fun r _ => hle r) (by rw [hsum]; exact hsum2))
  exact (heq ⟨q, ‹_›⟩ (Finset.mem_univ _)).symm

/-- In a Galois extension the local degree divides the global degree. -/
theorem localDegree_dvd [IsGalois K L] (p : HeightOneSpectrum (𝓞 K))
    (q : HeightOneSpectrum (𝓞 L)) [q.asIdeal.LiesOver p.asIdeal] :
    Module.finrank (p.adicCompletion K) (q.adicCompletion L) ∣ Module.finrank K L := by
  rw [localDegree_eq]
  have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p.asIdeal (𝓞 L)
    (L ≃ₐ[K] L)
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx p.asIdeal q.asIdeal (L ≃ₐ[K] L),
    Ideal.inertiaDegIn_eq_inertiaDeg p.asIdeal q.asIdeal (L ≃ₐ[K] L),
    IsGalois.card_aut_eq_finrank] at h
  exact Dvd.intro_left _ h

/-- A subalgebra of `L_q` over `K_p` containing the image of `L` is everything: `L_q` is
spanned over `K_p` by `L`. -/
theorem subalgebra_eq_top_of_algebraMap_mem (p : HeightOneSpectrum (𝓞 K))
    (q : HeightOneSpectrum (𝓞 L)) [hq : q.asIdeal.LiesOver p.asIdeal]
    (S : Subalgebra (p.adicCompletion K) (q.adicCompletion L))
    (hS : ∀ y : L, algebraMap L (q.adicCompletion L) y ∈ S) : S = ⊤ := by
  classical
  rw [eq_top_iff]
  intro x _
  let r : FinitePlacesAbove L p := ⟨q, hq⟩
  obtain ⟨t, ht⟩ := finiteTensorMap_surjective (L := L) p (Pi.single r x)
  have hx : finiteTensorMap p t r = x := by rw [ht, Pi.single_eq_same]
  rw [← hx]
  clear hx ht
  induction t using TensorProduct.inductionOn with
  | tmul a y =>
    rw [finiteTensorMap_tmul]
    exact S.mul_mem (S.algebraMap_mem a) (hS y)
  | add s t hs ht =>
    rw [map_add, Pi.add_apply]
    exact S.add_mem hs ht

/-- If `L / K` is Galois, so is every completion `L_q / K_p` at a finite place. -/
theorem isGalois_adicCompletion [IsGalois K L] (p : HeightOneSpectrum (𝓞 K))
    (q : HeightOneSpectrum (𝓞 L)) [q.asIdeal.LiesOver p.asIdeal] :
    IsGalois (p.adicCompletion K) (q.adicCompletion L) := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element K L
  have hint : IsIntegral K α := .of_finite K α
  set f := minpoly K α
  have hmap : ∀ r : K, algebraMap L (q.adicCompletion L) (algebraMap K L r) =
      algebraMap (p.adicCompletion K) (q.adicCompletion L)
        (algebraMap K (p.adicCompletion K) r) := fun r => by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hroot : algebraMap L (q.adicCompletion L) α ∈
      (f.map (algebraMap K (p.adicCompletion K))).rootSet (q.adicCompletion L) := by
    rw [Polynomial.mem_rootSet]
    refine ⟨(Polynomial.map_ne_zero_iff (algebraMap K _).injective).2 (minpoly.ne_zero hint),
      ?_⟩
    rw [Polynomial.aeval_map_algebraMap, Polynomial.aeval_algebraMap_apply, minpoly.aeval,
      map_zero]
  have : Polynomial.IsSplittingField (p.adicCompletion K) (q.adicCompletion L)
      (f.map (algebraMap K (p.adicCompletion K))) := by
    constructor
    · rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq,
        IsScalarTower.algebraMap_eq K L (q.adicCompletion L), ← Polynomial.map_map]
      exact (IsGalois.splits K α).map _
    · apply subalgebra_eq_top_of_algebraMap_mem p q
      intro y
      have hy : y ∈ Algebra.adjoin K {α} := by
        rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, hα]
        trivial
      refine Algebra.adjoin_induction (fun x hx => ?_) (fun r => ?_)
        (fun x y _ _ hx hy => ?_) (fun x y _ _ hx hy => ?_) hy
      · rw [Set.mem_singleton_iff.mp hx]
        exact Algebra.subset_adjoin hroot
      · rw [hmap]
        exact Subalgebra.algebraMap_mem _ _
      · rw [map_add]; exact Subalgebra.add_mem _ hx hy
      · rw [map_mul]; exact Subalgebra.mul_mem _ hx hy
  have hsep : f.Separable := Algebra.IsSeparable.isSeparable K α
  exact IsGalois.of_separable_splitting_field (hsep.map (f := algebraMap K (p.adicCompletion K)))

end LocalDegree

section Tower

variable {F : Type u} {K : Type v} {L : Type w} [Field F] [NumberField F] [Field K]
  [NumberField K] [Field L] [NumberField L] [Algebra F K] [Algebra F L] [Algebra K L]
  [IsScalarTower F K L]

/-- Local degrees are multiplicative in towers, so they divide upward. -/
theorem localDegree_dvd_localDegree (v : HeightOneSpectrum (𝓞 F))
    (v' : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L))
    [v'.asIdeal.LiesOver v.asIdeal] [q.asIdeal.LiesOver v'.asIdeal]
    [q.asIdeal.LiesOver v.asIdeal] :
    Module.finrank (v.adicCompletion F) (v'.adicCompletion K) ∣
      Module.finrank (v.adicCompletion F) (q.adicCompletion L) := by
  rw [localDegree_eq v v', localDegree_eq v q,
    Ideal.ramificationIdx_tower (R := 𝓞 F) v'.asIdeal q.asIdeal,
    Ideal.inertiaDeg_tower (R := 𝓞 F) v'.asIdeal q.asIdeal]
  exact mul_dvd_mul (dvd_mul_right _ _) (dvd_mul_right _ _)

end Tower

end Langlands.Global.AdelicFunctoriality
