import Langlands.CommutativeAlgebra.Popescu.CharZeroResolutionStatement
import Langlands.CommutativeAlgebra.Popescu.StrictlyStandardSmoothStatement
import Langlands.CommutativeAlgebra.Popescu.StrictlyStandardRetractStatement
import Langlands.CommutativeAlgebra.Popescu.RegularParameterChoiceStatement
import Langlands.CommutativeAlgebra.Popescu.ArtinianBottom
import Langlands.CommutativeAlgebra.Popescu.SmoothingAlgebra
import Mathlib

/-! # Assembly of Stacks Lemma 10.3 (07FE) in characteristic zero -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

open MvPolynomial

section Aux

/-- If `q` is minimal over `I` in a Noetherian ring, some power of `qΛ_q` lies in `IΛ_q`. -/
theorem exists_pow_map_le {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ] (I q : Ideal Λ)
    [q.IsPrime] (hq : q ∈ I.minimalPrimes) :
    ∃ n : ℕ, (q ^ n).map (algebraMap Λ (Localization.AtPrime q)) ≤
      I.map (algebraMap Λ (Localization.AtPrime q)) := by
  set L := Localization.AtPrime q
  have hrad : IsLocalRing.maximalIdeal L ≤ (I.map (algebraMap Λ L)).radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf ?_
    rintro P ⟨hIP, hP⟩
    have h1 : P.comap (algebraMap Λ L) = q := by
      have hle : P.comap (algebraMap Λ L) ≤ q := by
        have := Ideal.comap_mono (f := algebraMap Λ L) (IsLocalRing.le_maximalIdeal hP.ne_top)
        have h2 : Ideal.comap (algebraMap Λ L) (IsLocalRing.maximalIdeal L) = q :=
          Localization.AtPrime.under_maximalIdeal
        rwa [h2] at this
      exact le_antisymm hle (hq.2 ⟨Ideal.IsPrime.comap _, Ideal.map_le_iff_le_comap.mp hIP⟩ hle)
    have h1' : Ideal.under Λ P = q := h1
    rw [← IsLocalization.map_under q.primeCompl L P, h1',
      Localization.AtPrime.map_eq_maximalIdeal]
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  refine ⟨n, ?_⟩
  rw [Ideal.map_pow, Localization.AtPrime.map_eq_maximalIdeal]
  exact hn

/-- The singular ideal over a smooth base is contained in the singular ideal over the bottom. -/
theorem singularIdeal_le_of_smooth (k R D : Type u) [CommRing k] [CommRing R] [CommRing D]
    [Algebra k R] [Algebra R D] [Algebra k D] [IsScalarTower k R D] [Algebra.Smooth k R]
    [Algebra.FinitePresentation R D] [Algebra.FinitePresentation k D] :
    singularIdeal R D ≤ singularIdeal k D := by
  intro b hb
  have := DimZeroResolutionProof.smooth_away_of_mem_singularIdeal hb
  exact DimZeroResolutionProof.mem_singularIdeal_of_smooth b (Algebra.Smooth.comp k R (Localization.Away b))

/-- An element with a strictly standard power lies in the singular ideal. -/
theorem mem_singularIdeal_of_pow (n0 : StrictlyStandardSmoothStatement.{u}) {R C : Type u}
    [CommRing R] [CommRing C] [Algebra R C] [Algebra.FinitePresentation R C] {x : C} {c : ℕ}
    (h : IsStrictlyStandard R (x ^ c)) : x ∈ singularIdeal R C := by
  have hsm := n0 R C (x ^ c) h
  have := DimZeroResolutionProof.mem_singularIdeal_of_smooth (x ^ c) hsm
  exact PrimeSpectrum.isRadical_vanishingIdeal _ ⟨c, this⟩

theorem SmoothingAlgebra.algebraMap_X_mem_singularIdeal {A : Type u} [CommRing A] (d : ℕ)
    {r : ℕ} (n : ℕ) (a : Fin r → A) (k : Type u) [Field k] [Algebra k A]
    [Algebra.FinitePresentation k A]
    (h : ∀ j, algebraMap A (SmoothingAlgebra.Alg d n a) (a j) ∈
      singularIdeal (MvPolynomial (Fin d) k) (SmoothingAlgebra.Alg d n a)) (i : Fin d) :
    algebraMap (MvPolynomial (Fin d) k) (SmoothingAlgebra.Alg d n a) (X i) ∈
      singularIdeal (MvPolynomial (Fin d) k) (SmoothingAlgebra.Alg d n a) := by
  refine PrimeSpectrum.isRadical_vanishingIdeal _ ⟨n, ?_⟩
  rw [SmoothingAlgebra.algebraMap_X, SmoothingAlgebra.rel_eq]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (h j)

end Aux

section Main

/-- Stacks Lemma 10.3 (07FE) in characteristic zero, from the Library statements of its
ingredients. -/
theorem charZeroResolution_of (h5 : NilpotentLiftingStatement.{u})
    (h6 : StrictlyStandardDesingularizationStatement.{u}) (n0 : StrictlyStandardSmoothStatement.{u})
    (n1 : DimZeroResolutionStatement.{u}) (n2 : CharZeroFieldFactorizationStatement.{u})
    (n3 : RegularSequenceFlatStatement.{u}) (n4 : RegularParameterChoiceStatement.{u})
    (n5 : StrictlyStandardRetractStatement.{u}) : CharZeroResolutionStatement.{u} := by
  intro k A Λ _ _ _ _ _ _ _ _ f q _ hq hreg
  classical
  -- generators of the singular ideal of `A`
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  obtain ⟨r, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian (singularIdeal k A))
  have ha' : Ideal.span (Set.range a) = singularIdeal k A := ha
  set I := (singularIdeal k A).map f with hI
  have hqI : q ∈ I.minimalPrimes := by
    rw [← Ideal.radical_minimalPrimes]; exact hq
  have hIq : I ≤ q := hqI.1.2
  obtain ⟨n, hn⟩ := exists_pow_map_le I q hqI
  set L := Localization.AtPrime q
  set d := (IsLocalRing.maximalIdeal L).spanFinrank
  set R := MvPolynomial (Fin d) k
  set B := SmoothingAlgebra.Alg d n a
  -- `B_{aⱼ}` and `B_{xᵢ}` are smooth over `R`
  have ha_mem : ∀ j, a j ∈ singularIdeal k A := fun j => by
    rw [← ha']; exact Ideal.subset_span ⟨j, rfl⟩
  have hBa : ∀ j, algebraMap A B (a j) ∈ singularIdeal R B := fun j => by
    have := DimZeroResolutionProof.smooth_away_of_mem_singularIdeal (ha_mem j)
    exact DimZeroResolutionProof.mem_singularIdeal_of_smooth _ (SmoothingAlgebra.smooth_away d n a k j)
  have hBx : ∀ i, algebraMap R B (X i) ∈ singularIdeal R B :=
    SmoothingAlgebra.algebraMap_X_mem_singularIdeal d n a k hBa
  -- Lemmas 3.1 and 3.7
  obtain ⟨C, _, _, hCfp, gC, rC, hrg, hss⟩ := n5 R B
  have hcx : ∀ i, ∃ c, IsStrictlyStandard R (gC (algebraMap R B (X i)) ^ c) := fun i =>
    hss _ (DimZeroResolutionProof.smooth_away_of_mem_singularIdeal (hBx i))
  choose cx hcx using hcx
  set c := ∑ i, cx i + 1 with hcdef
  have hc : 0 < c := Nat.succ_pos _
  have hssC : ∀ i, IsStrictlyStandard R (algebraMap R C (X i ^ c)) := fun i => by
    have hle : cx i ≤ c := by
      have := Finset.single_le_sum (f := cx) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      omega
    rw [map_pow, ← gC.commutes, ← Nat.add_sub_cancel' hle, pow_add]
    exact (hcx i).mul_right _
  -- Lemma 10.2
  obtain ⟨π, hspan, hregseq, hπn, hann⟩ := n4 Λ I q n hIq hn hreg (8 * c) (by omega)
  -- `Λ` as an `R`-algebra, `xᵢ ↦ πᵢ`
  let _ : Algebra R Λ := (aeval π : R →ₐ[k] Λ).toRingHom.toAlgebra
  have : IsScalarTower k R Λ := .of_algebraMap_eq fun c => (aeval_C π c).symm
  have hX : ∀ i, algebraMap R Λ (X i) = π i := fun i => aeval_X π i
  have hπq : ∀ i, π i ∈ q := fun i => by
    have : algebraMap Λ L (π i) ∈ IsLocalRing.maximalIdeal L := by
      rw [← hspan]; exact Ideal.subset_span ⟨i, rfl⟩
    have h2 : Ideal.comap (algebraMap Λ L) (IsLocalRing.maximalIdeal L) = q :=
      Localization.AtPrime.under_maximalIdeal
    rw [← h2]
    exact this
  -- the map `B → Λ`
  have hlex : ∀ i, ∃ lam : Fin r → Λ, π i ^ n = ∑ j, lam j * f (a j) := fun i => by
    have h1 : π i ^ n ∈ I := hπn i
    rw [hI, ← ha', Ideal.map_span, ← Set.range_comp, Ideal.mem_span_range_iff_exists_fun] at h1
    obtain ⟨lam, hlam⟩ := h1
    exact ⟨lam, hlam.symm⟩
  choose lam hlam using hlex
  let fB : B →ₐ[R] Λ := SmoothingAlgebra.lift d n a k f π lam hlam hX
  have hfB : ∀ x, fB (algebraMap A B x) = f x := SmoothingAlgebra.lift_algebraMap d n a k f π lam hlam hX
  let fC : C →ₐ[R] Λ := fB.comp rC
  have hfC : ∀ x, fC (gC (algebraMap A B x)) = f x := fun x => by
    show fB (rC (gC (algebraMap A B x))) = f x
    rw [← AlgHom.comp_apply rC gC, hrg, AlgHom.id_apply, hfB]
  -- flatness and the bottom of the induction
  have : Module.Flat R L := flat_localization_of_regular n3 π hX q hspan hregseq
  set K : Ideal R := Ideal.span (Set.range fun i => (X i ^ c) ^ 8) with hK
  have hK1 : K ≤ Ideal.span (Set.range X) := by
    rw [hK, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    show ((X i : R) ^ c) ^ 8 ∈ Ideal.span (Set.range X)
    rw [← pow_mul]
    obtain ⟨m, hm⟩ : ∃ m, c * 8 = m + 1 := ⟨c * 8 - 1, by omega⟩
    rw [hm, pow_succ]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  have hK2 : ∀ i, ∃ m, (X i : R) ^ m ∈ K := fun i =>
    ⟨c * 8, by rw [pow_mul]; exact Ideal.subset_span ⟨i, rfl⟩⟩
  have hbot := bottomCondition_of_flat n2 h5 π hX q hspan K hK1 hK2
  -- Lemma 9.2
  have hres := canBeResolved_of_sequence h6 n1 d R C Λ fC q (fun i => X i ^ c)
    (fun i => by
      show algebraMap R Λ (X i ^ c) ∈ q
      rw [map_pow, hX]
      exact Ideal.pow_mem_of_mem _ (hπq i) _ hc)
    (fun i x hx => X_pow_annihilator k c 8 i x hx)
    (fun i y hy => by
      have hfun : (fun j => algebraMap R Λ ((fun i => (X i : R) ^ c) j) ^ 8) =
          fun j => π j ^ (8 * c) := funext fun j => by
        simp only [map_pow, hX, ← pow_mul, mul_comm]
      have hpi : algebraMap R Λ ((fun i => (X i : R) ^ c) i) = π i ^ c := by
        simp only [map_pow, hX]
      rw [hfun, hpi] at hy ⊢
      exact pow_annihilator (hann i) hc y hy)
    hssC hbot
  obtain ⟨D, _, _, hD, gD, hD', hgh, hle, hnle⟩ := hres
  -- the resolution over `k`
  let _ : Algebra k C := ((algebraMap R C).comp (algebraMap k R)).toAlgebra
  have : IsScalarTower k R C := .of_algebraMap_eq fun _ => rfl
  let _ : Algebra k D := ((algebraMap R D).comp (algebraMap k R)).toAlgebra
  have : IsScalarTower k R D := .of_algebraMap_eq fun _ => rfl
  have : Algebra.FinitePresentation k D := Algebra.FinitePresentation.trans k R D
  let g' : A →ₐ[k] D :=
    (gD.restrictScalars k).comp ((gC.restrictScalars k).comp (IsScalarTower.toAlgHom k A B))
  let h' : D →ₐ[k] Λ := hD'.restrictScalars k
  have hcomp : h'.comp g' = f := by
    ext x
    show hD' (gD (gC (algebraMap A B x))) = f x
    have := congrArg (fun φ => φ (gC (algebraMap A B x))) hgh
    simp only [AlgHom.comp_apply] at this
    rw [this, hfC]
  have hDle : singularRadical R hD' ≤ singularRadical k h' :=
    Ideal.radical_mono (Ideal.map_mono (singularIdeal_le_of_smooth k R D))
  refine ⟨D, inferInstance, inferInstance, inferInstance, g', h', hcomp, ?_,
    fun h => hnle (hDle.trans h)⟩
  show ((singularIdeal k A).map f).radical ≤ _
  refine (Ideal.radical_mono ?_).trans (Ideal.radical_isRadical _)
  rw [← ha', Ideal.map_span, Ideal.span_le]
  rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
  have h1 : gC (algebraMap A B (a j)) ∈ singularIdeal R C := by
    obtain ⟨c', hc'⟩ := hss _ (DimZeroResolutionProof.smooth_away_of_mem_singularIdeal (hBa j))
    exact mem_singularIdeal_of_pow n0 hc'
  have h2 : fC (gC (algebraMap A B (a j))) ∈ singularRadical R fC :=
    Ideal.le_radical (Ideal.mem_map_of_mem _ h1)
  rw [hfC] at h2
  exact hDle (hle h2)

end Main

end Langlands.CommutativeAlgebra.Popescu
