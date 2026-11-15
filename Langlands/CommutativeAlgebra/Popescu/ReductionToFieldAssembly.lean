import Langlands.CommutativeAlgebra.Popescu.ArtinianBottom
import Langlands.CommutativeAlgebra.Popescu.ReductionToFieldStatement
import Langlands.CommutativeAlgebra.Popescu.SingularIdealFactorizationStatement
import Langlands.CommutativeAlgebra.Popescu.NilpotentLiftingStatement
import Langlands.CommutativeAlgebra.Popescu.StrictlyStandardDesingularizationStatement
import Langlands.CommutativeAlgebra.Popescu.LocalizationStandardDescentStatement
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Noetherian.Nilpotent
import Mathlib.RingTheory.TensorProduct.Quotient

/-! # Assembly of the reduction of Popescu's theorem to a base field (Stacks 07F5) -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

open TensorProduct

section Regularity

/-- Geometric regularity is preserved by base change along an isomorphism of fields. -/
theorem GeometricallyRegular.baseChange_of_bijective {k k' : Type u} [Field k] [Field k']
    [Algebra k k'] (hk : Function.Bijective (algebraMap k k')) {A : Type u} [CommRing A]
    [Algebra k A] (h : GeometricallyRegular k A) : GeometricallyRegular k' (k' ⊗[k] A) := by
  let e : k ≃ₐ[k] k' := AlgEquiv.ofBijective (Algebra.ofId k k') hk
  refine ⟨?_, ?_⟩
  · have := h.1
    exact isNoetherianRing_of_ringEquiv A
      ((Algebra.TensorProduct.lid k A).symm.trans
        (Algebra.TensorProduct.congr e AlgEquiv.refl)).toRingEquiv
  · intro k'' _ _ _ _
    let _ : Algebra k k'' := ((algebraMap k' k'').comp (algebraMap k k')).toAlgebra
    have : IsScalarTower k k' k'' := .of_algebraMap_eq fun _ => rfl
    have : Module.Finite k k' := Module.Finite.equiv e.toLinearEquiv
    have : FiniteDimensional k k'' := Module.Finite.trans k' k''
    have : IsPurelyInseparable k k' := e.isPurelyInseparable
    have : IsPurelyInseparable k k'' := IsPurelyInseparable.trans k k' k''
    have := h.2 k''
    exact IsRegularRing.of_ringEquiv
      (Algebra.TensorProduct.cancelBaseChange k k' k'' k'' A).symm.toRingEquiv

/-- Over a field, geometric regularity gives a regular algebra map: the only prime is `⊥`,
whose residue field is the field itself. -/
theorem regularAlgebra_of_geometricallyRegular {k : Type u} [Field k] {A : Type u} [CommRing A]
    [Algebra k A] (h : GeometricallyRegular k A) : RegularAlgebra k A := by
  refine ⟨inferInstance, fun p _ => ?_⟩
  obtain rfl : p = ⊥ := Ideal.eq_bot_of_prime p
  exact GeometricallyRegular.baseChange_of_bijective
    (⊥ : Ideal k).algEquivResidueFieldOfField.bijective h

/-- A regular algebra map stays regular after reduction modulo an ideal of the base. -/
theorem regularAlgebra_quotient {R Λ : Type u} [CommRing R] [CommRing Λ] [Algebra R Λ]
    (I : Ideal R) (h : RegularAlgebra R Λ) :
    RegularAlgebra (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ)) := by
  refine ⟨?_, fun P _ => ?_⟩
  · have := h.1
    exact Module.Flat.of_linearEquiv
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor Λ I).toLinearEquiv
  · let p : Ideal R := P.comap (Ideal.Quotient.mk I)
    have hp : p.IsPrime := Ideal.comap_isPrime _ _
    let φ : p.ResidueField →+* P.ResidueField :=
      Ideal.ResidueField.map p P (Ideal.Quotient.mk I) rfl
    have hφ : Function.Bijective φ :=
      (RingHom.surjectiveOnStalks_of_surjective Ideal.Quotient.mk_surjective).residueFieldMap_bijective
        p P rfl
    let _ : Algebra p.ResidueField P.ResidueField := φ.toAlgebra
    have : IsScalarTower R p.ResidueField P.ResidueField := .of_algebraMap_eq fun r => by
      show _ = φ _
      rw [Ideal.ResidueField.map_algebraMap, IsScalarTower.algebraMap_apply R (R ⧸ I)]
      rfl
    have h₁ := GeometricallyRegular.baseChange_of_bijective hφ (h.2 p)
    refine GeometricallyRegular.of_algEquiv h₁ <|
      (Algebra.TensorProduct.cancelBaseChange R p.ResidueField P.ResidueField P.ResidueField Λ).trans <|
      (Algebra.TensorProduct.cancelBaseChange R (R ⧸ I) P.ResidueField P.ResidueField Λ).symm.trans <|
      Algebra.TensorProduct.congr AlgEquiv.refl
        (Algebra.TensorProduct.quotIdealMapEquivQuotTensor Λ I).symm

end Regularity

section Auxiliary

/-- In a reduced ring, `Ann(π²) = Ann(π)`. -/
theorem mul_eq_zero_of_sq_mul_eq_zero {R : Type u} [CommRing R] (hN : nilradical R = ⊥) (π x : R)
    (hx : π ^ 2 * x = 0) : π * x = 0 := by
  have hmem : π * x ∈ nilradical R :=
    mem_nilradical.mpr ⟨2, by rw [mul_pow, pow_two x, ← mul_assoc, hx, zero_mul]⟩
  rw [hN] at hmem
  simpa using hmem

/-- Over a flat algebra, the annihilator condition `Ann(π²) = Ann(π)` passes from the base
to the algebra (equational criterion for flatness). -/
theorem flat_mul_eq_zero_of_sq_mul_eq_zero {R Λ : Type u} [CommRing R] [CommRing Λ] [Algebra R Λ]
    [Module.Flat R Λ] (π : R) (hR : ∀ x : R, π ^ 2 * x = 0 → π * x = 0) (x : Λ)
    (hx : algebraMap R Λ π ^ 2 * x = 0) : algebraMap R Λ π * x = 0 := by
  have h : ∑ _i : Unit, (π ^ 2) • x = 0 := by
    simpa [Algebra.smul_def] using hx
  obtain ⟨k, a, y, hxy, ha⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero
    (f := fun _ : Unit => π ^ 2) (x := fun _ => x) h
  have hx' : x = ∑ j, a () j • y j := hxy ()
  have ha' : ∀ j, π ^ 2 * a () j = 0 := fun j => by simpa using ha j
  rw [hx', ← Algebra.smul_def, Finset.smul_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [smul_smul, hR _ (ha' j), zero_smul]

/-- The singular ideal of a smooth algebra is the unit ideal. -/
theorem singularIdeal_eq_top_of_smooth {R C : Type u} [CommRing R] [CommRing C] [Algebra R C]
    [Algebra.Smooth R C] : singularIdeal R C = ⊤ := by
  have : Algebra.smoothLocus R C = Set.univ := Algebra.smoothLocus_eq_univ_iff.mpr inferInstance
  rw [singularIdeal, this, Set.compl_univ, PrimeSpectrum.vanishingIdeal_empty]

/-- An element whose localization is smooth lies in the singular ideal. -/
theorem mem_singularIdeal_of_smooth_away {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    [Algebra.FinitePresentation R B] (b : B) (hb : Algebra.Smooth R (Localization.Away b)) :
    b ∈ singularIdeal R B := by
  rw [singularIdeal, PrimeSpectrum.mem_vanishingIdeal]
  intro x hx
  by_contra hbx
  exact hx (Algebra.basicOpen_subset_smoothLocus_iff_smooth.mpr hb
    ((PrimeSpectrum.mem_basicOpen _ _).mpr hbx))

/-- At a minimal prime of a reduced ring the residue field is the localization. -/
theorem isLocalization_residueField_of_mem_minimalPrimes {R : Type u} [CommRing R]
    (hN : nilradical R = ⊥) (p : Ideal R) [p.IsPrime] (hp : p ∈ minimalPrimes R) :
    IsLocalization p.primeCompl p.ResidueField := by
  have : IsReduced R := nilradical_eq_bot_iff.mp hN
  have hmax : IsLocalRing.maximalIdeal (Localization.AtPrime p) = ⊥ := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p (Localization.AtPrime p),
      ← IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes (A := Localization.AtPrime p) p ⊥ hp,
      Ideal.map_bot]
    exact nilradical_eq_bot_iff.mpr inferInstance
  have hbij : Function.Bijective (algebraMap (Localization.AtPrime p) p.ResidueField) := by
    refine ⟨?_, IsLocalRing.residue_surjective⟩
    rw [RingHom.injective_iff_ker_eq_bot]
    exact IsLocalRing.ker_residue.trans hmax
  exact IsLocalization.isLocalization_of_algEquiv (M := p.primeCompl)
    (S := Localization.AtPrime p)
    (AlgEquiv.ofBijective (IsScalarTower.toAlgHom R (Localization.AtPrime p) p.ResidueField) hbij)

end Auxiliary

section KeyLemma

/-- Stacks 07F5, first half: at a prime `p` of `R` whose residue field is a localization of `R`,
the field case applied to the fibre and Lemma 8.3 give a factorization through a finitely
presented algebra in which some `s ∉ p` is strictly standard. -/
theorem exists_strictlyStandard_factorization (hfield : PopescuFieldCaseStatement.{u})
    (h9 : LocalizationStandardDescentStatement.{u}) {R Λ : Type u} [CommRing R] [CommRing Λ]
    [Algebra R Λ] (hreg : RegularAlgebra R Λ) (p : Ideal R) [p.IsPrime]
    [IsLocalization p.primeCompl p.ResidueField]
    (A : Type u) [CommRing A] [Algebra R A] [Algebra.FinitePresentation R A] (f : A →ₐ[R] Λ) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra R B), Algebra.FinitePresentation R B ∧
      ∃ (g : A →ₐ[R] B) (h : B →ₐ[R] Λ), h.comp g = f ∧
        ∃ s ∈ p.primeCompl, IsStrictlyStandard R (algebraMap R B s) := by
  have hN : IsNoetherianRing (p.Fiber Λ) := (hreg.2 p).1
  obtain ⟨B', _, _, hB', g', h', hgh'⟩ := hfield p.ResidueField (p.Fiber Λ)
    (regularAlgebra_of_geometricallyRegular (hreg.2 p)) (p.ResidueField ⊗[R] A)
    (Algebra.TensorProduct.map (AlgHom.id p.ResidueField p.ResidueField) f)
  let _ : Algebra Λ (p.Fiber Λ) := Algebra.TensorProduct.rightAlgebra
  have : IsLocalization (Algebra.algebraMapSubmonoid Λ p.primeCompl) (p.Fiber Λ) :=
    IsLocalization.tensorRight _ _
  let _ : Algebra R B' := ((algebraMap p.ResidueField B').comp (algebraMap R p.ResidueField)).toAlgebra
  have : IsScalarTower R p.ResidueField B' := .of_algebraMap_eq fun _ => rfl
  refine h9 R A Λ p.ResidueField (p.Fiber Λ) p.primeCompl f B'
    ((g'.restrictScalars R).comp Algebra.TensorProduct.includeRight) h' ?_
  ext a
  have := congrArg (fun φ => φ ((1 : p.ResidueField) ⊗ₜ[R] a)) hgh'
  simp only [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, map_one] at this
  exact this

/-- Stacks 07F5, inductive step: if `R` is Noetherian, `R → Λ` is regular, and PT holds for
`R/J → Λ/JΛ` for every nonzero ideal `J`, then PT holds for `R → Λ`. -/
theorem hasSmoothFactorizations_of_quotients (hfield : PopescuFieldCaseStatement.{u})
    (h3 : SingularIdealFactorizationStatement.{u}) (h5 : NilpotentLiftingStatement.{u})
    (h6 : StrictlyStandardDesingularizationStatement.{u})
    (h9 : LocalizationStandardDescentStatement.{u})
    {R Λ : Type u} [CommRing R] [CommRing Λ] [IsNoetherianRing R] [Algebra R Λ]
    (hreg : RegularAlgebra R Λ)
    (hq : ∀ J : Ideal R, J ≠ ⊥ → HasSmoothFactorizations (R ⧸ J) (Λ ⧸ J.map (algebraMap R Λ))) :
    HasSmoothFactorizations R Λ := by
  by_cases hN : nilradical R = ⊥
  swap
  · exact h5 R Λ (nilradical R) (IsNoetherianRing.isNilpotent_nilradical R) hreg.1 (hq _ hN)
  intro A _ _ _ f
  suffices H : ∃ (B : Type u) (_ : CommRing B) (_ : Algebra R B), Algebra.FinitePresentation R B ∧
      ∃ (g : A →ₐ[R] B) (h : B →ₐ[R] Λ), h.comp g = f ∧ (singularIdeal R B).map h = ⊤ by
    obtain ⟨B, _, _, _, g, h, hgh, htop⟩ := H
    obtain ⟨C, _, _, hC, g', h', hgh'⟩ := h3 R B Λ h htop
    exact ⟨C, inferInstance, inferInstance, hC, g'.comp g, h', by
      rw [← AlgHom.comp_assoc, hgh', hgh]⟩
  rcases subsingleton_or_nontrivial R with hR | hR
  · have h01 : (0 : Λ) = 1 := by
      rw [← map_zero (algebraMap R Λ), ← map_one (algebraMap R Λ), Subsingleton.elim (0 : R) 1]
    refine ⟨A, inferInstance, inferInstance, inferInstance, AlgHom.id R A, f, rfl, ?_⟩
    rw [Ideal.eq_top_iff_one, ← h01]
    exact Ideal.zero_mem _
  obtain ⟨m, hm⟩ := Ideal.exists_maximal R
  obtain ⟨p, hp, -⟩ := Ideal.exists_minimalPrimes_le (bot_le : (⊥ : Ideal R) ≤ m)
  have : p.IsPrime := hp.1.1
  have : IsLocalization p.primeCompl p.ResidueField :=
    isLocalization_residueField_of_mem_minimalPrimes hN p hp
  obtain ⟨B, _, _, _, g, h, hgh, s, hs, hss⟩ :=
    exists_strictlyStandard_factorization hfield h9 hreg p A f
  have hRs : ∀ x : R, s ^ 2 * x = 0 → s * x = 0 := mul_eq_zero_of_sq_mul_eq_zero hN s
  have := hreg.1
  have hΛs := flat_mul_eq_zero_of_sq_mul_eq_zero (Λ := Λ) s hRs
  have hJ : Ideal.span {s ^ 8} ≠ ⊥ := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    intro h0
    exact hs (‹p.IsPrime›.mem_of_pow_mem 8 (h0 ▸ p.zero_mem))
  obtain ⟨C, _, _, hC, gb, hb, hghb⟩ := hq _ hJ ((R ⧸ Ideal.span {s ^ 8}) ⊗[R] B)
    (Algebra.TensorProduct.lift
      (Algebra.ofId (R ⧸ Ideal.span {s ^ 8}) (Λ ⧸ (Ideal.span {s ^ 8}).map (algebraMap R Λ)))
      ((Ideal.Quotient.mkₐ R _).comp h) (fun _ _ => .all _ _))
  let _ : Algebra R C :=
    ((algebraMap (R ⧸ Ideal.span {s ^ 8}) C).comp (algebraMap R (R ⧸ Ideal.span {s ^ 8}))).toAlgebra
  have : IsScalarTower R (R ⧸ Ideal.span {s ^ 8}) C := .of_algebraMap_eq fun _ => rfl
  obtain ⟨B₂, _, _, _, g₂, h₂, hgh₂, hsm, hsing⟩ := h6 R B Λ s hRs hΛs h hss C
    ((gb.restrictScalars R).comp Algebra.TensorProduct.includeRight) (hb.restrictScalars R) (by
      ext b
      have := congrArg (fun φ => φ ((1 : R ⧸ Ideal.span {s ^ 8}) ⊗ₜ[R] b)) hghb
      simpa using this)
  refine ⟨B₂, inferInstance, inferInstance, inferInstance, g₂.comp g, h₂, by
    rw [← AlgHom.comp_assoc, hgh₂, hgh], ?_⟩
  rw [← Ideal.radical_eq_top]
  change singularRadical R h₂ = ⊤
  have h1 : (singularRadical R h₂).map
      (Ideal.Quotient.mk ((Ideal.span {s ^ 8}).map (algebraMap R Λ))) = ⊤ := by
    rw [singularIdeal_eq_top_of_smooth, Ideal.map_top] at hsing
    exact top_le_iff.mp hsing
  have h2 : (Ideal.span {s ^ 8}).map (algebraMap R Λ) ≤ singularRadical R h₂ := by
    rw [Ideal.map_span, Set.image_singleton, Ideal.span_le, Set.singleton_subset_iff,
      SetLike.mem_coe, map_pow]
    refine Ideal.pow_mem_of_mem _ (Ideal.le_radical ?_) 8 (by norm_num)
    rw [← h₂.commutes s]
    exact Ideal.mem_map_of_mem h₂ (mem_singularIdeal_of_smooth_away _ hsm)
  have := Ideal.comap_map_of_surjective
    (Ideal.Quotient.mk ((Ideal.span {s ^ 8}).map (algebraMap R Λ))) Ideal.Quotient.mk_surjective
    (singularRadical R h₂)
  rw [h1, Ideal.comap_top, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr h2] at this
  exact this.symm

end KeyLemma

section Main

/-- Stacks 07F5 (Lemma 8.4): the reduction of Popescu's theorem to the case of a field base,
assuming Lemmas 2.8, 5.3 (nilpotent lifting), the strictly standard desingularization step and
Lemma 8.3. -/
theorem reductionToField_of (h3 : SingularIdealFactorizationStatement.{u})
    (h5 : NilpotentLiftingStatement.{u}) (h6 : StrictlyStandardDesingularizationStatement.{u})
    (h9 : LocalizationStandardDescentStatement.{u}) : PopescuReductionToFieldStatement.{u} := by
  intro hfield R Λ _ _ _ _ _ hreg
  have key : ∀ I : Ideal R, HasSmoothFactorizations (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ)) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨I, hI, hmax⟩ := set_has_maximal_iff_noetherian.mpr (inferInstance : IsNoetherian R R)
      {I : Ideal R | ¬ HasSmoothFactorizations (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ))} hcon
    apply hI
    refine hasSmoothFactorizations_of_quotients hfield h3 h5 h6 h9 (regularAlgebra_quotient I hreg)
      fun Jb hJb => ?_
    obtain ⟨J, hIJ, rfl⟩ : ∃ J : Ideal R, I ≤ J ∧ Jb = J.map (Ideal.Quotient.mk I) :=
      ⟨Jb.comap (Ideal.Quotient.mk I), fun x hx => by
        rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]; exact Jb.zero_mem,
        (Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective Jb).symm⟩
    have hlt : I < J := by
      refine lt_of_le_of_ne hIJ fun hIJ' => hJb ?_
      subst hIJ'
      rw [Ideal.map_quotient_self]
    have hJ : HasSmoothFactorizations (R ⧸ J) (Λ ⧸ J.map (algebraMap R Λ)) := by
      by_contra hJ
      exact hmax J hJ hlt
    have heq : Ideal.map (algebraMap (R ⧸ I) (Λ ⧸ Ideal.map (algebraMap R Λ) I))
          (Ideal.map (Ideal.Quotient.mk I) J) =
        Ideal.map (Ideal.Quotient.mk (Ideal.map (algebraMap R Λ) I))
          (Ideal.map (algebraMap R Λ) J) := by
      rw [Ideal.map_map, Ideal.map_map]
      rfl
    refine hasSmoothFactorizations_of_ringEquiv' (DoubleQuot.quotQuotEquivQuotOfLE hIJ)
      ((Ideal.quotEquivOfEq heq).trans
        (DoubleQuot.quotQuotEquivQuotOfLE (Ideal.map_mono hIJ))) (fun r => ?_) hJ
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    rfl
  refine hasSmoothFactorizations_of_ringEquiv' (RingEquiv.quotientBot R).symm
    ((RingEquiv.quotientBot Λ).symm.trans (Ideal.quotEquivOfEq Ideal.map_bot.symm))
    (fun r => rfl) (key ⊥)

end Main

end Langlands.CommutativeAlgebra.Popescu
