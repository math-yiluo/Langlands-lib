import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Langlands.Cohomology.ModuleComplex.FibreH0RestrictionSpreadStatement
import Langlands.Cohomology.ModuleComplex.FibreH0RestrictionSpread.Model

/-!
# Spreading out a degree-zero restriction isomorphism from a fibre

Proof of `FibreH0RestrictionSpreadStatement`. Near the kernel `p` of the field point
`φ₀ : R →+* k`, the three complexes have finite free models over one localization `A = R[1/r]`
whose term ranks are the homology dimensions over the residue field `κ(p)`. These models have
zero differentials after scalar extension to `κ(p)`, hence also to `k`, which turns the
hypotheses into those of `exists_bijective_of_finiteFree`. The element it produces in `A` is
cleared of denominators to give the required element of `R`.
-/

universe u

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace Langlands.Cohomology.ModuleComplex.FibreH0Spread

variable {R : Type u} [CommRing R]

/-- A finite free model of `K` with term ranks the residue-field homology dimensions exists after
inverting one element outside a prime, with the ranks recorded as a separate function. -/
lemma exists_hasModel_rank {K : CochainComplex (ModuleCat.{u} R) ℤ} (hK : IsStrictlyPerfect K)
    (p : Ideal R) [p.IsPrime] :
    ∃ r : R, r ∉ p ∧ ∃ n : ℤ → ℕ, HasModel (algebraMap R (Localization.Away r)) K n ∧
      ∀ i, n i = Module.finrank p.ResidueField
        (((baseChange (algebraMap R p.ResidueField)).obj K).homology i) := by
  obtain ⟨r, hr, h⟩ := exists_hasModel hK p
  exact ⟨r, hr, _, h, fun _ ↦ rfl⟩

/-- A module linearly equivalent to `Fin n → F` over a field `F` has dimension `n`. -/
lemma eq_finrank_of_nonempty_equiv {F : Type u} [Field F] {M : Type u} [AddCommGroup M]
    [Module F M] {n : ℕ} (h : Nonempty (M ≃ₗ[F] (Fin n → F))) : n = Module.finrank F M := by
  obtain ⟨e⟩ := h
  rw [e.finrank_eq, Module.finrank_fin_fun F]

/-- A further scalar extension of a complex with zero differentials has zero differentials. -/
lemma baseChange_comp_d_eq_zero {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (β : A →+* B) (ι : B →+* C) {Q : CochainComplex (ModuleCat.{u} A) ℤ}
    (hd : ∀ i j : ℤ, ((baseChange β).obj Q).d i j = 0) (i j : ℤ) :
    ((baseChange (ι.comp β)).obj Q).d i j = 0 := by
  let E := (baseChangeCompIso β ι).app Q
  have h₁ : ((baseChange β ⋙ baseChange ι).obj Q).d i j = 0 := by
    change (ModuleCat.extendScalars ι).map (((baseChange β).obj Q).d i j) = 0
    rw [hd, CategoryTheory.Functor.map_zero]
  have h₂ : E.hom.f j ≫ E.inv.f j = 𝟙 _ := by
    rw [← HomologicalComplex.comp_f, E.hom_inv_id, HomologicalComplex.id_f]
  rw [← Category.comp_id (((baseChange (ι.comp β)).obj Q).d i j), ← h₂, ← Category.assoc,
    ← E.hom.comm, h₁, Limits.comp_zero, Limits.zero_comp]

variable {A : Type u} [CommRing A] {α : R →+* A}

/-- If the term ranks of a model equal the homology dimensions of the modelled complex over a
field `F`, then the scalar extension of the model to `F` has zero differentials. -/
lemma d_eq_zero_of_finrank {F : Type u} [Field F] {K : CochainComplex (ModuleCat.{u} R) ℤ}
    {P : CochainComplex (ModuleCat.{u} A) ℤ} (e : HomotopyEquiv P ((baseChange α).obj K))
    {n : ℤ → ℕ} (hn : ∀ i, Nonempty (P.X i ≃ₗ[A] (Fin (n i) → A))) (β : A →+* F)
    (γ : R →+* F) (hγ : β.comp α = γ)
    (hrank : ∀ i, n i = Module.finrank F (((baseChange γ).obj K).homology i)) (i j : ℤ) :
    ((baseChange β).obj P).d i j = 0 := by
  by_cases hij : i + 1 = j
  · subst hij
    obtain ⟨ei⟩ := nonempty_extendScalars_equiv β (hn i).some
    obtain ⟨eH⟩ := nonempty_homology_equiv_of_model e β γ hγ i
    have : Module.Finite F (((baseChange β).obj P).X i) := Module.Finite.equiv ei.symm
    have h₁ : Module.finrank F (((baseChange β).obj P).X i) = n i :=
      ei.finrank_eq.trans (Module.finrank_fin_fun F)
    have h₂ : Module.finrank F (((baseChange β).obj P).homology i) = n i :=
      eH.finrank_eq.trans (hrank i).symm
    exact d_eq_zero_of_finrank_homology _ i (h₂.trans h₁.symm)
  · exact ((baseChange β).obj P).shape _ _ hij

/-- If a scalar extension of a model has zero differentials, the homology of the corresponding
scalar extension of the modelled complex is free of the term rank. -/
lemma nonempty_homology_equiv_fin {T : Type u} [CommRing T]
    {K : CochainComplex (ModuleCat.{u} R) ℤ} {P : CochainComplex (ModuleCat.{u} A) ℤ}
    (e : HomotopyEquiv P ((baseChange α).obj K)) {n : ℤ → ℕ}
    (hn : ∀ i, Nonempty (P.X i ≃ₗ[A] (Fin (n i) → A))) (β : A →+* T) (γ : R →+* T)
    (hγ : β.comp α = γ) (hd : ∀ i j : ℤ, ((baseChange β).obj P).d i j = 0) (i : ℤ) :
    Nonempty ((((baseChange γ).obj K).homology i) ≃ₗ[T] (Fin (n i) → T)) := by
  obtain ⟨ei⟩ := nonempty_extendScalars_equiv β (hn i).some
  obtain ⟨eH⟩ := nonempty_homology_equiv_of_model e β γ hγ i
  exact ⟨eH.symm ≪≫ₗ (termIsoHomology _ i (hd _ _) (hd _ _)).toLinearEquiv.symm ≪≫ₗ ei⟩

/-- A model whose term ranks are the residue-field homology dimensions has zero differentials
after scalar extension to any field `k` through the residue field, and its term ranks are then
the homology dimensions over `k`. -/
lemma fibre_data {F k : Type u} [Field F] [Field k] {K : CochainComplex (ModuleCat.{u} R) ℤ}
    {P : CochainComplex (ModuleCat.{u} A) ℤ} (e : HomotopyEquiv P ((baseChange α).obj K))
    {n : ℤ → ℕ} (hn : ∀ i, Nonempty (P.X i ≃ₗ[A] (Fin (n i) → A))) (ρ : A →+* F)
    (γ : R →+* F) (hγ : ρ.comp α = γ)
    (hrank : ∀ i, n i = Module.finrank F (((baseChange γ).obj K).homology i)) (ι : F →+* k)
    (φ₀ : R →+* k) (hφ : (ι.comp ρ).comp α = φ₀) :
    (∀ i j : ℤ, ((baseChange (ι.comp ρ)).obj P).d i j = 0) ∧
      ∀ i, n i = Module.finrank k (((baseChange φ₀).obj K).homology i) := by
  have hd := baseChange_comp_d_eq_zero ρ ι (d_eq_zero_of_finrank e hn ρ γ hγ hrank)
  exact ⟨hd, fun i ↦
    eq_finrank_of_nonempty_equiv (nonempty_homology_equiv_fin e hn _ φ₀ hφ hd i)⟩

/-- A term of rank equal to the dimension of a vanishing homology module is zero. -/
lemma isZero_X_of_isZero_homology {k : Type u} [Field k] {M : ModuleCat.{u} k}
    {P : CochainComplex (ModuleCat.{u} A) ℤ} {n : ℤ → ℕ}
    (hn : ∀ i, Nonempty (P.X i ≃ₗ[A] (Fin (n i) → A))) (i : ℤ)
    (hrank : n i = Module.finrank k M) (hz : IsZero M) : IsZero (P.X i) := by
  have : Subsingleton M := ModuleCat.isZero_iff_subsingleton.1 hz
  have h0 : n i = 0 := hrank.trans Module.finrank_zero_of_subsingleton
  have : Subsingleton (Fin (n i) → A) := by
    rw [h0]
    infer_instance
  have : Subsingleton (P.X i) := (hn i).some.toEquiv.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

/-- A term of rank equal to the dimension of a homology module free of rank one is free of rank
one. -/
lemma nonempty_X_equiv_of_homology {k : Type u} [Field k] {M : ModuleCat.{u} k}
    {P : CochainComplex (ModuleCat.{u} A) ℤ} {n : ℤ → ℕ}
    (hn : ∀ i, Nonempty (P.X i ≃ₗ[A] (Fin (n i) → A))) (i : ℤ)
    (hrank : n i = Module.finrank k M) (hM : Nonempty (M ≃ₗ[k] k)) :
    Nonempty (P.X i ≃ₗ[A] (Fin 1 → A)) := by
  obtain ⟨eM⟩ := hM
  have h1 : n i = 1 := hrank.trans (eM.finrank_eq.trans (Module.finrank_self k))
  obtain ⟨ei⟩ := hn i
  rw [h1] at ei
  exact ⟨ei⟩

/-- The spreading statement for a degree-zero restriction isomorphism detected on a fibre. -/
theorem fibreH0RestrictionSpread : FibreH0RestrictionSpreadStatement.{u} := by
  intro R _ K K₁ K₂ hK hK₁ hK₂ ψ₁ ψ₂ k _ φ₀ hneg hneg₁ hneg₂ hH₁ hH₂ h0 h1
  obtain ⟨p, hp⟩ : ∃ p : Ideal R, p = RingHom.ker φ₀ := ⟨_, rfl⟩
  have : p.IsPrime := hp ▸ RingHom.ker_isPrime φ₀
  have hmem : ∀ x, x ∉ p ↔ φ₀ x ≠ 0 := fun x ↦ by rw [hp, RingHom.mem_ker]
  -- Finite free models near `p`, moved to one localization `A = R[1/r]`.
  obtain ⟨r₀, hr₀, n, hm, hrank⟩ := exists_hasModel_rank hK p
  obtain ⟨r₁, hr₁, n₁, hm₁, hrank₁⟩ := exists_hasModel_rank hK₁ p
  obtain ⟨r₂, hr₂, n₂, hm₂, hrank₂⟩ := exists_hasModel_rank hK₂ p
  obtain ⟨r, hr_def⟩ : ∃ r : R, r = r₀ * r₁ * r₂ := ⟨_, rfl⟩
  have hr : φ₀ r ≠ 0 := by
    rw [hr_def, map_mul, map_mul]
    exact mul_ne_zero (mul_ne_zero ((hmem _).1 hr₀) ((hmem _).1 hr₁)) ((hmem _).1 hr₂)
  obtain ⟨P, hP, ⟨e⟩, hn⟩ := hm.of_dvd (s := r) (hr_def ▸ (dvd_mul_right r₀ r₁).mul_right r₂)
  obtain ⟨P₁, hP₁, ⟨e₁⟩, hn₁⟩ :=
    hm₁.of_dvd (s := r) (hr_def ▸ (dvd_mul_left r₁ r₀).mul_right r₂)
  obtain ⟨P₂, hP₂, ⟨e₂⟩, hn₂⟩ := hm₂.of_dvd (s := r) (hr_def ▸ dvd_mul_left r₂ (r₀ * r₁))
  let A := Localization.Away r
  let α : R →+* A := algebraMap R A
  -- The residue field `κ(p)` receives `A`, and maps to `k`.
  have hκr : IsUnit (algebraMap R p.ResidueField r) :=
    isUnit_iff_ne_zero.2 (by rw [Ne, Ideal.algebraMap_residueField_eq_zero]; exact (hmem r).2 hr)
  let ρ : A →+* p.ResidueField := IsLocalization.Away.lift r hκr
  have hρ : ρ.comp α = algebraMap R p.ResidueField :=
    IsLocalization.Away.lift_comp (S := A) r hκr
  have hf₂ : p.primeCompl ≤ (IsUnit.submonoid k).comap φ₀ := by
    intro x hx
    exact (IsUnit.mem_submonoid_iff _).2 (isUnit_iff_ne_zero.2 ((hmem x).1 hx))
  let ι : p.ResidueField →+* k := Ideal.ResidueField.lift p φ₀ (le_of_eq hp) hf₂
  have hι : ι.comp (algebraMap R p.ResidueField) = φ₀ :=
    RingHom.ext fun x ↦ Ideal.ResidueField.lift_algebraMap p φ₀ (le_of_eq hp) hf₂ x
  let φ : A →+* k := ι.comp ρ
  have hφ : φ.comp α = φ₀ := by
    rw [RingHom.comp_assoc, hρ, hι]
  -- The fibres of the models over `k` have zero differentials.
  obtain ⟨hd, hfin⟩ := fibre_data e hn ρ _ hρ hrank ι φ₀ hφ
  obtain ⟨-, hfin₁⟩ := fibre_data e₁ hn₁ ρ _ hρ hrank₁ ι φ₀ hφ
  obtain ⟨-, hfin₂⟩ := fibre_data e₂ hn₂ ρ _ hρ hrank₂ ι φ₀ hφ
  -- The terms in degree `-1` vanish and the terms in degree `0` have rank one.
  have hz := isZero_X_of_isZero_homology hn (-1) (hfin (-1)) (hneg (-1) (by norm_num))
  have hz₁ := isZero_X_of_isZero_homology hn₁ (-1) (hfin₁ (-1)) (hneg₁ (-1) (by norm_num))
  have hz₂ := isZero_X_of_isZero_homology hn₂ (-1) (hfin₂ (-1)) (hneg₂ (-1) (by norm_num))
  obtain ⟨E₁⟩ := nonempty_X_equiv_of_homology hn₁ 0 (hfin₁ 0) (hH₁ k φ₀)
  obtain ⟨E₂⟩ := nonempty_X_equiv_of_homology hn₂ 0 (hfin₂ 0) (hH₂ k φ₀)
  obtain ⟨E₀⟩ := nonempty_X_equiv_of_homology hn 0 (hfin 0)
    (by
      obtain ⟨F⟩ := hH₁ k φ₀
      exact ⟨LinearEquiv.ofBijective _ h0 ≪≫ₗ F⟩)
  -- Universal rank-one degree-zero homology of the models of `K₁` and `K₂`.
  have hH₁' : ∀ (T : Type u) [CommRing T] (β : A →+* T),
      Nonempty ((((baseChange β).obj P₁).homology 0) ≃ₗ[T] T) := by
    intro T _ β
    obtain ⟨E⟩ := nonempty_homology_equiv_of_model e₁ β (β.comp α) rfl 0
    obtain ⟨E'⟩ := hH₁ T (β.comp α)
    exact ⟨E ≪≫ₗ E'⟩
  have hH₂' : ∀ (T : Type u) [CommRing T] (β : A →+* T),
      Nonempty ((((baseChange β).obj P₂).homology 0) ≃ₗ[T] T) := by
    intro T _ β
    obtain ⟨E⟩ := nonempty_homology_equiv_of_model e₂ β (β.comp α) rfl 0
    obtain ⟨E'⟩ := hH₂ T (β.comp α)
    exact ⟨E ≪≫ₗ E'⟩
  obtain ⟨a, ha, hbij⟩ := exists_bijective_of_finiteFree φ hP hP₁ hP₂
    (e.hom ≫ (baseChange α).map ψ₁ ≫ e₁.inv) (e.hom ≫ (baseChange α).map ψ₂ ≫ e₂.inv)
    hz hz₁ hz₂ E₀ E₁ E₂ hd hH₁' hH₂'
    ((bijective_homologyMap_iff_of_model e e₁ ψ₁ φ φ₀ hφ 0).2 h0)
    (jointly_injective_homologyMap_of_model e e₁ e₂ ψ₁ ψ₂ φ φ₀ hφ 1 h1)
  -- Clear the denominator of `a`.
  obtain ⟨m, s, hs⟩ := IsLocalization.Away.surj r a
  have hφs : φ (α s) = φ₀ s := RingHom.congr_fun hφ s
  have hφr : φ (α r) = φ₀ r := RingHom.congr_fun hφ r
  refine ⟨r * s, ?_, ?_⟩
  · rw [map_mul, ← hφs, ← hs, map_mul, map_pow, hφr]
    exact mul_ne_zero hr (mul_ne_zero ha (pow_ne_zero _ hr))
  · intro T _ φT hu
    rw [map_mul, IsUnit.mul_iff] at hu
    let β : A →+* T := IsLocalization.Away.lift r hu.1
    have hβ : β.comp α = φT := IsLocalization.Away.lift_comp (S := A) r hu.1
    have hβa : IsUnit (β a) := by
      have : β a * β (α r) ^ m = φT s := by
        rw [← map_pow, ← map_mul, hs]
        exact RingHom.congr_fun hβ s
      exact isUnit_of_mul_isUnit_left (this ▸ hu.2)
    exact (bijective_homologyMap_iff_of_model e e₁ ψ₁ β φT hβ 0).1 (hbij T β hβa)

end Langlands.Cohomology.ModuleComplex.FibreH0Spread
