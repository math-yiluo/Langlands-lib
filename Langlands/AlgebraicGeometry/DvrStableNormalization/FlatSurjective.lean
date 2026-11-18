import Langlands.AlgebraicGeometry.DvrStableNormalization.Model

/-! # Flatness and surjectivity of the normalization model -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.DvrStableNormalization

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- An algebra over a DVR embedding into an algebra where a uniformizer is invertible is flat. -/
theorem flat_of_injective_of_isUnit {B C : Type*} [CommRing B] [CommRing C] [Algebra R B]
    [Algebra R C] (ι : B →ₐ[R] C) (hι : Function.Injective ι) {ϖ : R} (hϖ : Irreducible ϖ)
    (hu : IsUnit (algebraMap R C ϖ)) : Module.Flat R B := by
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
  intro b hb
  obtain ⟨⟨r, hr⟩, hrb⟩ := (Submodule.mem_torsion_iff b).mp hb
  have hr0 : r ≠ 0 := nonZeroDivisors.ne_zero hr
  obtain ⟨n, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr0 hϖ
  have hunit : IsUnit (algebraMap R C r) := by
    rw [hv, map_mul, map_pow]
    exact (v.isUnit.map _).mul (hu.pow n)
  have h1 : algebraMap R C r * ι b = 0 := by
    rw [← Algebra.smul_def, ← map_smul]
    change ι (r • b) = 0
    rw [show r • b = 0 from hrb, map_zero]
  have h2 : ι b = 0 := (hunit.mul_right_eq_zero).mp h1
  rw [Submodule.mem_bot]
  exact hι (h2.trans (map_zero ι).symm)

/-- A scheme over a DVR whose sections embed into those of a scheme over the fraction field
is flat. -/
theorem flat_of_injective_generic {Y Z : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R))
    (τ : Z ⟶ Y) (g : Z ⟶ Spec (CommRingCat.of (FractionRing R)))
    (hτg : τ ≫ f = g ≫ Spec.algebraMap R (FractionRing R))
    (hinj : ∀ V : Y.affineOpens, Function.Injective (τ.app V.1)) : Flat f := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  refine HasRingHomProperty.of_iSup_eq_top (P := @Flat) (fun V : Y.affineOpens => V)
    (iSup_affineOpens_eq_top Y) fun V => ?_
  let e := Scheme.ΓSpecIso (CommRingCat.of R)
  let φ : R →+* Γ(Y, V.1) := (f.appLE ⊤ V.1 le_top).hom.comp e.inv.hom
  have hφeq : (f.appLE ⊤ V.1 le_top).hom = φ.comp e.hom.hom := by
    ext x
    simp only [φ, RingHom.comp_apply]
    congr 1
    exact (e.hom_inv_id_apply x).symm
  suffices hflat : φ.Flat by
    rw [hφeq]
    exact RingHom.Flat.comp (RingHom.Flat.of_bijective
      (ConcreteCategory.bijective_of_isIso e.hom)) hflat
  let ψ : R →+* Γ(Z, τ ⁻¹ᵁ V.1) := (τ.app V.1).hom.comp φ
  let := φ.toAlgebra
  let := ψ.toAlgebra
  let ι : Γ(Y, V.1) →ₐ[R] Γ(Z, τ ⁻¹ᵁ V.1) :=
    { (τ.app V.1).hom with commutes' := fun r => rfl }
  have hψ : ψ ϖ = (g.appLE ⊤ (τ ⁻¹ᵁ V.1) le_top).hom
      ((Spec.algebraMap R (FractionRing R)).appTop (e.inv ϖ)) := by
    have h1 : f.appLE ⊤ V.1 le_top ≫ τ.app V.1 = (τ ≫ f).appLE ⊤ (τ ⁻¹ᵁ V.1) le_top := by
      rw [Scheme.Hom.app_eq_appLE]
      exact Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
    have key : ∀ h : Z ⟶ Spec (CommRingCat.of R), h = g ≫ Spec.algebraMap R (FractionRing R) →
        h.appLE ⊤ (τ ⁻¹ᵁ V.1) le_top =
          (Spec.algebraMap R (FractionRing R)).appTop ≫ g.appLE ⊤ (τ ⁻¹ᵁ V.1) le_top := by
      rintro h rfl
      exact Scheme.Hom.comp_appLE _ _ _ _ _
    have h2 := key (τ ≫ f) hτg
    change (f.appLE ⊤ V.1 le_top ≫ τ.app V.1) (e.inv ϖ) = _
    rw [h1, h2]
    rfl
  have hu0 : IsUnit ((Spec.algebraMap R (FractionRing R)).appTop (e.inv ϖ)) := by
    have hnat := Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (algebraMap R (FractionRing R)))
    have : (Spec.algebraMap R (FractionRing R)).appTop (e.inv ϖ) =
        (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv (algebraMap R _ ϖ) := by
      have := congrArg (fun h => h ϖ) hnat
      rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at this
      exact this.symm
    rw [this]
    refine IsUnit.map _ ?_
    exact isUnit_iff_ne_zero.mpr
      ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).mpr hϖ.ne_zero)
  have hu : IsUnit (algebraMap R Γ(Z, τ ⁻¹ᵁ V.1) ϖ) := by
    change IsUnit (ψ ϖ)
    rw [hψ]
    exact hu0.map _
  exact flat_of_injective_of_isUnit ι (hinj V) hϖ hu

/-- The structure map of the normalization model is flat. -/
instance flat_source (X : Over (Spec (CommRingCat.of R))) : Flat (source X).hom := by
  have hdom : IsSchemeTheoreticallyDominant (genericι X).toNormalization :=
    ⟨Scheme.Hom.ker_toNormalization _⟩
  refine flat_of_injective_generic (source X).hom (genericι X).toNormalization
    (pullback.snd X.hom (Spec.algebraMap R (FractionRing R))) ?_
    fun V => (genericι X).toNormalization.app_injective V.1
  change (genericι X).toNormalization ≫ (genericι X).fromNormalization ≫ X.hom = _
  rw [Scheme.Hom.toNormalization_fromNormalization_assoc]
  exact pullback.condition

/-- The normalization map of a flat scheme over a DVR is surjective. -/
instance surjective_map (X : Over (Spec (CommRingCat.of R))) [Flat X.hom] :
    Surjective (map X).left := by
  constructor
  have hclosed : IsClosed (Set.range (genericι X).fromNormalization) :=
    (genericι X).fromNormalization.isClosedMap.isClosed_range
  have hsub : Set.range (genericι X) ⊆ Set.range (genericι X).fromNormalization := by
    rintro _ ⟨y, rfl⟩
    exact ⟨(genericι X).toNormalization y, by
      rw [← Scheme.Hom.comp_apply, Scheme.Hom.toNormalization_fromNormalization]⟩
  intro x
  let ξ : Spec (CommRingCat.of R) := ⟨⊥, Ideal.isPrime_bot⟩
  have hξ : ξ ⤳ X.hom x := (PrimeSpectrum.le_iff_specializes _ _).mp bot_le
  obtain ⟨x', hx', hfx'⟩ := Flat.generalizingMap X.hom hξ
  have hx'mem : x' ∈ Set.range (genericι X) := by
    have h : x' ∈ (genericι X).opensRange := by
      rw [Scheme.Hom.opensRange_pullbackFst]
      change X.hom x' ∈ (Spec.algebraMap R (FractionRing R)).opensRange
      rw [hfx']
      refine ⟨⟨⊥, Ideal.isPrime_bot⟩, ?_⟩
      apply PrimeSpectrum.ext
      exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R (FractionRing R))
    exact h
  have hx : x ∈ closure (Set.range (genericι X)) :=
    closure_mono (Set.singleton_subset_iff.mpr hx'mem) (specializes_iff_mem_closure.mp hx')
  exact hclosed.closure_subset_iff.mpr hsub hx

end Langlands.AlgebraicGeometry.DvrStableNormalization
