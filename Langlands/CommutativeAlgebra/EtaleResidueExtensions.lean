import Langlands.CommutativeAlgebra.EtaleLocalSections

/-! # Realizing finite separable residue extensions by etale algebras -/

universe u

open Polynomial
open scoped IntermediateField

noncomputable section

namespace Langlands.CommutativeAlgebra

open Algebra EtaleLocalSections

/-- A prescribed finite separable extension of a residue field is the actual
residue field of a point of an etale algebra over the original ring. -/
theorem exists_etale_residue_extension (R : Type u) [CommRing R] (𝔭 : Ideal R) [𝔭.IsPrime]
    (K : Type u) [Field K] [Algebra 𝔭.ResidueField K]
    [Algebra R K] [IsScalarTower R 𝔭.ResidueField K]
    [FiniteDimensional 𝔭.ResidueField K] [Algebra.IsSeparable 𝔭.ResidueField K] :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A), Etale R A ∧
      ∃ (q : PrimeSpectrum A) (e : q.asIdeal.ResidueField ≃+* K),
        q.asIdeal.comap (algebraMap R A) = 𝔭 ∧
        ∀ r : R, e (algebraMap A q.asIdeal.ResidueField (algebraMap R A r)) =
          algebraMap R K r := by
  classical
  let κ := 𝔭.ResidueField
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element κ K
  let mbar := minpoly κ θ
  obtain ⟨b, -, β, hβ, hc⟩ := exists_away_lift 𝔭 (mbar.support.image mbar.coeff)
  have hmlift : mbar ∈ Polynomial.lifts β := by
    rw [lifts_iff_coeff_lifts]
    intro k
    by_cases hk : k ∈ mbar.support
    · exact hc _ (Finset.mem_image_of_mem _ hk)
    · rw [notMem_support_iff.mp hk]
      exact ⟨0, map_zero β⟩
  obtain ⟨m, hmmap, -, hmmon⟩ := lifts_and_degree_eq_and_monic hmlift
    (minpoly.monic (Algebra.IsIntegral.isIntegral θ))
  let Rb := Localization.Away b
  let E : StandardEtalePair Rb := ⟨m, hmmon, derivative m, ⟨1, 0, 1, by simp⟩⟩
  let A := E.Ring
  let : Algebra R A := ((algebraMap Rb A).comp (algebraMap R Rb)).toAlgebra
  have : IsScalarTower R Rb A := .of_algebraMap_eq fun _ => rfl
  let : Algebra Rb K := ((algebraMap κ K).comp β).toAlgebra
  have : IsScalarTower R Rb K := .of_algebraMap_eq fun r => by
    change algebraMap R K r = algebraMap κ K (β (algebraMap R Rb r))
    rw [← RingHom.comp_apply β, hβ, ← IsScalarTower.algebraMap_apply R κ K]
  have hev : ∀ f : Rb[X], aeval θ f = aeval θ (f.map β) := fun f => by
    rw [aeval_def, aeval_def, eval₂_map]
    rfl
  have hE : E.HasMap θ := by
    refine ⟨?_, ?_⟩
    · change aeval θ m = 0
      rw [hev, hmmap]
      exact minpoly.aeval κ θ
    · change IsUnit (aeval θ (derivative m))
      rw [hev, ← derivative_map, hmmap]
      exact isUnit_iff_ne_zero.mpr
        ((Algebra.IsSeparable.isSeparable κ θ).aeval_derivative_ne_zero (minpoly.aeval κ θ))
  let ρ : A →ₐ[R] K := (E.lift θ hE).restrictScalars R
  let q : PrimeSpectrum A := ⟨RingHom.ker ρ.toRingHom, RingHom.ker_isPrime _⟩
  have : q.asIdeal.IsPrime := q.isPrime
  have hρcomp : ρ.toRingHom.comp (algebraMap R A) = algebraMap R K := by
    ext r
    exact ρ.commutes r
  have hq : q.asIdeal.comap (algebraMap R A) = 𝔭 := by
    change (RingHom.ker ρ.toRingHom).comap (algebraMap R A) = 𝔭
    rw [RingHom.comap_ker, hρcomp]
    rw [IsScalarTower.algebraMap_eq R κ K,
      RingHom.ker_comp_of_injective _ (algebraMap κ K).injective,
      Ideal.ker_algebraMap_residueField]
  let η : q.asIdeal.ResidueField →+* K := Ideal.ResidueField.lift q.asIdeal ρ.toRingHom
    le_rfl (fun r hr => isUnit_iff_ne_zero.mpr hr)
  have hη (a : A) : η (algebraMap A q.asIdeal.ResidueField a) = ρ a :=
    Ideal.ResidueField.lift_algebraMap ..
  let : Algebra κ q.asIdeal.ResidueField :=
    (Ideal.ResidueField.map 𝔭 q.asIdeal (algebraMap R A) hq.symm).toAlgebra
  have hηκ : η.comp (algebraMap κ q.asIdeal.ResidueField) = algebraMap κ K := by
    apply Ideal.ResidueField.ringHom_ext
    ext r
    change η (Ideal.ResidueField.map 𝔭 q.asIdeal (algebraMap R A) hq.symm
      (algebraMap R κ r)) = algebraMap κ K (algebraMap R κ r)
    rw [Ideal.ResidueField.map_algebraMap, hη, ρ.commutes,
      ← IsScalarTower.algebraMap_apply R κ K]
  let ηₐ : q.asIdeal.ResidueField →ₐ[κ] K :=
    ⟨η, fun c => congrArg (fun h : κ →+* K => h c) hηκ⟩
  have hθrange : θ ∈ ηₐ.fieldRange := by
    refine ⟨algebraMap A q.asIdeal.ResidueField E.X, ?_⟩
    change η (algebraMap A q.asIdeal.ResidueField E.X) = θ
    rw [hη]
    exact E.lift_X θ hE
  have hrange : ηₐ.fieldRange = ⊤ := by
    apply top_unique
    rw [← hθ]
    exact IntermediateField.adjoin_simple_le_iff.mpr hθrange
  have hsurj : Function.Surjective η := by
    intro y
    exact show y ∈ ηₐ.fieldRange from hrange ▸ IntermediateField.mem_top
  let e : q.asIdeal.ResidueField ≃+* K := RingEquiv.ofBijective η ⟨η.injective, hsurj⟩
  refine ⟨A, inferInstance, inferInstance, Etale.comp R Rb A, q, e, hq, fun r => ?_⟩
  change η (algebraMap A q.asIdeal.ResidueField (algebraMap R A r)) = _
  rw [hη, ρ.commutes]

end Langlands.CommutativeAlgebra
