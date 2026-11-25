import Langlands.GaloisCohomology.Global.BrauerSequence.HigherDegrees.LocalVanishing
import Langlands.GaloisCohomology.Global.BrauerSequence.HigherDegrees.Connecting
import Langlands.GaloisCohomology.Global.BrauerSequence.HigherDegrees.GlobalInvariant
import Langlands.GaloisCohomology.Global.BrauerSequence.CyclicLayers

/-!
# `H³(Gal(Ω/K), Ωˣ) = 0`

Let `K` be a number field and `Ω` a separable closure. Every class `x ∈ H³(Gal(Ω/K), Ωˣ)` is
inflated from a finite Galois level `E` (`exists_unitsInflation_eq`), `x = infl a`. At the level
`E`:

* `H³(Gal(E/K), J_E) = 0` (`subsingleton_relativeIdeleCohomology_three`), so by the long exact
  sequence of `0 → Eˣ → J_E → C_E → 0` the class `a` is `δ c` for some `c ∈ H²(Gal(E/K), C_E)`;
* there is a larger finite Galois level `L` with a finite place whose local degrees in `L` are
  divisible by `[E : K]` (a cyclic layer, `exists_cyclic_layer`, composed with `E`;
  `exists_le_localDegreesDvd`); there the inflation of `c` is the image of an idèle class of
  `H²(Gal(L/K), J_L)` (`relativeIdeleClassInflation_mem_range`);
* hence the inflation of `a` to `L` is `δ` of an element of the image of `H²(J_L)`, which is zero;
  and `x` is the inflation of that class, so `x = 0`.

This is Tate's theorem `H³(G_K, K̄ˣ) = 0` (Neukirch–Schmidt–Wingberg (8.1.20) and its proof;
Tate in Cassels–Fröhlich, VII §11.4), proved at finite levels from the Library's class field theory.
-/

namespace Langlands.GaloisCohomology

open CategoryTheory Limits NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open Langlands.ProfiniteCohomology Langlands.ClassFieldTheory.Global Langlands.ClassFieldTheory.Local
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic
open scoped Langlands.Global.AdelicFunctoriality.FiniteExtension

universe u

noncomputable section

/-- A number field has a finite place. -/
theorem nonempty_heightOneSpectrum (K : Type u) [Field K] [NumberField K] :
    Nonempty (HeightOneSpectrum (𝓞 K)) :=
  ⟨(placeAbove (K := ℚ) K (Rat.HeightOneSpectrum.primesEquiv.symm ⟨2, Nat.prime_two⟩)).1⟩

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

/-- Over a finite Galois level `E` there is a larger finite Galois level `L` whose local degrees
above every place of a finite set `T` of finite places are divisible by a given `m ≠ 0`. -/
theorem exists_le_localDegreesDvd_of_finset (E : IntermediateField K Ω) [FiniteDimensional K E]
    [IsGalois K E] (T : Finset (HeightOneSpectrum (𝓞 K))) (m : ℕ) (hm : m ≠ 0) :
    ∃ (L : IntermediateField K Ω) (_ : FiniteDimensional K L), IsGalois K L ∧ E ≤ L ∧
      ∀ v ∈ T, ∀ (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal],
        m ∣ localDegree L v w := by
  obtain ⟨M, hM, hMgal, -, -, hloc⟩ := exists_cyclic_layer (Ω := Ω) T m hm
  have : NumberField M := NumberField.of_module_finite K M
  have : NumberField (E ⊔ M : IntermediateField K Ω) :=
    NumberField.of_module_finite K (E ⊔ M : IntermediateField K Ω)
  refine ⟨E ⊔ M, inferInstance, inferInstance, le_sup_left, fun v hv w _ => ?_⟩
  exact localDegreesDvd_of_le (E₁ := M) le_sup_right (fun v' hv' w' _ => hloc v' hv' w') v hv w

/-- Over a finite Galois level `E` there is a larger finite Galois level `L` whose local degrees
above a given finite place `v` are all divisible by a given `m ≠ 0`. -/
theorem exists_le_localDegreesDvd (E : IntermediateField K Ω) [FiniteDimensional K E]
    [IsGalois K E] (v : HeightOneSpectrum (𝓞 K)) (m : ℕ) (hm : m ≠ 0) :
    ∃ (L : IntermediateField K Ω) (_ : FiniteDimensional K L), IsGalois K L ∧ E ≤ L ∧
      ∀ (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal], m ∣ localDegree L v w := by
  obtain ⟨L, hL, hLgal, hEL, h⟩ := exists_le_localDegreesDvd_of_finset E {v} m hm
  exact ⟨L, hL, hLgal, hEL, fun w _ => h v (Finset.mem_singleton_self v) w⟩

/-- Over a finite Galois level `E` there is a larger finite Galois level `L` with
`[E : K] ∣ [L : E]`. -/
theorem exists_le_dvd_finrank (E : IntermediateField K Ω) [FiniteDimensional K E] [IsGalois K E] :
    ∃ (L : IntermediateField K Ω) (_ : FiniteDimensional K L), IsGalois K L ∧ ∃ h : E ≤ L,
      letI : Algebra E L := (IntermediateField.inclusion h).toRingHom.toAlgebra
      Module.finrank K E ∣ Module.finrank E L := by
  obtain ⟨v⟩ := nonempty_heightOneSpectrum K
  have hpos : 0 < Module.finrank K E := Module.finrank_pos
  obtain ⟨L, hL, hLgal, hEL, hdvd⟩ :=
    exists_le_localDegreesDvd E v (Module.finrank K E * Module.finrank K E)
      (Nat.mul_ne_zero hpos.ne' hpos.ne')
  refine ⟨L, hL, hLgal, hEL, ?_⟩
  let _ : Algebra E L := (IntermediateField.inclusion hEL).toRingHom.toAlgebra
  have _ : IsScalarTower K E L := IsScalarTower.of_algebraMap_eq' rfl
  have : NumberField L := NumberField.of_module_finite K L
  have := (placeAbove L v).2
  have h1 := (hdvd (placeAbove L v).1).trans (localDegree_dvd v (placeAbove L v).1)
  rw [← Module.finrank_mul_finrank K E L] at h1
  exact Nat.dvd_of_mul_dvd_mul_left hpos h1

/-- A class of `H³(Gal(E/K), Eˣ)` at a finite Galois level `E ⊆ Ω` inflates to zero in
`H³(Gal(Ω/K), Ωˣ)`. -/
theorem unitsInflation_three_eq_zero (E : IntermediateField K Ω) [FiniteDimensional K E]
    [IsGalois K E] (a : groupCohomology (unitsModule K E) 3) : (unitsInflation E 3).hom a = 0 := by
  classical
  have : NumberField E := NumberField.of_module_finite K E
  -- `a` comes from `H²(Gal(E/K), C_E)`
  have hX := ideleCoefficientSequence_shortExact K E
  have h1 : principalIdeleCohomologyMap K E 3 a = 0 :=
    (subsingleton_relativeIdeleCohomology_three K E).elim _ _
  obtain ⟨c, hc⟩ : ∃ c : relativeIdeleClassCohomology K E 2,
      groupCohomology.δ hX 2 3 rfl c = a := by
    have hex :=
      (groupCohomology.mapShortComplex₁_exact hX (i := 2) (j := 3) rfl).moduleCat_range_eq_ker
    have ha : a ∈ LinearMap.ker (groupCohomology.mapShortComplex₁ hX (i := 2) (j := 3) rfl).g.hom :=
      h1
    rw [← hex] at ha
    exact ha
  -- a larger level where `c` lifts to the idèles
  obtain ⟨v⟩ := nonempty_heightOneSpectrum K
  obtain ⟨L, hL, hLgal, hEL, hdvd⟩ :=
    exists_le_localDegreesDvd E v (Module.finrank K E) Module.finrank_pos.ne'
  have : NumberField L := NumberField.of_module_finite K L
  let _ : Algebra E L := (IntermediateField.inclusion hEL).toRingHom.toAlgebra
  have _ : IsScalarTower K E L := IsScalarTower.of_algebraMap_eq' rfl
  have := (placeAbove L v).2
  obtain ⟨y, hy⟩ := relativeIdeleClassInflation_mem_range (F := K) (E := E) (L := L) v
    (hdvd (placeAbove L v).1) c
  -- the inflation of `a` to `L` vanishes
  have h4 : relativeInflation K E L 3 a = 0 := by
    rw [← hc, relativeInflation_δ_apply, ← hy]
    exact ConcreteCategory.congr_hom
      (groupCohomology.mapShortComplex₃ (ideleCoefficientSequence_shortExact K L)
        (i := 2) (j := 3) rfl).zero y
  have h5 := ConcreteCategory.congr_hom (unitsInflationOfLE_comp_unitsInflation hEL 3) a
  rw [← h5]
  change (unitsInflation L 3).hom ((unitsInflationOfLE hEL 3).hom a) = 0
  rw [unitsInflationOfLE_eq_relativeInflation hEL 3]
  change (unitsInflation L 3).hom (relativeInflation K E L 3 a) = 0
  rw [h4, map_zero]

/-- **`H³(Gal(Ω/K), Ωˣ) = 0`** for a number field `K` and a separable closure `Ω`. -/
theorem subsingleton_cohomology_three_unitsModule :
    Subsingleton (cohomology (unitsModule K Ω) 3) := by
  suffices h : ∀ x : cohomology (unitsModule K Ω) 3, x = 0 from
    ⟨fun a b => (h a).trans (h b).symm⟩
  intro x
  obtain ⟨E, a, rfl⟩ := exists_unitsInflation_eq 3 x
  exact unitsInflation_three_eq_zero E.toIntermediateField a

end

end Langlands.GaloisCohomology
