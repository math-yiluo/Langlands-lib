import Langlands.GaloisCohomology.Global.Units.DivisorSequence
import Langlands.ClassFieldTheory.Global.Artin.PrincipalIdeal

/-!
# The divisor class group of `K_S` prime to `S` is trivial: capitulation at finite levels

Let `K` be a number field, `Ω` a separably closed Galois extension of `K` (a separable closure),
`S` a set of finite places of `K` (finite or not), `K_S ⊆ Ω` the maximal extension unramified
outside `S` and `ι : PlaceEmbeddings K Ω`. The finite levels of `K_S / K` are its finite Galois
subextensions `L` (`FiniteGaloisIntermediateField K K_S`), and a divisor of `L` prime to `S` is,
in the divisor module `sDivisorModule S ι` of the module
`Langlands.GaloisCohomology.Global.Units.DivisorMap`, a divisor function fixed by the fixing group
`U_L` of `L`; the place of `L` given by `ι` above `v ∉ S` is the indicator `zuInd S ι v U_L` at `v`
(the module `Langlands.GaloisCohomology.Global.Units.Capitulation`).

**Capitulation at finite levels** (`exists_level_forall_unitsToSDivisor_eq`). For every finite level
`L` there is a finite level `L' ⊇ L` such that every divisor of `L` prime to `S` is the divisor of a
unit of `K_S` lying in `L'`. The proof is the principal ideal theorem
(`exists_unramified_extension_forall_isPrincipal` of the module
`Langlands.ClassFieldTheory.Global.Artin.PrincipalIdeal`) applied to `L`: the extension `H / L` it
gives is unramified at every finite place, so it embeds over `L` into `K_S`
(`nonempty_algHom_maximalUnramifiedOutside_of_le`), and `L'` is a finite level containing its image.
If `h` is the class number of `L` and `W^h = (π)`, `W 𝒪_H = (α)`, then `α^h = π u` with `u` a unit
(`exists_level_forall_pow_classNumber_eq`), so `h` times the divisor of `α` is the divisor of `π`,
`h` times the place `W` (`sOrder_galUnitsHom_placeUnit`, `exists_level_forall_sOrder_eq_single`).
A divisor of `L` is an integral combination of translates of places of `L`
(`isPrincipalIn_single_of_base`).

Consequences, with no prime `ℓ` and no hypothesis on `S`:
* `unitsToSDivisor_surjective`: the divisor map `K_Sˣ → Div_S(K_S)` is onto;
* `isCapitulating_of_mem_divisorFunctions`: `IsCapitulating S ι ℓ f` for every divisor `f` and every
  `ℓ : ℕ` (with `N = 1`);
* `sUnitsDivisorSequence_shortExact`: `0 → 𝒪_Sˣ → K_Sˣ → Div_S(K_S) → 0` is a short exact sequence
  of smooth `G_S`-modules;
* `isZero_sDivisorClassModule`: the divisor class module `sDivisorClassModule S ι` is zero, and
  `K_Sˣ/𝒪_Sˣ → Div_S(K_S)` is an isomorphism (`isIso_unitsModSUnitsToSDivisor`);
* `cohomologyOneSUnitsToSPicard_surjective_of_surjective`: the surjectivity of the divisor map
  of `K_S` gives that of `H¹(G_S, 𝒪_Sˣ) → Pic(𝒪_S)` (through `ordAbove_eq_neg_sOrder`, which
  compares the two divisor maps of `K_S`).

This file imports the NYLL library (the copy under `Nyll/`) through
`Langlands.ClassFieldTheory.Global.Artin.PrincipalIdeal`.
-/

namespace Langlands.GaloisCohomology

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain

universe u

noncomputable section

section Embedding

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  [IsSepClosed Ω] (S : Set (HeightOneSpectrum (𝓞 K)))

/-- Let `L` be a finite extension of `K` with an embedding into `Ω`, in which the places outside `S`
are unramified. A finite extension `H` of `L` in which the places of `L` outside the places above
`S` are unramified has an `L`-embedding into `Ω` with image in `K_S`. -/
theorem exists_algHom_forall_mem_maximalUnramifiedOutside {L : Type*} [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [Algebra L Ω] [IsScalarTower K L Ω]
    (hL : ∀ v ∉ S, Algebra.IsUnramifiedIn (𝓞 L) v.asIdeal)
    (H : Type*) [Field H] [NumberField H] [Algebra L H] [FiniteDimensional L H]
    (hH : ∀ w ∉ finitePlacesAbove L S, Algebra.IsUnramifiedIn (𝓞 H) w.asIdeal) :
    ∃ φ : H →ₐ[L] Ω, ∀ z, φ z ∈ maximalUnramifiedOutside K Ω S := by
  have : IsGalois L Ω := IsGalois.tower_top_of_isGalois K L Ω
  let φ : H →ₐ[L] Ω := IsSepClosed.lift
  let : Algebra H Ω := φ.toRingHom.toAlgebra
  have : IsScalarTower L H Ω := IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  have : IsGalois H Ω := IsGalois.tower_top_of_isGalois L H Ω
  let E : IntermediateField L Ω := (⊥ : IntermediateField H Ω).restrictScalars L
  have : FiniteDimensional L E := FiniteDimensional.trans L H (⊥ : IntermediateField H Ω)
  have hE : IsUnramifiedOutside (finitePlacesAbove L S) E :=
    (isUnramifiedOutside_restrictScalars_iff (finitePlacesAbove L S) hH ⊥).2
      (isUnramifiedOutside_bot _)
  have : FiniteDimensional K (E.restrictScalars K) := FiniteDimensional.trans K L E
  have hEK : IsUnramifiedOutside S (E.restrictScalars K) :=
    (isUnramifiedOutside_restrictScalars_iff S hL E).2 hE
  exact ⟨φ, fun z => le_maximalUnramifiedOutside S hEK (IntermediateField.algebraMap_mem _ z)⟩

/-- A finite extension `H` of a finite subextension `L` of `K_S / K`, in which the places of `L`
outside the places above `S` are unramified, embeds over `L` into `K_S`. -/
theorem nonempty_algHom_maximalUnramifiedOutside_of_le
    (L : IntermediateField K (maximalUnramifiedOutside K Ω S)) [FiniteDimensional K L]
    (H : Type*) [Field H] [NumberField H] [Algebra L H] [FiniteDimensional L H]
    (hH : ∀ w ∉ finitePlacesAbove L S, Algebra.IsUnramifiedIn (𝓞 H) w.asIdeal) :
    Nonempty (H →ₐ[L] maximalUnramifiedOutside K Ω S) := by
  have := NumberField.of_module_finite K L
  let ιL : L →ₐ[K] Ω := (maximalUnramifiedOutside K Ω S).val.comp L.val
  let : Algebra L Ω := ιL.toRingHom.toAlgebra
  have : IsScalarTower K L Ω := IsScalarTower.of_algebraMap_eq fun r => (ιL.commutes r).symm
  obtain ⟨φ, hφ⟩ := exists_algHom_forall_mem_maximalUnramifiedOutside (Ω := Ω) (L := L) S
    (fun v hv => isUnramifiedIn_of_maximalUnramifiedOutside S L hv) H hH
  exact ⟨{ φ.toRingHom.codRestrict (maximalUnramifiedOutside K Ω S) hφ with
    commutes' := fun x => Subtype.ext (φ.commutes x) }⟩

end Embedding

section Level

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  [IsSepClosed Ω] (S : Set (HeightOneSpectrum (𝓞 K)))

/-- **Principal ideal theorem in `K_S`.** For every finite Galois level `L` of `K_S` there is a
finite Galois level `L' ⊇ L` in which every place `W` of `L` becomes principal: with `h` the class
number of `L` and `placeUnit W` the generator of `W^h`, some `x ∈ L'` has `x^h = placeUnit W · y`
with `y` an `S`-unit of `K_S`. -/
theorem exists_level_forall_pow_classNumber_eq
    (L : FiniteGaloisIntermediateField K (maximalUnramifiedOutside K Ω S)) :
    haveI := NumberField.of_module_finite K L.toIntermediateField
    ∃ L' : FiniteGaloisIntermediateField K (maximalUnramifiedOutside K Ω S), L ≤ L' ∧
      ∀ W : HeightOneSpectrum (𝓞 L.toIntermediateField), ∃ x : (maximalUnramifiedOutside K Ω S)ˣ,
        (x : maximalUnramifiedOutside K Ω S) ∈ L'.toIntermediateField ∧
        ∃ y ∈ maximalSUnits K Ω S, x ^ classNumber L.toIntermediateField =
          Units.map (L.toIntermediateField.val :
            L.toIntermediateField →* maximalUnramifiedOutside K Ω S) (placeUnit W) * y := by
  have := NumberField.of_module_finite K L.toIntermediateField
  obtain ⟨H, _, _, _, _, hun, hprin⟩ :=
    Langlands.ClassFieldTheory.Global.Artin.exists_unramified_extension_forall_isPrincipal
      L.toIntermediateField
  obtain ⟨φ⟩ := nonempty_algHom_maximalUnramifiedOutside_of_le (Ω := Ω) S L.toIntermediateField H
    fun w _ => hun w
  -- a finite Galois level containing the image of `H`
  have : FiniteDimensional L.toIntermediateField φ.fieldRange :=
    LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField φ).toLinearEquiv
  let E : IntermediateField K (maximalUnramifiedOutside K Ω S) :=
    φ.fieldRange.restrictScalars K
  have : FiniteDimensional K E := FiniteDimensional.trans K L.toIntermediateField φ.fieldRange
  obtain ⟨L', hEL'⟩ := exists_finiteGaloisIntermediateField_le E
  have hφL' : ∀ z : H, (φ z : maximalUnramifiedOutside K Ω S) ∈ L'.toIntermediateField :=
    fun z => hEL' ⟨z, rfl⟩
  have hLL' : L ≤ L' := by
    intro z hz
    have : φ (algebraMap L.toIntermediateField H ⟨z, hz⟩) = z := φ.commutes _
    rw [← this]
    exact hφL' _
  refine ⟨L', hLL', fun W => ?_⟩
  let ψ : 𝓞 H →+* maximalUnramifiedOutside K Ω S := φ.toRingHom.comp (algebraMap (𝓞 H) H)
  have hψ : Function.Injective ψ :=
    φ.toRingHom.injective.comp (FaithfulSMul.algebraMap_injective (𝓞 H) H)
  -- `α^h u = a` in `𝓞 H`, where `W 𝒪_H = (α)` and `W^h = (a)`
  obtain ⟨α, hα⟩ := (hprin W.asIdeal).principal
  have hpow := exists_pow_classNumber_eq_span W
  set a := hpow.choose
  have hspan : Ideal.span {α ^ classNumber L.toIntermediateField} =
      Ideal.span {algebraMap (𝓞 L.toIntermediateField) (𝓞 H) a} := by
    rw [← Ideal.span_singleton_pow, show Ideal.span {α} = _ from hα.symm, ← Ideal.map_pow,
      hpow.choose_spec.2, Ideal.map_span, Set.image_singleton]
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.1 hspan
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_pow (classNumber_ne_zero L.toIntermediateField), zero_mul, eq_comm,
      map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 L.toIntermediateField) (𝓞 H))] at hu
    exact hpow.choose_spec.1 hu
  let x : (maximalUnramifiedOutside K Ω S)ˣ := Units.mk0 (ψ α) ((map_ne_zero_iff ψ hψ).2 hα0)
  let y : (maximalUnramifiedOutside K Ω S)ˣ := Units.map (ψ : 𝓞 H →* _) u
  have hint : ∀ z : 𝓞 H, IsIntegral (S.integer K) (ψ z) := fun z =>
    ((RingOfIntegers.isIntegral z).map ψ.toIntAlgHom).tower_top
  have hy : y⁻¹ ∈ maximalSUnits K Ω S := by
    refine inv_mem ⟨hint _, ?_⟩
    rw [← map_inv]
    exact hint _
  refine ⟨x, hφL' _, y⁻¹, hy, ?_⟩
  rw [eq_mul_inv_iff_mul_eq]
  apply Units.ext
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0, Units.coe_map,
    MonoidHom.coe_ofClass, x, y]
  rw [← map_pow, ← map_mul, hu]
  change φ (algebraMap (𝓞 H) H (algebraMap (𝓞 L.toIntermediateField) (𝓞 H) a)) =
    L.toIntermediateField.val (algebraMap (𝓞 L.toIntermediateField) L.toIntermediateField a)
  rw [← IsScalarTower.algebraMap_apply (𝓞 L.toIntermediateField) (𝓞 H) H,
    IsScalarTower.algebraMap_apply (𝓞 L.toIntermediateField) L.toIntermediateField H, φ.commutes]
  rfl

end Level

section Divisor

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (S : Set (HeightOneSpectrum (𝓞 K))) (ι : PlaceEmbeddings K Ω)

variable {S} in
/-- `sOrder` of an integral power. -/
theorem sOrder_zpow {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S)
    (y : (maximalUnramifiedOutside K Ω S)ˣ) (m : ℤ) :
    sOrder S ι v (y ^ m) = m * sOrder S ι v y := by
  rcases Int.eq_nat_or_neg m with ⟨k, rfl | rfl⟩
  · rw [zpow_natCast, sOrder_pow ι hv]
  · have h1 := sOrder_mul ι hv (y ^ k) (y ^ (-(k : ℤ)))
    rw [← zpow_natCast, ← zpow_add, add_neg_cancel, zpow_zero, sOrder_one ι hv, zpow_natCast,
      sOrder_pow ι hv] at h1
    linarith

variable {S} in
/-- `sOrder` of an inverse. -/
theorem sOrder_inv {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S)
    (y : (maximalUnramifiedOutside K Ω S)ˣ) :
    sOrder S ι v y⁻¹ = -sOrder S ι v y := by
  have h := sOrder_mul ι hv y y⁻¹
  rw [mul_inv_cancel, sOrder_one ι hv] at h
  omega

open Classical in
/-- The divisor function of the generator `placeUnit W` of `W^h` (`W` the place of `ι` above `v` of
a finite Galois level `L`, `h` the class number of `L`) is `-h` times the indicator of `Z_v · U_L`
at `v`. -/
theorem sOrder_galUnitsHom_placeUnit
    (L : FiniteGaloisIntermediateField K (maximalUnramifiedOutside K Ω S))
    (v v' : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) (g : GaloisGroupUnramifiedOutside K Ω S) :
    haveI := NumberField.of_module_finite K L.toIntermediateField
    sOrder S ι v'.1 (galUnitsHom K _ g (Units.map
      (L.toIntermediateField.val : L.toIntermediateField →* maximalUnramifiedOutside K Ω S)
      (placeUnit (placeOfAlgHom (levelEmbedding S ι v.1 L.toIntermediateField)).1))) =
      -(classNumber L.toIntermediateField : ℤ) *
        (Pi.single v (zuInd S ι v L.toIntermediateField.fixingSubgroup) :
          {v : HeightOneSpectrum (𝓞 K) // v ∉ S} → GaloisGroupUnramifiedOutside K Ω S → ℤ)
          v' g := by
  have := NumberField.of_module_finite K L.toIntermediateField
  set j := levelEmbedding S ι v.1 L.toIntermediateField with hj
  set W := (placeOfAlgHom j).1 with hW
  set π : L.toIntermediateFieldˣ := placeUnit W with hπ
  have hval : ∀ w : HeightOneSpectrum (𝓞 L.toIntermediateField),
      w.valuation L.toIntermediateField (π : L.toIntermediateField) =
        if w = W then WithZero.exp (-(classNumber L.toIntermediateField : ℤ)) else 1 := by
    intro w
    rw [← HeightOneSpectrum.valuationOfNeZero_eq, valuationOfNeZero_placeUnit]
    split_ifs <;> rfl
  set πS : (maximalUnramifiedOutside K Ω S)ˣ :=
    Units.map (L.toIntermediateField.val :
      L.toIntermediateField →* maximalUnramifiedOutside K Ω S) π
  have hπL : (πS : maximalUnramifiedOutside K Ω S) ∈ L.toIntermediateField :=
    (π : L.toIntermediateField).2
  have hπunit : levelUnit πS hπL = π := Units.ext rfl
  set τ := levelRestrict S L g
  set j' := levelEmbedding S ι v'.1 L.toIntermediateField
  have h1 : sOrder S ι v'.1 (galUnitsHom K _ g πS) =
      placeExponent v'.1 (j'.comp (τ : L.toIntermediateField →ₐ[K] L.toIntermediateField)) π := by
    rw [sOrder_galUnitsHom_eq ι v'.2 L hπL g, hπunit, placeExponent_comp_algEquiv]
    rfl
  have h2 : placeExponent v'.1 (j'.comp (τ : L.toIntermediateField →ₐ[K] L.toIntermediateField)) π =
      if (placeOfAlgHom (j'.comp (τ : L.toIntermediateField →ₐ[K] L.toIntermediateField))).1 = W
        then -(classNumber L.toIntermediateField : ℤ) else 0 := by
    apply WithZero.exp_injective
    rw [← valuation_eq_exp_placeExponent, hval]
    split_ifs <;> simp
  have h3 :
      (placeOfAlgHom (j'.comp (τ : L.toIntermediateField →ₐ[K] L.toIntermediateField))).1 = W ↔
      v' = v ∧ ∃ z ∈ decompositionSubgroup S ι v.1,
        ∃ u ∈ L.toIntermediateField.fixingSubgroup, g = z * u := by
    constructor
    · intro hWW
      have hvv : v'.1 = v.1 := HeightOneSpectrum.ext ((placeOfAlgHom
        (j'.comp (τ : L.toIntermediateField →ₐ[K] L.toIntermediateField))).2.over.trans
          ((congrArg (fun w : HeightOneSpectrum (𝓞 L.toIntermediateField) => w.asIdeal.under (𝓞 K))
            hWW).trans (placeOfAlgHom j).2.over.symm))
      have hvv' : v' = v := Subtype.ext hvv
      subst hvv'
      refine ⟨rfl, (mem_decompositionSubgroup_mul_iff S ι v'.1 L g).2 ?_⟩
      exact (placeOfAlgHom_comp_eq_iff v'.1 j τ).1 (Subtype.ext hWW)
    · rintro ⟨rfl, hz⟩
      exact congrArg Subtype.val ((placeOfAlgHom_comp_eq_iff v'.1 j τ).2
        ((mem_decompositionSubgroup_mul_iff S ι v'.1 L g).1 hz))
  rw [h1, h2]
  by_cases hc :
    (placeOfAlgHom (j'.comp (τ : L.toIntermediateField →ₐ[K] L.toIntermediateField))).1 = W
  · obtain ⟨rfl, hz⟩ := h3.1 hc
    rw [ite_eq_left_of_eq_true _ _ (eq_true hc), Pi.single_eq_same, zuInd,
      ite_eq_left_of_eq_true _ _ (eq_true hz), mul_one]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]
    by_cases hvv : v' = v
    · subst hvv
      rw [Pi.single_eq_same, zuInd,
        ite_eq_right_of_eq_false _ _ (eq_false fun hz => hc (h3.2 ⟨rfl, hz⟩)), mul_zero]
    · rw [Pi.single_eq_of_ne hvv, Pi.zero_apply, mul_zero]

end Divisor

section LevelDivisor

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  [IsSepClosed Ω] (S : Set (HeightOneSpectrum (𝓞 K)))

open Classical in
/-- For every finite Galois level `L` there is a finite Galois level `L' ⊇ L` in which every place
of `L` outside `S` becomes principal: for each `ι` and `v ∉ S` the indicator of `Z_v · U_L` at `v`
(the place of `L` given by `ι` above `v`) is the divisor function of a unit of `K_S` lying in
`L'`. -/
theorem exists_level_forall_sOrder_eq_single
    (L : FiniteGaloisIntermediateField K (maximalUnramifiedOutside K Ω S)) :
    ∃ L' : FiniteGaloisIntermediateField K (maximalUnramifiedOutside K Ω S), L ≤ L' ∧
      ∀ (ι : PlaceEmbeddings K Ω) (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}),
        ∃ y : (maximalUnramifiedOutside K Ω S)ˣ,
          (y : maximalUnramifiedOutside K Ω S) ∈ L'.toIntermediateField ∧
          ∀ v' g, sOrder S ι v'.1 (galUnitsHom K _ g y) =
            (Pi.single v (zuInd S ι v L.toIntermediateField.fixingSubgroup) :
              {v : HeightOneSpectrum (𝓞 K) // v ∉ S} → GaloisGroupUnramifiedOutside K Ω S → ℤ)
              v' g := by
  have := NumberField.of_module_finite K L.toIntermediateField
  obtain ⟨L', hLL', hL'⟩ := exists_level_forall_pow_classNumber_eq S L
  refine ⟨L', hLL', fun ι v => ?_⟩
  obtain ⟨x, hxL', y, hy, hxy⟩ :=
    hL' (placeOfAlgHom (levelEmbedding S ι v.1 L.toIntermediateField)).1
  refine ⟨x⁻¹, ?_, fun v' g => ?_⟩
  · rw [Units.val_inv_eq_inv_val]
    exact inv_mem hxL'
  have hh : (classNumber L.toIntermediateField : ℤ) ≠ 0 := by
    exact_mod_cast classNumber_ne_zero L.toIntermediateField
  have e1 := sOrder_pow ι v'.2 (galUnitsHom K _ g x) (classNumber L.toIntermediateField)
  rw [← map_pow, hxy, map_mul, sOrder_mul ι v'.2,
    sOrder_eq_zero_of_mem ι v'.2 (galUnitsHom_mem_sUnitsOf g hy), add_zero,
    sOrder_galUnitsHom_placeUnit] at e1
  have e2 : sOrder S ι v'.1 (galUnitsHom K _ g x⁻¹) = -sOrder S ι v'.1 (galUnitsHom K _ g x) := by
    have := sOrder_mul ι v'.2 (galUnitsHom K _ g x) (galUnitsHom K _ g x⁻¹)
    rw [← map_mul, mul_inv_cancel, map_one, sOrder_one ι v'.2] at this
    omega
  rw [e2]
  apply mul_left_cancel₀ hh
  linarith

end LevelDivisor

section Principal

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (S : Set (HeightOneSpectrum (𝓞 K))) (ι : PlaceEmbeddings K Ω)

/-- A function `{v ∉ S} → G_S → ℤ` is *principal in* the finite Galois level `L'` of `K_S` if it is
the divisor function of a unit of `K_S` lying in `L'`. -/
def IsPrincipalIn (L' : FiniteGaloisIntermediateField K (maximalUnramifiedOutside K Ω S))
    (f : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} → GaloisGroupUnramifiedOutside K Ω S → ℤ) : Prop :=
  ∃ y : (maximalUnramifiedOutside K Ω S)ˣ,
    (y : maximalUnramifiedOutside K Ω S) ∈ L'.toIntermediateField ∧
    ∀ v g, sOrder S ι v.1 (galUnitsHom K _ g y) = f v g

variable {S ι} {L' : FiniteGaloisIntermediateField K (maximalUnramifiedOutside K Ω S)}

/-- `0` is principal in every level. -/
theorem isPrincipalIn_zero : IsPrincipalIn S ι L' 0 :=
  ⟨1, one_mem _, fun v g => by rw [map_one, sOrder_one ι v.2]; rfl⟩

/-- Sums of functions principal in `L'` are principal in `L'`. -/
theorem IsPrincipalIn.add
    {f g : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} → GaloisGroupUnramifiedOutside K Ω S → ℤ}
    (hf : IsPrincipalIn S ι L' f) (hg : IsPrincipalIn S ι L' g) : IsPrincipalIn S ι L' (f + g) := by
  obtain ⟨y₁, h₁, hy₁⟩ := hf
  obtain ⟨y₂, h₂, hy₂⟩ := hg
  refine ⟨y₁ * y₂, by rw [Units.val_mul]; exact mul_mem h₁ h₂, fun v x => ?_⟩
  rw [map_mul, sOrder_mul ι v.2, hy₁, hy₂, Pi.add_apply, Pi.add_apply]

/-- Integral multiples of a function principal in `L'` are principal in `L'`. -/
theorem IsPrincipalIn.zsmul
    {f : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} → GaloisGroupUnramifiedOutside K Ω S → ℤ}
    (hf : IsPrincipalIn S ι L' f) (c : ℤ) : IsPrincipalIn S ι L' (c • f) := by
  obtain ⟨y, h, hy⟩ := hf
  refine ⟨y ^ c, ?_, fun v x => ?_⟩
  · rw [Units.val_zpow_eq_zpow_val]
    exact zpow_mem h c
  rw [map_zpow, sOrder_zpow ι v.2, hy]
  rfl

/-- Finite sums of functions principal in `L'` are principal in `L'`. -/
theorem isPrincipalIn_sum {J : Type*} (T : Finset J)
    (f : J → {v : HeightOneSpectrum (𝓞 K) // v ∉ S} → GaloisGroupUnramifiedOutside K Ω S → ℤ)
    (hf : ∀ i ∈ T, IsPrincipalIn S ι L' (f i)) : IsPrincipalIn S ι L' (∑ i ∈ T, f i) := by
  classical
  induction T using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact isPrincipalIn_zero
  | insert a T ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a T)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- Right translates of a function principal in `L'` are principal in `L'` (`L'` is Galois). -/
theorem IsPrincipalIn.translate
    {f : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} → GaloisGroupUnramifiedOutside K Ω S → ℤ}
    (hf : IsPrincipalIn S ι L' f) (g : GaloisGroupUnramifiedOutside K Ω S) :
    IsPrincipalIn S ι L' (fun v x => f v (x * g)) := by
  obtain ⟨y, h, hy⟩ := hf
  refine ⟨galUnitsHom K _ g y, mem_level_galUnitsHom S L' g h, fun v x => ?_⟩
  change _ = f v (x * g)
  rw [← hy v (x * g), map_mul, Monoid.End.coe_mul, Function.comp_apply]

/-- A function principal in some level is capitulating for every `ℓ`, with `N = 1`. -/
theorem IsPrincipalIn.isCapitulating
    {f : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} → GaloisGroupUnramifiedOutside K Ω S → ℤ}
    (hf : IsPrincipalIn S ι L' f) (ℓ : ℕ) : IsCapitulating S ι ℓ f := by
  obtain ⟨y, -, hy⟩ := hf
  exact ⟨1, Nat.coprime_one_left ℓ, y, fun v g => by rw [hy, Nat.cast_one, one_mul]⟩

open Classical in
/-- If the indicator function of `Z_v · U` (at the place `v`) is principal in `L'`, so is every
function at `v` which is left `Z_v`-invariant and right `U`-invariant, for `U` open and normal. -/
theorem isPrincipalIn_single_of_base (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S})
    (U : Subgroup (GaloisGroupUnramifiedOutside K Ω S)) [hUn : U.Normal]
    (hU : IsOpen (U : Set (GaloisGroupUnramifiedOutside K Ω S)))
    (hbase : IsPrincipalIn S ι L' (Pi.single v (zuInd S ι v U)))
    (φ : GaloisGroupUnramifiedOutside K Ω S → ℤ) (hφU : ∀ x, ∀ u ∈ U, φ (x * u) = φ x)
    (hφZ : ∀ z ∈ decompositionSubgroup S ι v.1, ∀ x, φ (z * x) = φ x) :
    IsPrincipalIn S ι L' (Pi.single v φ) := by
  have : Finite (GaloisGroupUnramifiedOutside K Ω S ⧸ U) := Subgroup.quotient_finite_of_isOpen U hU
  have := Fintype.ofFinite (GaloisGroupUnramifiedOutside K Ω S ⧸ U)
  set Z := decompositionSubgroup S ι v.1 with hZ
  suffices key : ∀ n : ℕ, ∀ φ : GaloisGroupUnramifiedOutside K Ω S → ℤ,
      (∀ x, ∀ u ∈ U, φ (x * u) = φ x) → (∀ z ∈ Z, ∀ x, φ (z * x) = φ x) →
      (Finset.univ.filter (fun q : GaloisGroupUnramifiedOutside K Ω S ⧸ U =>
        ∃ x : GaloisGroupUnramifiedOutside K Ω S, (x : GaloisGroupUnramifiedOutside K Ω S ⧸ U) = q ∧
          φ x ≠ 0)).card = n → IsPrincipalIn S ι L' (Pi.single v φ) from
    key _ φ hφU hφZ rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro φ hφU hφZ hn
  by_cases h0 : ∀ x, φ x = 0
  · have : φ = 0 := funext h0
    rw [this, Pi.single_zero]
    exact isPrincipalIn_zero
  simp only [not_forall] at h0
  obtain ⟨x₀, hx₀⟩ := h0
  set χ : GaloisGroupUnramifiedOutside K Ω S → ℤ := fun g => zuInd S ι v U (g * x₀⁻¹) with hχ
  have hmemD : ∀ g, (∃ z ∈ Z, ∃ u ∈ U, g * x₀⁻¹ = z * u) ↔ ∃ z ∈ Z, ∃ u ∈ U, g = z * x₀ * u := by
    intro g
    constructor
    · rintro ⟨z, hz, u, hu, h⟩
      refine ⟨z, hz, x₀⁻¹ * u * x₀, hUn.conj_mem' u hu x₀, ?_⟩
      calc g = g * x₀⁻¹ * x₀ := by group
        _ = _ := by rw [h]; group
    · rintro ⟨z, hz, u, hu, rfl⟩
      refine ⟨z, hz, x₀ * u * x₀⁻¹, hUn.conj_mem u hu x₀, by group⟩
  have hφD : ∀ z ∈ Z, ∀ u ∈ U, φ (z * x₀ * u) = φ x₀ := by
    intro z hz u hu
    rw [hφU _ u hu, hφZ z hz]
  set ψ : GaloisGroupUnramifiedOutside K Ω S → ℤ := fun g => φ g - φ x₀ * χ g with hψ
  have hχ1 : ∀ g, χ g = if ∃ z ∈ Z, ∃ u ∈ U, g = z * x₀ * u then 1 else 0 := by
    intro g
    simp only [hχ, zuInd, ← hZ, hmemD g]
  have hsplit : Pi.single v φ = Pi.single v ψ + (φ x₀) • fun v' x =>
      (Pi.single v (zuInd S ι v U) :
        {v : HeightOneSpectrum (𝓞 K) // v ∉ S} → GaloisGroupUnramifiedOutside K Ω S → ℤ)
        v' (x * x₀⁻¹) := by
    funext v' x
    by_cases hv : v' = v
    · subst hv
      simp [hψ, hχ]
    · simp [Pi.single_eq_of_ne hv]
  rw [hsplit]
  refine IsPrincipalIn.add ?_ ((hbase.translate x₀⁻¹).zsmul (φ x₀))
  refine ih _ ?_ ψ ?_ ?_ rfl
  · rw [← hn]
    apply Finset.card_lt_card
    refine ⟨fun q hq => ?_, fun hsub => ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      obtain ⟨x, rfl, hx⟩ := hq
      refine ⟨x, rfl, fun hφx => hx ?_⟩
      have : χ x = 0 := by
        rw [hχ1]
        split_ifs with hD
        · obtain ⟨z, hz, u, hu, rfl⟩ := hD
          exact absurd (hφD z hz u hu ▸ hφx) hx₀
        · rfl
      simp [hψ, hφx, this]
    · have := hsub (Finset.mem_filter.2 ⟨Finset.mem_univ _, x₀, rfl, hx₀⟩)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
      obtain ⟨x, hx, hψx⟩ := this
      obtain ⟨u, hu, rfl⟩ : ∃ u ∈ U, x = x₀ * u := by
        have h := QuotientGroup.eq.1 hx
        refine ⟨x₀⁻¹ * x, ?_, by group⟩
        have := U.inv_mem h
        rwa [mul_inv_rev, inv_inv] at this
      apply hψx
      have hD : ∃ z ∈ Z, ∃ u' ∈ U, x₀ * u = z * x₀ * u' := ⟨1, Z.one_mem, u, hu, by rw [one_mul]⟩
      simp only [hψ, hχ1, hD, ite_true, hφU x₀ u hu, mul_one, sub_self]
  · intro x u hu
    have hAB : (∃ z ∈ Z, ∃ u' ∈ U, x * u = z * x₀ * u') ↔ ∃ z ∈ Z, ∃ u' ∈ U, x = z * x₀ * u' := by
      constructor
      · rintro ⟨z, hz, u', hu', h⟩
        refine ⟨z, hz, u' * u⁻¹, U.mul_mem hu' (U.inv_mem hu), ?_⟩
        rw [← mul_assoc, ← h, mul_inv_cancel_right]
      · rintro ⟨z, hz, u', hu', rfl⟩
        exact ⟨z, hz, u' * u, U.mul_mem hu' hu, mul_assoc _ _ _⟩
    simp only [hψ, hφU x u hu, hχ1, hAB]
  · intro z hz x
    have hAB : (∃ z' ∈ Z, ∃ u' ∈ U, z * x = z' * x₀ * u') ↔
        ∃ z' ∈ Z, ∃ u' ∈ U, x = z' * x₀ * u' := by
      constructor
      · rintro ⟨z', hz', u', hu', h⟩
        refine ⟨z⁻¹ * z', Z.mul_mem (Z.inv_mem hz) hz', u', hu', ?_⟩
        simp only [mul_assoc] at h ⊢
        rw [← h, inv_mul_cancel_left]
      · rintro ⟨z', hz', u', hu', rfl⟩
        exact ⟨z * z', Z.mul_mem hz hz', u', hu', by simp only [mul_assoc]⟩
    simp only [hψ, hφZ z hz, hχ1, hAB]

end Principal

section Main

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  [IsSepClosed Ω] (S : Set (HeightOneSpectrum (𝓞 K)))

/-- **Capitulation at finite levels.** For every finite Galois level `L` of `K_S` there is a finite
Galois level `L' ⊇ L` such that every divisor of `L` prime to `S` (a divisor of `K_S` fixed by the
fixing group of `L`) is the divisor of a unit of `K_S` lying in `L'`. -/
theorem exists_level_forall_unitsToSDivisor_eq
    (L : FiniteGaloisIntermediateField K (maximalUnramifiedOutside K Ω S)) :
    ∃ L' : FiniteGaloisIntermediateField K (maximalUnramifiedOutside K Ω S), L ≤ L' ∧
      ∀ (ι : PlaceEmbeddings K Ω) (f : sDivisorModule S ι),
        (∀ u ∈ L.toIntermediateField.fixingSubgroup, (sDivisorModule S ι).ρ u f = f) →
        ∃ y : (maximalUnramifiedOutside K Ω S)ˣ,
          (y : maximalUnramifiedOutside K Ω S) ∈ L'.toIntermediateField ∧
            (unitsToSDivisor S ι).hom (Additive.ofMul y) = f := by
  classical
  obtain ⟨L', hLL', hbase⟩ := exists_level_forall_sOrder_eq_single S L
  refine ⟨L', hLL', fun ι f hfix => ?_⟩
  let f' : divisorFunctions (outsideLocalizationHom S ι) (ULift.{u} ℤ) := f
  let F : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} → GaloisGroupUnramifiedOutside K Ω S → ℤ :=
    fun v g => (f'.1 v g).down
  have hf := f'.2
  have hU : ∀ v x, ∀ u ∈ L.toIntermediateField.fixingSubgroup, F v (x * u) = F v x := by
    intro v x u hu
    have h := congrArg (fun f : divisorFunctions (outsideLocalizationHom S ι) (ULift.{u} ℤ) =>
      (f.1 v x).down) (hfix u hu)
    exact h
  have hF : IsPrincipalIn S ι L' F := by
    rw [eq_sum_single S F hf.1.toFinset (fun v hv => by
      have : f'.1 v = 0 := by simpa using hv
      funext g
      change (f'.1 v g).down = 0
      rw [this]
      rfl)]
    refine isPrincipalIn_sum _ _ fun v _ => ?_
    have : (L.toIntermediateField.fixingSubgroup).Normal := inferInstance
    obtain ⟨y, hy, hyv⟩ := hbase ι v
    refine isPrincipalIn_single_of_base v L.toIntermediateField.fixingSubgroup
      (IntermediateField.fixingSubgroup_isOpen L.toIntermediateField) ⟨y, hy, hyv⟩ (F v)
      (fun x u hu => hU v x u hu) ?_
    rintro _ ⟨σ, rfl⟩ x
    change (f'.1 v (localizationHom ι S v.1 σ * x)).down = _
    rw [(hf.2 v).2 σ x]
  obtain ⟨y, hyL', hy⟩ := hF
  refine ⟨y, hyL', Subtype.ext ?_⟩
  funext v g
  apply ULift.ext
  exact hy v g

variable (ι : PlaceEmbeddings K Ω)

omit [IsSepClosed Ω] in
/-- Every divisor of `K_S` prime to `S` is fixed by the fixing group of a finite Galois level. -/
theorem exists_level_forall_ρ_eq (f : sDivisorModule S ι) :
    ∃ L : FiniteGaloisIntermediateField K (maximalUnramifiedOutside K Ω S),
      ∀ u ∈ L.toIntermediateField.fixingSubgroup, (sDivisorModule S ι).ρ u f = f := by
  have ho := IsSmoothRep.isOpen_stabilizer (sDivisorModule S ι) f
  obtain ⟨E, hE, hEsub⟩ := (krullTopology_mem_nhds_one_iff K (maximalUnramifiedOutside K Ω S)
    _).1 (ho.mem_nhds (Subgroup.one_mem _))
  obtain ⟨L, hEL⟩ := exists_finiteGaloisIntermediateField_le E
  exact ⟨L, fun u hu => hEsub (IntermediateField.fixingSubgroup_le hEL hu)⟩

/-- **The divisor class group of `K_S` prime to `S` is trivial**: the divisor map
`K_Sˣ → Div_S(K_S)` is onto. -/
theorem unitsToSDivisor_surjective : Function.Surjective (unitsToSDivisor S ι).hom := by
  intro f
  obtain ⟨L, hL⟩ := exists_level_forall_ρ_eq S ι f
  obtain ⟨L', -, h⟩ := exists_level_forall_unitsToSDivisor_eq S L
  obtain ⟨y, -, hy⟩ := h ι f hL
  exact ⟨Additive.ofMul y, hy⟩

/-- Every divisor of `K_S` prime to `S` is capitulating, for every `ℓ : ℕ` and with no hypothesis
on `S`. -/
theorem isCapitulating_of_mem_divisorFunctions (ℓ : ℕ)
    (F : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} → GaloisGroupUnramifiedOutside K Ω S → ℤ)
    (hF : (fun v g => ULift.up (F v g)) ∈
      divisorFunctions (outsideLocalizationHom S ι) (ULift.{u} ℤ)) :
    IsCapitulating S ι ℓ F := by
  obtain ⟨y, hy⟩ := unitsToSDivisor_surjective S ι ⟨_, hF⟩
  refine ⟨1, Nat.coprime_one_left ℓ, Additive.toMul y, fun v g => ?_⟩
  have h := congrArg (fun f : divisorFunctions (outsideLocalizationHom S ι) (ULift.{u} ℤ) =>
    (f.1 v g).down) hy
  rw [Nat.cast_one, one_mul]
  exact h

end Main

section Sequence

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (S : Set (HeightOneSpectrum (𝓞 K))) (ι : PlaceEmbeddings K Ω)

/-- `0 → 𝒪_Sˣ → K_Sˣ → Div_S(K_S) → 0`: the inclusion of the `S`-units followed by the divisor
map. -/
def sUnitsDivisorSequence :
    ShortComplex (Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) :=
  ShortComplex.mk (sUnitsToUnits S (maximalUnramifiedOutside K Ω S)) (unitsToSDivisor S ι) (by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    exact (unitsToSDivisor_eq_zero_iff S ι _).2 (Additive.toMul x).2)

instance isSmoothRep_sUnitsDivisorSequence_X₁ : IsSmoothRep (sUnitsDivisorSequence S ι).X₁ :=
  inferInstanceAs (IsSmoothRep (maximalSUnitsModule K Ω S))

instance isSmoothRep_sUnitsDivisorSequence_X₂ : IsSmoothRep (sUnitsDivisorSequence S ι).X₂ :=
  inferInstanceAs (IsSmoothRep (sUnitsQuotSequence K Ω S).X₂)

instance isSmoothRep_sUnitsDivisorSequence_X₃ : IsSmoothRep (sUnitsDivisorSequence S ι).X₃ :=
  inferInstanceAs (IsSmoothRep (sDivisorModule S ι))

variable [IsSepClosed Ω]

/-- `0 → 𝒪_Sˣ → K_Sˣ → Div_S(K_S) → 0` is exact. -/
theorem sUnitsDivisorSequence_shortExact : (sUnitsDivisorSequence S ι).ShortExact where
  exact := by
    apply shortComplex_exact_of_forall_exists
    intro x hx
    exact ⟨Additive.ofMul ⟨Additive.toMul x, (unitsToSDivisor_eq_zero_iff S ι _).1 hx⟩, rfl⟩
  mono_f := (Rep.mono_iff_injective _).2 (sUnitsToUnits_injective S _)
  epi_g := (Rep.epi_iff_surjective _).2 (unitsToSDivisor_surjective S ι)

/-- Every divisor of `K_S` prime to `S` is principal. -/
theorem sPrincipalDivisors_eq_top : sPrincipalDivisors S ι = ⊤ :=
  eq_top_iff.2 fun f _ => unitsToSDivisor_surjective S ι f

/-- The divisor class module of `K_S` prime to `S` is zero. -/
theorem isZero_sDivisorClassModule : Limits.IsZero (sDivisorClassModule S ι) := by
  rw [Rep.isZero_iff]
  refine ⟨fun p q => ?_⟩
  induction p using Submodule.Quotient.induction_on with
  | H f =>
  induction q using Submodule.Quotient.induction_on with
  | H g =>
  rw [Submodule.Quotient.eq, sPrincipalDivisors_eq_top]
  exact Submodule.mem_top

/-- `K_Sˣ/𝒪_Sˣ → Div_S(K_S)` is an isomorphism of `G_S`-modules. -/
theorem isIso_unitsModSUnitsToSDivisor : IsIso (unitsModSUnitsToSDivisor S ι) := by
  have : Mono (unitsModSUnitsToSDivisor S ι) := (sDivisorSequence_shortExact S ι).mono_f
  have : Epi (unitsModSUnitsToSDivisor S ι) := (Rep.epi_iff_surjective _).2 fun f => by
    obtain ⟨a, ha⟩ := unitsToSDivisor_surjective S ι f
    exact ⟨Submodule.Quotient.mk a, ha⟩
  exact isIso_of_mono_of_epi _

end Sequence

section Check

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (S : Set (HeightOneSpectrum (𝓞 K))) (ι : PlaceEmbeddings K Ω)

variable {S} in
/-- For an `S`-invariant unit `x` of `K_S` and `v ∉ S`, the order `ordAbove v x` of the module
`Langlands.GaloisCohomology.Global.Units.Divisor` is `-sOrder v x`. -/
theorem ordAbove_eq_neg_sOrder {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S)
    {x : (maximalUnramifiedOutside K Ω S)ˣ} (hx : IsSInvariant S x) :
    ordAbove S v x = -sOrder S ι v x := by
  obtain ⟨L, hxL⟩ := exists_level_mem S (x : maximalUnramifiedOutside K Ω S)
  have := NumberField.of_module_finite K L.toIntermediateField
  set W := (placeOfAlgHom (levelEmbedding S ι v L.toIntermediateField)).1 with hW
  have hWv : W.asIdeal.LiesOver v.asIdeal :=
    (placeOfAlgHom (levelEmbedding S ι v L.toIntermediateField)).2
  set z : L.toIntermediateFieldˣ := levelUnit x hxL with hz
  have h1 : W.valuation L.toIntermediateField (z : L.toIntermediateField) =
      WithZero.exp (sOrder S ι v x) := by
    rw [sOrder_eq ι hv x hxL]
    exact valuation_eq_exp_placeExponent v _ _
  let E : IntermediateField K Ω := L.toIntermediateField.map (maximalUnramifiedOutside K Ω S).val
  let φ : L.toIntermediateField ≃ₐ[K] E :=
    IntermediateField.equivMap L.toIntermediateField (maximalUnramifiedOutside K Ω S).val
  have : FiniteDimensional K E := LinearEquiv.finiteDimensional φ.toLinearEquiv
  have := NumberField.of_module_finite K E
  have hE : E ≤ maximalUnramifiedOutside K Ω S := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hxE : ((x : maximalUnramifiedOutside K Ω S) : Ω) ∈ E := ⟨x, hxL, rfl⟩
  let w : HeightOneSpectrum (𝓞 E) :=
    Langlands.Global.AdelicFunctoriality.finitePlaceEquiv φ.symm.toRingEquiv W
  have hw : w.valuation E ⟨_, hxE⟩ = W.valuation L.toIntermediateField (φ.symm ⟨_, hxE⟩) :=
    Langlands.Global.AdelicFunctoriality.finitePlaceEquiv_valuation _ _ _
  have hφx : φ.symm ⟨_, hxE⟩ = (z : L.toIntermediateField) := by
    apply φ.injective
    rw [AlgEquiv.apply_symm_apply]
    exact Subtype.ext rfl
  have hwv : w.asIdeal.LiesOver v.asIdeal := by
    constructor
    ext a
    have e : RingOfIntegers.mapRingEquiv φ.symm.toRingEquiv (algebraMap (𝓞 K) (𝓞 E) a) =
        algebraMap (𝓞 K) (𝓞 L.toIntermediateField) a := by
      apply RingOfIntegers.ext
      change φ.symm (algebraMap K E a) = algebraMap K L.toIntermediateField a
      exact φ.symm.commutes a
    show a ∈ v.asIdeal ↔ algebraMap (𝓞 K) (𝓞 E) a ∈ w.asIdeal
    rw [Langlands.Global.AdelicFunctoriality.finitePlaceEquiv_mem, e]
    exact Ideal.ext_iff.1 hWv.over a
  have hwv' : w.under (𝓞 K) = v := (liesOver_iff_eq_under.1 hwv).symm
  have h2 := valuation_eq_exp_ordAbove S hx hE hxE w (hwv' ▸ hv)
  rw [hwv', hw, hφx, h1] at h2
  have := congrArg WithZero.log h2
  simp only [WithZero.log_exp] at this
  omega

/-- The divisor map of `K_S` being onto, every divisor of `K` prime to `S` is the divisor
`divAbove` of an `S`-invariant unit of `K_S`. -/
theorem divAbove_surjective_of_surjective (h : Function.Surjective (unitsToSDivisor S ι).hom) :
    Function.Surjective (divAbove (Ω := Ω) S) := by
  classical
  have hsingle : ∀ v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
      ∃ x : sInvariantSubgroup Ω S, divAbove S (Additive.ofMul x) = Finsupp.single v 1 := by
    intro v
    let F : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} → GaloisGroupUnramifiedOutside K Ω S →
        ULift.{u} ℤ := fun v' _ => ULift.up (if v' = v then -1 else 0)
    have hF : F ∈ divisorFunctions (outsideLocalizationHom S ι) (ULift.{u} ℤ) := by
      refine ⟨(Set.finite_singleton v).subset fun v' hv' => ?_, fun v' =>
        ⟨IsLocallyConstant.const _, fun _ _ => rfl⟩⟩
      by_contra hne
      have hne' : v' ≠ v := hne
      apply hv'
      funext g
      change ULift.up (if v' = v then -1 else 0) = 0
      rw [ite_eq_right_of_eq_false _ _ (eq_false hne')]
      rfl
    obtain ⟨y, hy⟩ := h ⟨F, hF⟩
    set x : (maximalUnramifiedOutside K Ω S)ˣ :=
      Additive.toMul (α := (maximalUnramifiedOutside K Ω S)ˣ) y
    have hxv : ∀ v' g, sOrder S ι v'.1 (galUnitsHom K _ g x) = if v' = v then -1 else 0 :=
      fun v' g => congrArg (fun f : divisorFunctions (outsideLocalizationHom S ι) (ULift.{u} ℤ) =>
        (f.1 v' g).down) hy
    have hxS : IsSInvariant S x := by
      intro σ
      rw [← unitsToSDivisor_eq_zero_iff S ι]
      apply Subtype.ext
      funext v' g
      apply ULift.ext
      change sOrder S ι v'.1 (galUnitsHom K _ g (galUnitsHom K _ σ x * x⁻¹)) = 0
      have e : galUnitsHom K _ g (galUnitsHom K _ σ x) = galUnitsHom K _ (g * σ) x := by
        rw [map_mul, Monoid.End.coe_mul, Function.comp_apply]
      rw [map_mul, map_inv, sOrder_mul ι v'.2, sOrder_inv ι v'.2, e, hxv, hxv, add_neg_cancel]
    refine ⟨⟨x, hxS⟩, ?_⟩
    ext v'
    rw [divAbove_apply, toMul_ofMul, ordAbove_eq_neg_sOrder ι v'.2 hxS]
    have := hxv v' 1
    rw [map_one, Monoid.End.coe_one, id] at this
    rw [this, Finsupp.single_apply]
    by_cases hv : v' = v
    · subst hv
      simp
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hv),
        ite_eq_right_of_eq_false _ _ (eq_false (Ne.symm hv))]
      rfl
  intro D
  induction D using Finsupp.induction_linear with
  | zero => exact ⟨0, map_zero _⟩
  | add f g hf hg =>
    obtain ⟨x, rfl⟩ := hf
    obtain ⟨y, rfl⟩ := hg
    exact ⟨x + y, map_add _ _ _⟩
  | single v m =>
    obtain ⟨x, hx⟩ := hsingle v
    exact ⟨m • Additive.ofMul x, by rw [map_zsmul, hx, Finsupp.smul_single_one]⟩

/-- The divisor map of `K_S` being onto, `H¹(G_S, 𝒪_Sˣ) → Pic(𝒪_S)` is onto. -/
theorem cohomologyOneSUnitsToSPicard_surjective_of_surjective
    (h : Function.Surjective (unitsToSDivisor S ι).hom) :
    Function.Surjective (cohomologyOneSUnitsToSPicard (Ω := Ω) S) := by
  intro c
  obtain ⟨D, rfl⟩ := QuotientAddGroup.mk'_surjective _ c
  obtain ⟨x, hx⟩ := divAbove_surjective_of_surjective S ι h D
  exact ⟨invariantsToCohomologyOne (Ω := Ω) S (sInvariantToInvariants (Ω := Ω) S x),
    by rw [cohomologyOneSUnitsToSPicard_apply, hx]⟩

end Check

end

end Langlands.GaloisCohomology
