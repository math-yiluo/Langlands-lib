import Langlands.GaloisCohomology.Global.Units.Picard
import Langlands.ClassFieldTheory.Global.Artin.PrincipalIdeal

/-!
# `H¹(G_S, 𝒪_Sˣ) = Pic(𝒪_S)` for every `S`, by the principal ideal theorem

For a number field `F`, a set `S` of finite places of `F` and a separably closed Galois extension
`Ω / F`, the injection `cohomologyOneSUnitsToSPicard : H¹(G_S, 𝒪_Sˣ) → Pic(𝒪_S)` of the module
`Langlands.GaloisCohomology.Global.Units.Picard` is surjective with no condition on `S`
(`cohomologyOneSUnitsToSPicard_surjective`), hence an isomorphism
(`cohomologyOneSUnitsPicardEquiv`).

The class of an `S`-invariant unit of `K_S` goes to the class of its divisor `divAbove`
(`cohomologyOneSUnitsToSPicard_apply`), so it suffices that every divisor prime to `S` is the
divisor of an `S`-invariant unit (`divAbove_surjective`). For a prime `v ∉ S` this is the
principal ideal theorem (`exists_unramified_extension_forall_isPrincipal` of the module
`Langlands.ClassFieldTheory.Global.Artin.PrincipalIdeal`): there is a finite extension `H` of `F`,
unramified at every finite place, with `v 𝒪_H = (α)`. Such an `H` embeds over `F` into `K_S`
(`nonempty_algHom_maximalUnramifiedOutside` of the module
`Langlands.Galois.RestrictedRamification.MaximalExtension`). If `v^h = (a)` with `h` the class
number of `F`, then `α^h = a u` with `u` a unit of `𝒪_H`; the image of `u` is an `S`-unit, so `α`
is `S`-invariant (`isSInvariant_of_isSInvariant_pow` of the module
`Langlands.GaloisCohomology.Global.Units.Divisor`) and `h` times its divisor is the divisor `h v`
of `a` (`nsmul_divAbove_eq_sDivisorOf` of the module `Langlands.GaloisCohomology.Global.Units.Picard`).
Hence the divisor of `α` is `v` (`exists_divAbove_eq_single`).

This file imports the NYLL library (the copy under `Nyll/`) through
`Langlands.ClassFieldTheory.Global.Artin.PrincipalIdeal`.
-/

namespace Langlands.GaloisCohomology

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open Langlands.Galois Langlands.ProfiniteCohomology

universe u

noncomputable section

section Capitulation

variable {F Ω : Type u} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]
variable (S : Set (HeightOneSpectrum (𝓞 F))) [IsSepClosed Ω]

/-- Every prime outside `S` is the divisor of an `S`-invariant unit of `K_S`: a generator of the
prime extended to a finite extension of `F` unramified at every finite place in which it becomes
principal. -/
theorem exists_divAbove_eq_single (v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}) :
    ∃ x : sInvariantSubgroup Ω S, divAbove S (Additive.ofMul x) = Finsupp.single v 1 := by
  obtain ⟨H, _, _, _, _, hun, hprin⟩ :=
    Langlands.ClassFieldTheory.Global.Artin.exists_unramified_extension_forall_isPrincipal F
  obtain ⟨φ⟩ := nonempty_algHom_maximalUnramifiedOutside (Ω := Ω) S H fun v _ => hun v
  let ψ : 𝓞 H →+* maximalUnramifiedOutside F Ω S := φ.toRingHom.comp (algebraMap (𝓞 H) H)
  have hψ : Function.Injective ψ :=
    φ.toRingHom.injective.comp (FaithfulSMul.algebraMap_injective (𝓞 H) H)
  -- `α^h u = a` in `𝓞 H`, where `v 𝒪_H = (α)` and `v^h = (a)`
  obtain ⟨α, hα⟩ := (hprin v.1.asIdeal).principal
  have hpow := exists_pow_classNumber_eq_span v.1
  set a := hpow.choose
  have hspan : Ideal.span {α ^ classNumber F} = Ideal.span {algebraMap (𝓞 F) (𝓞 H) a} := by
    rw [← Ideal.span_singleton_pow, show Ideal.span {α} = _ from hα.symm, ← Ideal.map_pow,
      hpow.choose_spec.2, Ideal.map_span, Set.image_singleton]
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.1 hspan
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_pow (classNumber_ne_zero F), zero_mul, eq_comm,
      map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 H))] at hu
    exact hpow.choose_spec.1 hu
  -- their images in `K_S`
  let x : (maximalUnramifiedOutside F Ω S)ˣ := Units.mk0 (ψ α) ((map_ne_zero_iff ψ hψ).2 hα0)
  let y : (maximalUnramifiedOutside F Ω S)ˣ := Units.map (ψ : 𝓞 H →* _) u
  have hint : ∀ z : 𝓞 H, IsIntegral (S.integer F) (ψ z) := fun z =>
    ((RingOfIntegers.isIntegral z).map ψ.toIntAlgHom).tower_top
  have hy : y⁻¹ ∈ maximalSUnits F Ω S := by
    refine inv_mem ⟨hint _, ?_⟩
    rw [← map_inv]
    exact hint _
  have hxy : x ^ classNumber F =
      Units.map (algebraMap F (maximalUnramifiedOutside F Ω S) : F →* _) (placeUnit v.1) * y⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq]
    apply Units.ext
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0, Units.coe_map,
      MonoidHom.coe_ofClass, x, y]
    rw [← map_pow, ← map_mul, hu]
    change φ (algebraMap (𝓞 H) H (algebraMap (𝓞 F) (𝓞 H) a)) = algebraMap F _ (algebraMap (𝓞 F) F a)
    rw [← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 H) H, IsScalarTower.algebraMap_apply (𝓞 F) F H,
      φ.commutes]
  have hxS : IsSInvariant S x := by
    refine isSInvariant_of_isSInvariant_pow S (classNumber_ne_zero F) ?_
    rw [hxy]
    exact mul_mem (map_algebraMap_mem_sInvariantSubgroup (Ω := Ω) S _)
      (isSInvariant_of_mem_maximalSUnits S hy)
  refine ⟨⟨x, hxS⟩, ?_⟩
  have key := nsmul_divAbove_eq_sDivisorOf S ⟨x, hxS⟩ (placeUnit v.1) hy hxy
  rw [sDivisorOf_placeUnit, ← natCast_zsmul] at key
  exact smul_right_injective _ (by exact_mod_cast classNumber_ne_zero F) key

/-- `divAbove` is surjective: every divisor prime to `S` is the divisor of an `S`-invariant unit
of `K_S`. -/
theorem divAbove_surjective : Function.Surjective (divAbove (Ω := Ω) S) := by
  intro D
  induction D using Finsupp.induction_linear with
  | zero => exact ⟨0, map_zero _⟩
  | add f g hf hg =>
    obtain ⟨x, rfl⟩ := hf
    obtain ⟨y, rfl⟩ := hg
    exact ⟨x + y, map_add _ _ _⟩
  | single v m =>
    obtain ⟨x, hx⟩ := exists_divAbove_eq_single (Ω := Ω) S v
    exact ⟨m • Additive.ofMul x, by rw [map_zsmul, hx, Finsupp.smul_single_one]⟩

/-- `H¹(G_S, 𝒪_Sˣ) → Pic(𝒪_S)` is surjective, for every `S`. -/
theorem cohomologyOneSUnitsToSPicard_surjective :
    Function.Surjective (cohomologyOneSUnitsToSPicard (Ω := Ω) S) := by
  intro c
  obtain ⟨D, rfl⟩ := QuotientAddGroup.mk'_surjective _ c
  obtain ⟨x, hx⟩ := divAbove_surjective (Ω := Ω) S D
  exact ⟨invariantsToCohomologyOne (Ω := Ω) S (sInvariantToInvariants (Ω := Ω) S x),
    by rw [cohomologyOneSUnitsToSPicard_apply, hx]⟩

/-- **`H¹(G_S, 𝒪_Sˣ) = Pic(𝒪_S)`** for every set `S` of finite places: the injection
`cohomologyOneSUnitsToSPicard` is an isomorphism. -/
noncomputable def cohomologyOneSUnitsPicardEquiv :
    cohomology (maximalSUnitsModule F Ω S) 1 ≃+ SPicardGroup S :=
  AddEquiv.ofBijective (cohomologyOneSUnitsToSPicard (Ω := Ω) S)
    ⟨cohomologyOneSUnitsToSPicard_injective S, cohomologyOneSUnitsToSPicard_surjective S⟩

/-- `cohomologyOneSUnitsPicardEquiv` is `cohomologyOneSUnitsToSPicard`. -/
theorem cohomologyOneSUnitsPicardEquiv_apply (x : cohomology (maximalSUnitsModule F Ω S) 1) :
    cohomologyOneSUnitsPicardEquiv (Ω := Ω) S x = cohomologyOneSUnitsToSPicard (Ω := Ω) S x :=
  rfl

/-- Where `cohomologyOneSUnitsEquiv` is defined (the order of `Pic(𝒪_S)` invertible outside `S`),
it is `cohomologyOneSUnitsPicardEquiv`. -/
theorem cohomologyOneSUnitsEquiv_eq_cohomologyOneSUnitsPicardEquiv
    (hS : ∀ v ∉ S, ((Nat.card (SPicardGroup S) : ℕ) : 𝓞 F) ∉ v.asIdeal) :
    cohomologyOneSUnitsEquiv (Ω := Ω) S hS = cohomologyOneSUnitsPicardEquiv (Ω := Ω) S :=
  AddEquiv.ext fun _ => rfl

end Capitulation

end

end Langlands.GaloisCohomology
