import Langlands.Cohomology.Profinite.Cyclic.Profinite
import Langlands.GaloisCohomology.Field.FiniteLevel
import Mathlib.RingTheory.Flat.TorsionFree

namespace Langlands.GaloisCohomology

open Langlands.ProfiniteCohomology
open CategoryTheory MonoidalCategory groupCohomology GroupCoh IntermediateField

universe u

section Galois

variable (K L : Type u) [Field K] [Field L] [Algebra K L]

def unitsInvariant (a : Kˣ) : (unitsModuleZ K L).ρ.invariants :=
  ⟨Additive.ofMul (Units.map (algebraMap K L : K →* L) a), fun σ => by
    apply Additive.toMul.injective
    apply Units.ext
    change ((galUnitsHom K L σ (Units.map (algebraMap K L : K →* L) a) : Lˣ) : L) =
      (Units.map (algebraMap K L : K →* L) a : L)
    rw [coe_galUnitsHom_apply]
    simp⟩

@[simp]
theorem coe_unitsInvariant (a : Kˣ) :
    ((Additive.toMul (unitsInvariant K L a : Additive Lˣ) : Lˣ) : L) = algebraMap K L a :=
  rfl

end Galois

section GaloisInt

variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]

noncomputable def galCupClass (χ : Additive Gal(L/K) →ₜ+ QZ) (a : Kˣ) :
    cohomology (unitsModuleZ K L) 2 :=
  (cupCharClassProf (unitsModuleZ K L) χ).hom (unitsInvariant K L a)

end GaloisInt

section Galois

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [IsGalois K L]

theorem unitsModule_inflation_two_injective (U : OpenNormalSubgroup Gal(L/K)) :
    Function.Injective (inflation (unitsModule K L) U 2).hom := by
  rw [inflation_unitsModule_eq, ModuleCat.hom_comp, LinearMap.coe_comp]
  exact (unitsInflation_fixedField_two_injective U).comp
    ((ModuleCat.mono_iff_injective _).1 inferInstance)

end Galois

section GaloisInt

variable {K L : Type} [Field K] [Field L] [Algebra K L] [IsGalois K L]

theorem unitsModuleZ_inflation_two_injective (U : OpenNormalSubgroup Gal(L/K)) :
    Function.Injective (inflation (unitsModuleZ K L) U 2).hom := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using H2_induction_on with
  | h z =>
  obtain ⟨f, hf, hfz⟩ := (inflation_H2π_eq_zero_iff _ U z).1 hx
  let z' : cocycles₂ ((unitsModule K L).quotientToInvariants (U : Subgroup Gal(L/K))) :=
    ⟨fun p => ⟨(z p : Additive Lˣ), (z p).2⟩, (mem_cocycles₂_iff _).2 fun g h j => by
      induction g using QuotientGroup.induction_on with
      | H g =>
        apply Subtype.ext
        have e := congrArg Subtype.val ((mem_cocycles₂_iff z).1 z.2 (g : Gal(L/K) ⧸ (U : Subgroup Gal(L/K))) h j)
        exact e⟩
  have h' : (inflation (unitsModule K L) U 2).hom (H2π _ z') = 0 :=
    (inflation_H2π_eq_zero_iff _ U z').2 ⟨f, hf, fun g h => hfz g h⟩
  rw [← map_zero (inflation (unitsModule K L) U 2).hom] at h'
  have h0 := unitsModule_inflation_two_injective U h'
  obtain ⟨F, hF⟩ := (H2π_eq_zero_iff z').1 h0
  rw [H2π_eq_zero_iff]
  refine ⟨fun q => ⟨((F q).1 : Additive Lˣ), (F q).2⟩, ?_⟩
  funext p
  obtain ⟨q, q'⟩ := p
  induction q using QuotientGroup.induction_on with
  | H g =>
    have e := congrArg Subtype.val (congrFun hF ((g : Gal(L/K) ⧸ (U : Subgroup Gal(L/K))), q'))
    exact Subtype.ext e

end GaloisInt

section Galois

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [IsGalois K L]

theorem coe_norm_quotientToInvariants_unitsModuleZ (U : OpenNormalSubgroup Gal(L/K))
    [Fintype (Gal(L/K) ⧸ (U : Subgroup Gal(L/K)))]
    (m : Representation.invariants ((unitsModuleZ K L).ρ.comp (U : Subgroup Gal(L/K)).subtype)) :
    ((Additive.toMul
        ((((unitsModuleZ K L).quotientToInvariants (U : Subgroup Gal(L/K))).ρ.norm m :
          Representation.invariants ((unitsModuleZ K L).ρ.comp (U : Subgroup Gal(L/K)).subtype)) :
            Additive Lˣ) : Lˣ) : L) =
      algebraMap K L (Algebra.norm K (⟨((Additive.toMul m.1 : Lˣ) : L),
        mem_fixedField_of_mem_invariants_unitsModule (U : Subgroup Gal(L/K)) (v := m.1) m.2⟩ :
          fixedField (U : Subgroup Gal(L/K)))) := by
  have : FiniteDimensional K (fixedField (U : Subgroup Gal(L/K))) :=
    inferInstanceAs (FiniteDimensional K (fixedFiniteGalois U).toIntermediateField)
  have : IsGalois K (fixedField (U : Subgroup Gal(L/K))) :=
    inferInstanceAs (IsGalois K (fixedFiniteGalois U).toIntermediateField)
  set y : fixedField (U : Subgroup Gal(L/K)) := ⟨((Additive.toMul m.1 : Lˣ) : L),
    mem_fixedField_of_mem_invariants_unitsModule (U : Subgroup Gal(L/K)) (v := m.1) m.2⟩ with hy
  have hq : ∀ q : Gal(L/K) ⧸ (U : Subgroup Gal(L/K)),
      ((Additive.toMul ((((unitsModuleZ K L).quotientToInvariants (U : Subgroup Gal(L/K))).ρ q m :
        Representation.invariants ((unitsModuleZ K L).ρ.comp (U : Subgroup Gal(L/K)).subtype)) :
          Additive Lˣ) : Lˣ) : L) = ((quotientEquivGal U q y : fixedField (U : Subgroup Gal(L/K))) : L) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H σ =>
      rw [quotientEquivGal_mk_apply]
      exact coe_galUnitsHom_apply K L σ _
  rw [Representation.norm, LinearMap.sum_apply, AddSubmonoidClass.coe_finsetSum, toMul_sum,
    Units.coe_prod]
  simp_rw [hq]
  rw [Fintype.prod_equiv (quotientEquivGal U).toEquiv
      (fun q => ((quotientEquivGal U q y : fixedField (U : Subgroup Gal(L/K))) : L))
      (fun τ => ((τ y : fixedField (U : Subgroup Gal(L/K))) : L)) (fun _ => rfl),
    ← IntermediateField.coe_prod, ← Algebra.norm_eq_prod_automorphisms]
  rfl

end Galois

section Cocycles

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [IsGalois K L]

/-- **Norm criterion on cocycles.** For a continuous character `χ : Gal(L/K) → ℚ/ℤ` and `a ∈ Kˣ`,
the `2`-cocycle `(g, h) ↦ c_χ(g, h) • a` with values in `Lˣ` (`c_χ` is `GroupCoh.charCocycle`) is
the coboundary `(g, h) ↦ g • f(h) - f(gh) + f(g)` of a locally constant `f : Gal(L/K) → Lˣ` exactly
when `a` is a norm from the fixed field of the kernel of `χ`. The statement involves no coefficient
ring and holds in every universe. The proof passes to the finite cyclic quotient of `Gal(L/K)` by the
kernel of `χ` in the cohomology of `unitsModule`: inflation is injective in degree `2`
(`unitsModule_inflation_two_injective`), and on the cyclic quotient the cocycle is a coboundary
exactly when `a` is a norm (`GroupCoh.smul_norm_mem_coboundaries₂`,
`GroupCoh.exists_norm_eq_of_mem_coboundaries₂`). -/
theorem exists_coboundary_charCocycle_smul_iff_exists_norm (χ : Additive Gal(L/K) →ₜ+ QZ)
    (a : Kˣ) :
    (∃ f : Gal(L/K) → unitsModuleZ K L, IsLocallyConstant f ∧ ∀ g h : Gal(L/K),
      charCocycle (charAdd χ) (g, h) • (unitsInvariant K L a : unitsModuleZ K L) =
        (unitsModuleZ K L).ρ g (f h) - f (g * h) + f g) ↔
      ∃ y : fixedField (charKer (charAdd χ)), Algebra.norm K y = (a : K) := by
  set U : OpenNormalSubgroup Gal(L/K) := charKerOpen χ
  have := Fintype.ofFinite (Gal(L/K) ⧸ (U : Subgroup Gal(L/K)))
  set ψ : Additive (Gal(L/K) ⧸ (U : Subgroup Gal(L/K))) →+ AddCircle (1 : ℚ) :=
    charBar (charAdd χ)
  have hψinj : Function.Injective ψ := charBar_injective _
  have hψ : charAdd χ = charComp (U : Subgroup Gal(L/K)) ψ := (charComp_charBar (charAdd χ)).symm
  have := isCyclic_of_injective_char ψ hψinj
  have : FiniteDimensional K (fixedField (charKer (charAdd χ))) :=
    inferInstanceAs (FiniteDimensional K (fixedFiniteGalois U).toIntermediateField)
  set B := (unitsModule K L).quotientToInvariants (U : Subgroup Gal(L/K))
  have hx : ∀ σ : Gal(L/K), (unitsModule K L).ρ σ (unitsInvariant K L a : Additive Lˣ) =
      (unitsInvariant K L a : Additive Lˣ) := fun σ => (unitsInvariant K L a).2 σ
  let b : B := ⟨(unitsInvariant K L a : Additive Lˣ), fun s => hx s⟩
  have hb : ∀ q, B.ρ q b = b := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H g => exact Subtype.ext (hx g)
  let z : cocycles₂ B := ⟨fun p => charCocycle ψ p • b, (mem_cocycles₂_iff _).2 fun g h j => by
    change charCocycle ψ (g * h, j) • b + charCocycle ψ (g, h) • b =
      B.ρ g (charCocycle ψ (h, j) • b) + charCocycle ψ (g, h * j) • b
    rw [map_zsmul, hb, ← add_smul, ← add_smul, charCocycle_cocycle]⟩
  have key : (∃ f : Gal(L/K) → unitsModuleZ K L, IsLocallyConstant f ∧ ∀ g h : Gal(L/K),
      charCocycle (charAdd χ) (g, h) • (unitsInvariant K L a : unitsModuleZ K L) =
        (unitsModuleZ K L).ρ g (f h) - f (g * h) + f g) ↔
      (inflation (unitsModule K L) U 2).hom (H2π B z) = 0 := by
    have hz : ∀ g h : Gal(L/K), ((z ((g : Gal(L/K) ⧸ (U : Subgroup Gal(L/K))),
        (h : Gal(L/K) ⧸ (U : Subgroup Gal(L/K)))) : B) : unitsModule K L) =
          charCocycle (charAdd χ) (g, h) • (unitsInvariant K L a : unitsModuleZ K L) := by
      intro g h
      rw [hψ]
      rfl
    rw [inflation_H2π_eq_zero_iff]
    constructor
    · rintro ⟨f, hf, hfz⟩
      refine ⟨f, hf, fun g h => ?_⟩
      rw [hz]
      exact (hfz g h).symm
    · rintro ⟨f, hf, hfz⟩
      refine ⟨f, hf, fun g h => ?_⟩
      have e := hfz g h
      rw [hz] at e
      exact e.symm
  rw [key, ← map_zero (inflation (unitsModule K L) U 2).hom,
    (unitsModule_inflation_two_injective U).eq_iff, H2π_eq_zero_iff]
  have hnorm : ∀ m : B, ((Additive.toMul (((B.ρ.norm m : B) : unitsModule K L) : Additive Lˣ) :
      Lˣ) : L) = algebraMap K L (Algebra.norm K (⟨((Additive.toMul (m.1 : Additive Lˣ) : Lˣ) : L),
        mem_fixedField_of_mem_invariants_unitsModule (U : Subgroup Gal(L/K)) (v := m.1) m.2⟩ :
          fixedField (U : Subgroup Gal(L/K)))) :=
    fun m => by
      have : IsGalois K (fixedField (U : Subgroup Gal(L/K))) :=
        inferInstanceAs (IsGalois K (fixedFiniteGalois U).toIntermediateField)
      have : FiniteDimensional K (fixedField (U : Subgroup Gal(L/K))) :=
        inferInstanceAs (FiniteDimensional K (fixedFiniteGalois U).toIntermediateField)
      set y : fixedField (U : Subgroup Gal(L/K)) := ⟨((Additive.toMul (m.1 : Additive Lˣ) : Lˣ) : L),
        mem_fixedField_of_mem_invariants_unitsModule (U : Subgroup Gal(L/K)) (v := m.1) m.2⟩ with hy
      have hq : ∀ q : Gal(L/K) ⧸ (U : Subgroup Gal(L/K)),
          ((Additive.toMul (((B.ρ q m : B) : unitsModule K L) : Additive Lˣ) : Lˣ) : L) =
            ((quotientEquivGal U q y : fixedField (U : Subgroup Gal(L/K))) : L) := by
        intro q
        induction q using QuotientGroup.induction_on with
        | H σ =>
          rw [quotientEquivGal_mk_apply]
          exact coe_galUnitsHom_apply K L σ _
      rw [Representation.norm, LinearMap.sum_apply, AddSubmonoidClass.coe_finsetSum]
      change ((Additive.toMul (∑ q, (show Additive Lˣ from ((B.ρ q m : B) : unitsModule K L))) :
        Lˣ) : L) = _
      rw [toMul_sum, Units.coe_prod]
      simp_rw [hq]
      rw [Fintype.prod_equiv (quotientEquivGal U).toEquiv
          (fun q => ((quotientEquivGal U q y : fixedField (U : Subgroup Gal(L/K))) : L))
          (fun τ => ((τ y : fixedField (U : Subgroup Gal(L/K))) : L)) (fun _ => rfl),
        ← IntermediateField.coe_prod, ← Algebra.norm_eq_prod_automorphisms]
      rfl
  have hcob : ⇑z ∈ coboundaries₂ B ↔ ∃ m : B, B.ρ.norm m = b := by
    constructor
    · intro h
      rcases Nat.lt_or_ge (Fintype.card (Gal(L/K) ⧸ (U : Subgroup Gal(L/K)))) 2 with hm | hm
      · have : Subsingleton (Gal(L/K) ⧸ (U : Subgroup Gal(L/K))) :=
          Fintype.card_le_one_iff_subsingleton.1 (by omega)
        refine ⟨b, ?_⟩
        rw [Representation.norm, LinearMap.sum_apply, Fintype.sum_subsingleton _ 1, map_one,
          Module.End.one_apply]
      · obtain ⟨g, -, hg⟩ := exists_generator_sum_charCocycle ψ hψinj hm
        exact exists_norm_eq_of_mem_coboundaries₂ ψ g hg b h
    · rintro ⟨m, hm⟩
      have e : ⇑z = fun p => charCocycle ψ p • B.ρ.norm m := by
        rw [hm]
        rfl
      rw [e]
      exact smul_norm_mem_coboundaries₂ ψ m
  rw [hcob]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨⟨((Additive.toMul (m.1 : Additive Lˣ) : Lˣ) : L),
      mem_fixedField_of_mem_invariants_unitsModule (U : Subgroup Gal(L/K)) (v := m.1) m.2⟩, ?_⟩
    apply (algebraMap K L).injective
    have h := hnorm m
    rw [hm] at h
    exact h.symm.trans rfl
  · rintro ⟨y, hy⟩
    have hy0 : (y : L) ≠ 0 := by
      intro h0
      have : y = 0 := Subtype.ext h0
      rw [this, Algebra.norm_zero] at hy
      exact a.ne_zero hy.symm
    refine ⟨⟨Additive.ofMul (Units.mk0 (y : L) hy0), fun σ => ?_⟩, ?_⟩
    · apply Additive.toMul.injective
      apply Units.ext
      exact (coe_galUnitsHom_apply K L σ.1 _).trans (y.2 σ)
    · apply Subtype.ext
      apply Additive.toMul.injective
      apply Units.ext
      exact (hnorm _).trans (congrArg (algebraMap K L) hy)

end Cocycles

section GaloisInt

variable {K L : Type} [Field K] [Field L] [Algebra K L] [IsGalois K L]

theorem galCupClass_eq_zero_iff (χ : Additive Gal(L/K) →ₜ+ QZ) (a : Kˣ) :
    galCupClass K L χ a = 0 ↔ ∃ y : fixedField (charKer (charAdd χ)), Algebra.norm K y = (a : K) := by
  obtain ⟨w, hw, hwc⟩ := exists_cocycle_cupCharClassProf (unitsModuleZ K L) χ (unitsInvariant K L a)
  rw [galCupClass, ← hw, cohomologyπ_two_eq_zero_iff,
    ← exists_coboundary_charCocycle_smul_iff_exists_norm χ a]
  simp only [hwc, Matrix.cons_val_zero, Matrix.cons_val_one]

theorem galCupClass_eq_zero_iff_of_isSepClosure {Ksep : Type} [Field Ksep] [Algebra K Ksep]
    [IsSepClosure K Ksep] (χ : Additive Gal(Ksep/K) →ₜ+ QZ) (a : Kˣ) :
    galCupClass K Ksep χ a = 0 ↔
      ∃ y : fixedField (charKer (charAdd χ)), Algebra.norm K y = (a : K) :=
  galCupClass_eq_zero_iff χ a

end GaloisInt

section Quadratic

variable (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] [FiniteDimensional F Ω] [IsGalois F Ω]

theorem coe_toMul_norm_unitsModuleZ (m : Additive Ωˣ) :
    (((Additive.toMul ((unitsModuleZ F Ω).ρ.norm m) : Ωˣ) : Ω)) =
      algebraMap F Ω (Algebra.norm F ((Additive.toMul m : Ωˣ) : Ω)) := by
  rw [Algebra.norm_eq_prod_automorphisms, Representation.norm, LinearMap.sum_apply, toMul_sum,
    Units.coe_prod]
  exact Finset.prod_congr rfl fun σ _ => coe_galUnitsHom_apply F Ω σ _

theorem unitsInvariant_mem_normRangeInvariants_iff (a : Fˣ) :
    unitsInvariant F Ω a ∈ Langlands.Tate.normImage (unitsModuleZ F Ω) ↔
      (a : F) ∈ Set.range (Algebra.norm F : Ω → F) := by
  rw [mem_normRangeInvariants_iff]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨((Additive.toMul m : Ωˣ) : Ω), (algebraMap F Ω).injective ?_⟩
    rw [← coe_toMul_norm_unitsModuleZ, hm]
    rfl
  · rintro ⟨z, hz⟩
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [Algebra.norm_zero] at hz
      exact a.ne_zero hz.symm
    refine ⟨Additive.ofMul (Units.mk0 z hz0), ?_⟩
    apply Additive.toMul.injective
    apply Units.ext
    refine (coe_toMul_norm_unitsModuleZ F Ω _).trans ?_
    change algebraMap F Ω (Algebra.norm F z) = algebraMap F Ω a
    rw [hz]

theorem exists_unitsInvariant_eq (u : (unitsModuleZ F Ω).ρ.invariants) : ∃ a : Fˣ, unitsInvariant F Ω a = u := by
  have hfix : ∀ σ : Gal(Ω/F), σ ((Additive.toMul (u : Additive Ωˣ) : Ωˣ) : Ω) =
      ((Additive.toMul (u : Additive Ωˣ) : Ωˣ) : Ω) := fun σ => by
    have := congrArg (fun v : Additive Ωˣ => ((Additive.toMul v : Ωˣ) : Ω)) (u.2 σ)
    exact (coe_galUnitsHom_apply F Ω σ _).symm.trans this
  have hfix' : ∀ σ : Gal(Ω/F), σ (((Additive.toMul (u : Additive Ωˣ) : Ωˣ)⁻¹ : Ωˣ) : Ω) =
      (((Additive.toMul (u : Additive Ωˣ) : Ωˣ)⁻¹ : Ωˣ) : Ω) := fun σ => by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hfix]
  obtain ⟨x, hx⟩ := (IsGalois.mem_range_algebraMap_iff_fixed _).2 hfix
  obtain ⟨y, hy⟩ := (IsGalois.mem_range_algebraMap_iff_fixed _).2 hfix'
  refine ⟨⟨x, y, (algebraMap F Ω).injective ?_, (algebraMap F Ω).injective ?_⟩, Subtype.ext ?_⟩
  · rw [map_mul, hx, hy, map_one, Units.mul_inv]
  · rw [map_mul, hx, hy, map_one, Units.inv_mul]
  · apply Additive.toMul.injective
    apply Units.ext
    exact hx

omit [FiniteDimensional F Ω] [IsGalois F Ω] in
theorem unitsInvariant_mul (a b : Fˣ) :
    unitsInvariant F Ω (a * b) = unitsInvariant F Ω a + unitsInvariant F Ω b := by
  exact Subtype.ext (congrArg Additive.ofMul (map_mul (Units.map (algebraMap F Ω : F →* Ω)) a b))

end Quadratic

section QuadraticInv

variable (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] [FiniteDimensional F Ω] [IsGalois F Ω]

theorem galCupClass_eq_zero_of_mem_range_norm (χ : Additive Gal(Ω/F) →ₜ+ QZ) {a : Fˣ}
    (ha : (a : F) ∈ Set.range (Algebra.norm F : Ω → F)) : galCupClass F Ω χ a = 0 := by
  have hinj : Function.Injective (toGroupCohomology (unitsModuleZ F Ω) 2).hom := by
    rw [← isoGroupCohomology_hom]
    exact (ModuleCat.mono_iff_injective _).1 inferInstance
  apply hinj
  rw [map_zero, galCupClass, toGroupCohomology_cupCharClassProf]
  exact cupCharClass_eq_zero_of_mem _ _ ((unitsInvariant_mem_normRangeInvariants_iff F Ω a).2 ha)

theorem galCupClass_eq_zero_iff_of_injective (χ : Additive Gal(Ω/F) →ₜ+ QZ)
    (hχ : Function.Injective χ) (a : Fˣ) :
    galCupClass F Ω χ a = 0 ↔ (a : F) ∈ Set.range (Algebra.norm F : Ω → F) := by
  have hχ' : Function.Injective (charAdd χ) := QZ.toAddCircle.injective.comp hχ
  have := isCyclic_of_injective_char (charAdd χ) hχ'
  have hinj : Function.Injective (toGroupCohomology (unitsModuleZ F Ω) 2).hom := by
    rw [← isoGroupCohomology_hom]
    exact (ModuleCat.mono_iff_injective _).1 inferInstance
  rw [← unitsInvariant_mem_normRangeInvariants_iff, ← cupCharClass_eq_zero_iff (charAdd χ) hχ',
    ← toGroupCohomology_cupCharClassProf, ← map_zero (toGroupCohomology _ 2).hom,
    hinj.eq_iff]
  rfl

open Classical in

noncomputable def quadraticInvFun (x : cohomology (unitsModuleZ F Ω) 2) : QZ :=
  if x = 0 then 0 else QZ.mk (1 / 2)

omit [FiniteDimensional F Ω] in
theorem quadraticInvFun_zero : quadraticInvFun F Ω 0 = 0 := by
  simp [quadraticInvFun]

omit [FiniteDimensional F Ω] in
theorem quadraticInvFun_of_ne_zero {x : cohomology (unitsModuleZ F Ω) 2} (hx : x ≠ 0) :
    quadraticInvFun F Ω x = QZ.mk (1 / 2) := by
  simp [quadraticInvFun, hx]

theorem quadraticInvFun_galCupClass (h2 : Module.finrank F Ω ≤ 2) (χ : Additive Gal(Ω/F) →ₜ+ QZ)
    (a : Fˣ) (g : Gal(Ω/F)) (hg : g = 1 ↔ (a : F) ∈ Set.range (Algebra.norm F : Ω → F)) :
    quadraticInvFun F Ω (galCupClass F Ω χ a) = χ (Additive.ofMul g) := by
  by_cases ha : (a : F) ∈ Set.range (Algebra.norm F : Ω → F)
  · rw [hg.2 ha, ofMul_one, map_zero, galCupClass_eq_zero_of_mem_range_norm F Ω χ ha,
      quadraticInvFun_zero]
  have hg1 : g ≠ 1 := fun h => ha (hg.1 h)
  have hcard : Fintype.card Gal(Ω/F) = 2 := by
    have h1 : Fintype.card Gal(Ω/F) = Module.finrank F Ω := by
      rw [← Nat.card_eq_fintype_card]
      exact IsGalois.card_aut_eq_finrank F Ω
    have h3 : 1 < Fintype.card Gal(Ω/F) := Fintype.one_lt_card_iff.2 ⟨g, 1, hg1⟩
    omega
  by_cases hχg : χ (Additive.ofMul g) = 0
  · have hχ0 : χ = 0 := by
      ext x
      by_cases hx : Additive.toMul x = 1
      · rw [show x = Additive.ofMul 1 from hx ▸ rfl, ofMul_one, map_zero]
        rfl
      · rw [show x = Additive.ofMul g from eq_of_ne_one_of_card_eq_two hcard hx hg1 ▸ rfl, hχg]
        rfl
    rw [hχg, hχ0]
    change quadraticInvFun F Ω ((cupCharClassProf (unitsModuleZ F Ω) 0).hom _) = 0
    rw [cupCharClassProf_zero, quadraticInvFun_zero]
  · have hχinj : Function.Injective χ := (injective_iff_map_eq_zero χ).2 fun x hx => by
      by_contra hne
      have hx1 : Additive.toMul x ≠ 1 := fun h => hne (by rw [show x = Additive.ofMul 1 from h ▸ rfl,
        ofMul_one])
      exact hχg (by rw [← eq_of_ne_one_of_card_eq_two hcard hx1 hg1]; exact hx)
    rw [quadraticInvFun_of_ne_zero F Ω (fun h => ha ((galCupClass_eq_zero_iff_of_injective F Ω χ
      hχinj a).1 h))]
    exact (char_eq_half_of_card_eq_two hcard χ.toAddMonoidHom hχg).symm

end QuadraticInv

section QuadraticHom

variable (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] [FiniteDimensional F Ω] [IsGalois F Ω]

omit [IsGalois F Ω] in
theorem card_gal_le_two (h2 : Module.finrank F Ω ≤ 2) : Fintype.card Gal(Ω/F) ≤ 2 := by
  exact (AlgEquiv.card_le (F := F) (K := Ω)).trans h2

open Classical in

noncomputable def quadraticChar (h2 : Module.finrank F Ω ≤ 2) : Additive Gal(Ω/F) →ₜ+ QZ where
  toFun x := if Additive.toMul x = 1 then 0 else QZ.mk (1 / 2)
  map_zero' := by simp
  map_add' x y := by
    by_cases hx : Additive.toMul x = 1
    · have : Additive.toMul (x + y) = Additive.toMul y := by rw [toMul_add, hx, one_mul]
      simp [hx, this]
    by_cases hy : Additive.toMul y = 1
    · have : Additive.toMul (x + y) = Additive.toMul x := by rw [toMul_add, hy, mul_one]
      simp [hy, this]
    have hcard : Fintype.card Gal(Ω/F) = 2 := by
      have := card_gal_le_two F Ω h2
      have h3 : 1 < Fintype.card Gal(Ω/F) := Fintype.one_lt_card_iff.2 ⟨_, 1, hx⟩
      omega
    have hxy : Additive.toMul (x + y) = 1 := by
      rw [toMul_add, ← eq_of_ne_one_of_card_eq_two hcard hx hy, ← sq, ← hcard, pow_card_eq_one]
    simp only [hxy, hx, hy, ite_true, ite_false]
    exact QZ.mk_half_add_mk_half.symm
  continuous_toFun := continuous_of_discreteTopology

omit [IsGalois F Ω] in
open Classical in
theorem quadraticChar_injective (h2 : Module.finrank F Ω ≤ 2) :
    Function.Injective (quadraticChar F Ω h2) := by
  refine (injective_iff_map_eq_zero (quadraticChar F Ω h2)).2 fun x hx => ?_
  by_contra hne
  have h1 : Additive.toMul x ≠ 1 := fun h => hne (by rw [show x = Additive.ofMul 1 from h ▸ rfl, ofMul_one])
  change (if Additive.toMul x = 1 then 0 else QZ.mk (1 / 2)) = 0 at hx
  rw [ite_eq_right h1] at hx
  exact QZ.mk_half_ne_zero hx

noncomputable def quadraticInv (h2 : Module.finrank F Ω ≤ 2)
    (hN : ∀ a b : Fˣ, (a : F) ∉ Set.range (Algebra.norm F : Ω → F) →
      (b : F) ∉ Set.range (Algebra.norm F : Ω → F) → ((a * b : Fˣ) : F) ∈ Set.range (Algebra.norm F : Ω → F)) :
    cohomology (unitsModuleZ F Ω) 2 →+ QZ where
  toFun := quadraticInvFun F Ω
  map_zero' := quadraticInvFun_zero F Ω
  map_add' x y := by
    by_cases hx : x = 0
    · rw [hx, zero_add, quadraticInvFun_zero, zero_add]
    by_cases hy : y = 0
    · rw [hy, add_zero, quadraticInvFun_zero, add_zero]
    have hχ := quadraticChar_injective F Ω h2
    have := isCyclic_of_injective_char (charAdd (quadraticChar F Ω h2))
      (QZ.toAddCircle.injective.comp hχ)
    obtain ⟨u, rfl⟩ := cupCharClassProf_surjective (unitsModuleZ F Ω) _ hχ x
    obtain ⟨v, rfl⟩ := cupCharClassProf_surjective (unitsModuleZ F Ω) _ hχ y
    obtain ⟨a, rfl⟩ := exists_unitsInvariant_eq F Ω u
    obtain ⟨b, rfl⟩ := exists_unitsInvariant_eq F Ω v
    have ha : (a : F) ∉ Set.range (Algebra.norm F : Ω → F) := fun h =>
      hx (galCupClass_eq_zero_of_mem_range_norm F Ω _ h)
    have hb : (b : F) ∉ Set.range (Algebra.norm F : Ω → F) := fun h =>
      hy (galCupClass_eq_zero_of_mem_range_norm F Ω _ h)
    have hab : (cupCharClassProf (unitsModuleZ F Ω) (quadraticChar F Ω h2)).hom (unitsInvariant F Ω a) +
        (cupCharClassProf (unitsModuleZ F Ω) (quadraticChar F Ω h2)).hom (unitsInvariant F Ω b) = 0 := by
      rw [← map_add, ← unitsInvariant_mul]
      exact galCupClass_eq_zero_of_mem_range_norm F Ω _ (hN a b ha hb)
    rw [hab, quadraticInvFun_zero, quadraticInvFun_of_ne_zero F Ω hx,
      quadraticInvFun_of_ne_zero F Ω hy, QZ.mk_half_add_mk_half]

theorem quadraticInv_apply (h2 : Module.finrank F Ω ≤ 2) (hN) (x : cohomology (unitsModuleZ F Ω) 2) :
    quadraticInv F Ω h2 hN x = quadraticInvFun F Ω x :=
  rfl

theorem quadraticInv_injective (h2 : Module.finrank F Ω ≤ 2) (hN) :
    Function.Injective (quadraticInv F Ω h2 hN) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  by_contra hne
  rw [quadraticInv_apply, quadraticInvFun_of_ne_zero F Ω hne] at hx
  exact QZ.mk_half_ne_zero hx

theorem quadraticInv_galCupClass (h2 : Module.finrank F Ω ≤ 2) (hN) (χ : Additive Gal(Ω/F) →ₜ+ QZ)
    (a : Fˣ) (g : Gal(Ω/F)) (hg : g = 1 ↔ (a : F) ∈ Set.range (Algebra.norm F : Ω → F)) :
    quadraticInv F Ω h2 hN (galCupClass F Ω χ a) = χ (Additive.ofMul g) :=
  quadraticInvFun_galCupClass F Ω h2 χ a g hg

end QuadraticHom

end Langlands.GaloisCohomology