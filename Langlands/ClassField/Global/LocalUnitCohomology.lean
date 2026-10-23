import Langlands.ClassField.Global.CohomologyMaps

/-! # Valuation units of finite completions and their cohomology

The exponent of the normalized valuation on `E_wˣ`, its invariance under `Gal(E_w/F_v)`, the
representation of `Gal(E_w/F_v)` on the valuation units `U_w`, the short exact sequence
`0 → U_w → E_wˣ → ℤ → 0`, and the injectivity of `H²(Gal(E_w/F_v), U_w) → H²(Gal(E_w/F_v), E_wˣ)`.
-/

noncomputable section

universe u

namespace Langlands.ClassField.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField Langlands.Global.AdelicFunctoriality.FiniteExtension
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic
open Langlands.ClassFieldTheory.Local
open CategoryTheory Limits

section Exponent

variable {E : Type u} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

/-- The exponent of the normalized valuation on the units of `E_w`. -/
def unitsExponent : (w.adicCompletion E)ˣ →* Multiplicative ℤ :=
  WithZero.unitsWithZeroEquiv.toMonoidHom.comp
    (Units.map (Valued.v : Valuation (w.adicCompletion E)
      (WithZero (Multiplicative ℤ))).toMonoidWithZeroHom.toMonoidHom)

theorem valued_units (x : (w.adicCompletion E)ˣ) :
    Valued.v (x : w.adicCompletion E) =
      WithZero.exp (Multiplicative.toAdd (unitsExponent w x)) := by
  change Valued.v (x : w.adicCompletion E) =
    ((WithZero.unitsWithZeroEquiv (Units.map (Valued.v : Valuation (w.adicCompletion E)
      (WithZero (Multiplicative ℤ))).toMonoidWithZeroHom.toMonoidHom x) : Multiplicative ℤ) :
        WithZero (Multiplicative ℤ))
  rw [WithZero.coe_unitsWithZeroEquiv_eq_units_val]
  rfl

theorem unitsExponent_eq_one_iff (x : (w.adicCompletion E)ˣ) :
    unitsExponent w x = 1 ↔ Valued.v (x : w.adicCompletion E) = 1 := by
  rw [valued_units, ← WithZero.exp_zero, WithZero.exp_injective.eq_iff]
  rfl

theorem toAdd_unitsExponent_neg_iff (x : (w.adicCompletion E)ˣ) :
    Multiplicative.toAdd (unitsExponent w x) < 0 ↔ Valued.v (x : w.adicCompletion E) < 1 := by
  rw [valued_units, WithZero.exp_lt_one_iff]

/-- `E_w` has a unit of valuation exponent `-1` (a uniformizer). -/
theorem exists_unitsExponent_eq_neg_one :
    ∃ π : (w.adicCompletion E)ˣ, Multiplicative.toAdd (unitsExponent w π) = -1 := by
  obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer E
  have h0 : (π : w.adicCompletion E) ≠ 0 := by
    intro h
    rw [← valuedAdicCompletion_eq_valuation', h, map_zero] at hπ
    exact WithZero.zero_ne_coe hπ
  refine ⟨Units.mk0 _ h0, WithZero.exp_injective ?_⟩
  rw [← valued_units, Units.val_mk0, valuedAdicCompletion_eq_valuation', hπ]

/-- The valuation exponent is surjective onto `ℤ`. -/
theorem unitsExponent_surjective : Function.Surjective (unitsExponent w) := by
  obtain ⟨π, hπ⟩ := exists_unitsExponent_eq_neg_one w
  intro n
  refine ⟨π ^ (-Multiplicative.toAdd n), ?_⟩
  rw [map_zpow]
  apply Multiplicative.toAdd.injective
  rw [toAdd_zpow, hπ]
  simp

/-- The valuation units `U_w = {x ∈ E_wˣ | v(x) = 1}` of `E_w`. -/
def localUnits : Subgroup (w.adicCompletion E)ˣ := (unitsExponent w).ker

theorem mem_localUnits_iff (x : (w.adicCompletion E)ˣ) :
    x ∈ localUnits w ↔ Valued.v (x : w.adicCompletion E) = 1 :=
  MonoidHom.mem_ker.trans (unitsExponent_eq_one_iff w x)

end Exponent

/-- A short complex of representations is short exact when it is so on underlying elements. -/
theorem repShortExact_of_values {k G : Type u} [CommRing k] [Group G]
    (S : ShortComplex (Rep.{u} k G)) (h₁ : Function.Injective S.f.hom)
    (h₂ : ∀ x, S.g.hom x = 0 → ∃ y, S.f.hom y = x) (h₃ : Function.Surjective S.g.hom) :
    S.ShortExact where
  exact := (forget₂ (Rep.{u} k G) (ModuleCat.{u} k)).reflects_exact_of_faithful _ <|
    (ShortComplex.moduleCat_exact_iff _).2 fun x hx => h₂ x hx
  mono_f := (Rep.mono_iff_injective _).2 h₁
  epi_g := (Rep.epi_iff_surjective _).2 h₃

section LocalAut

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal]

/-- Local automorphisms preserve the valuation units. -/
theorem valued_localAut_eq_one_iff
    (σ : w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E)
    (x : w.adicCompletion E) : Valued.v (σ x) = 1 ↔ Valued.v x = 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hσx : σ x ≠ 0 := by simpa using hx
  have key : ∀ y : w.adicCompletion E, y ≠ 0 →
      (Valued.v y = 1 ↔ ¬ Valued.v y < 1 ∧ ¬ Valued.v y⁻¹ < 1) := by
    intro y hy
    rw [← Valuation.one_lt_val_iff _ hy, not_lt, not_lt]
    constructor
    · intro h
      rw [h]
      exact ⟨le_rfl, le_rfl⟩
    · rintro ⟨h1, h2⟩
      exact le_antisymm h2 h1
  rw [key _ hσx, key _ hx, ← map_inv₀ σ, valued_localAut_lt_one_iff,
    valued_localAut_lt_one_iff]

/-- Local automorphisms preserve the valuation exponent. -/
theorem unitsExponent_localAut
    (σ : w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E)
    (x : (w.adicCompletion E)ˣ) :
    unitsExponent w (Units.map (σ : w.adicCompletion E →* w.adicCompletion E) x) =
      unitsExponent w x := by
  set g : (w.adicCompletion E)ˣ → ℤ := fun y => Multiplicative.toAdd (unitsExponent w y)
    with hg
  set f : (w.adicCompletion E)ˣ → ℤ := fun y =>
    Multiplicative.toAdd (unitsExponent w (Units.map (σ : w.adicCompletion E →* w.adicCompletion E) y))
    with hf
  have hfmul : ∀ a b, f (a * b) = f a + f b := fun a b => by
    simp only [hf, map_mul, toAdd_mul]
  have hfzpow : ∀ a (n : ℤ), f (a ^ n) = n * f a := fun a n => by
    simp only [hf, map_zpow, toAdd_zpow, smul_eq_mul]
  have hgmul : ∀ a b, g (a * b) = g a + g b := fun a b => by
    simp only [hg, map_mul, toAdd_mul]
  have hgzpow : ∀ a (n : ℤ), g (a ^ n) = n * g a := fun a n => by
    simp only [hg, map_zpow, toAdd_zpow, smul_eq_mul]
  have hzero : ∀ a, f a = 0 ↔ g a = 0 := fun a => by
    have h1 := unitsExponent_eq_one_iff w a
    have h2 := unitsExponent_eq_one_iff w
      (Units.map (σ : w.adicCompletion E →* w.adicCompletion E) a)
    have h3 := valued_localAut_eq_one_iff v w σ (a : w.adicCompletion E)
    simp only [hf, hg]
    rw [← toAdd_one, Multiplicative.toAdd.injective.eq_iff,
      Multiplicative.toAdd.injective.eq_iff, h1, h2]
    exact h3
  obtain ⟨π, hπ⟩ := exists_unitsExponent_eq_neg_one w
  have hπ' : g π = -1 := hπ
  have hlin : ∀ a, f a = -(g a) * f π := fun a => by
    have h : g (a * π ^ g a) = 0 := by
      rw [hgmul, hgzpow, hπ']
      ring
    rw [← hzero, hfmul, hfzpow] at h
    linarith
  have hπneg : f π < 0 := by
    simp only [hf]
    rw [toAdd_unitsExponent_neg_iff]
    change Valued.v (σ (π : w.adicCompletion E)) < 1
    rw [valued_localAut_lt_one_iff, ← toAdd_unitsExponent_neg_iff, hπ]
    norm_num
  have hy : f (Units.map (σ.symm : w.adicCompletion E →* w.adicCompletion E) π) = -1 := by
    have : Units.map (σ : w.adicCompletion E →* w.adicCompletion E)
        (Units.map (σ.symm : w.adicCompletion E →* w.adicCompletion E) π) = π := by
      ext
      simp
    simp only [hf]
    rw [this]
    exact hπ
  have hunit : f π = -1 := by
    rw [hlin] at hy
    have hmul : (g (Units.map (σ.symm : w.adicCompletion E →* w.adicCompletion E) π)) * f π = 1 := by
      linarith
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hmul with ⟨_, h⟩ | ⟨_, h⟩
    · omega
    · exact h
  apply Multiplicative.toAdd.injective
  change f x = g x
  rw [hlin, hunit]
  ring

theorem units_smul_eq_map
    (σ : w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E)
    (x : (w.adicCompletion E)ˣ) :
    σ • x = Units.map (σ : w.adicCompletion E →* w.adicCompletion E) x := rfl

/-- Local automorphisms preserve the valuation units. -/
theorem smul_mem_localUnits
    (σ : w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E)
    {x : (w.adicCompletion E)ˣ} (hx : x ∈ localUnits w) : σ • x ∈ localUnits w := by
  rw [localUnits, MonoidHom.mem_ker, units_smul_eq_map, unitsExponent_localAut]
  exact hx

/-- The action of `Gal(E_w/F_v)` on the valuation units `U_w`. -/
def localUnitsAut :
    (w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E) →* MulAut (localUnits w) where
  toFun σ :=
    { toFun := fun u => ⟨σ • (u : (w.adicCompletion E)ˣ), smul_mem_localUnits v w σ u.2⟩
      invFun := fun u => ⟨σ⁻¹ • (u : (w.adicCompletion E)ˣ), smul_mem_localUnits v w σ⁻¹ u.2⟩
      left_inv := fun _ => Subtype.ext (inv_smul_smul σ _)
      right_inv := fun _ => Subtype.ext (smul_inv_smul σ _)
      map_mul' := fun a b => Subtype.ext (smul_mul' σ (a : (w.adicCompletion E)ˣ) b) }
  map_one' := MulEquiv.ext fun u => Subtype.ext (one_smul _ (u : (w.adicCompletion E)ˣ))
  map_mul' σ τ := MulEquiv.ext fun u => Subtype.ext (mul_smul σ τ (u : (w.adicCompletion E)ˣ))

/-- The action on valuation units, installed explicitly. -/
@[instance_reducible]
def localUnitsAction :
    MulDistribMulAction (w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E)
      (localUnits w) where
  __ := MulAction.compHom (localUnits w) (localUnitsAut v w)
  smul_one σ := map_one (localUnitsAut v w σ)
  smul_mul σ a b := map_mul (localUnitsAut v w σ) a b

attribute [local instance] localUnitsAction

theorem coe_localUnits_smul
    (σ : w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E) (u : localUnits w) :
    ((σ • u : localUnits w) : (w.adicCompletion E)ˣ) = σ • (u : (w.adicCompletion E)ˣ) := rfl

/-- The valuation units `U_w` as a representation of `Gal(E_w/F_v)`. -/
abbrev localUnitsRepresentation :
    Rep.{u} NormalizedTwoCocycle.CoefficientScalars.{u}
      (w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E) :=
  NormalizedTwoCocycle.coefficientRepresentation _ (localUnits w)

/-- The inclusion `U_w → E_wˣ`, a morphism of representations of `Gal(E_w/F_v)`. -/
def localUnitsInclusion :
    localUnitsRepresentation v w ⟶
      unitsRepresentation (padicField v).Carrier (w.adicCompletion E) :=
  Rep.ofHom
    { toLinearMap :=
        { toFun := fun x => Additive.ofMul
            ((@Additive.toMul (localUnits w) x : localUnits w) : (w.adicCompletion E)ˣ)
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      isIntertwining' := fun _ => rfl }

/-- The valuation exponent `E_wˣ → ℤ`, a morphism to the trivial representation. -/
def unitsExponentMorphism :
    unitsRepresentation (padicField v).Carrier (w.adicCompletion E) ⟶
      Rep.trivial IntegerScalars.{u}
        (w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E) IntegerScalars.{u} :=
  Rep.ofHom
    { toLinearMap :=
        { toFun := fun x => ULift.up
            (Multiplicative.toAdd (unitsExponent w (@Additive.toMul (w.adicCompletion E)ˣ x)))
          map_add' := fun x y => by
            apply ULift.ext
            change Multiplicative.toAdd (unitsExponent w
              (@Additive.toMul (w.adicCompletion E)ˣ x * @Additive.toMul (w.adicCompletion E)ˣ y)) = _
            rw [map_mul, toAdd_mul]
            rfl
          map_smul' := fun r x => by
            apply ULift.ext
            change Multiplicative.toAdd (unitsExponent w
              (@Additive.toMul (w.adicCompletion E)ˣ x ^ r.down)) = _
            rw [map_zpow, toAdd_zpow]
            rfl }
      isIntertwining' := fun σ => by
        ext x
        exact congrArg Multiplicative.toAdd
          (unitsExponent_localAut v w σ (@Additive.toMul (w.adicCompletion E)ˣ x)) }

/-- The valuation sequence `U_w → E_wˣ → ℤ`. -/
def unitsValuationSequence :
    ShortComplex (Rep.{u} IntegerScalars.{u}
      (w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E)) :=
  ShortComplex.mk (localUnitsInclusion v w) (unitsExponentMorphism v w) (by
    ext x
    exact congrArg Multiplicative.toAdd (@Additive.toMul (localUnits w) x).2)

/-- `0 → U_w → E_wˣ → ℤ → 0` is a short exact sequence of representations. -/
theorem unitsValuationSequence_shortExact : (unitsValuationSequence v w).ShortExact := by
  refine repShortExact_of_values _ ?_ ?_ ?_
  · intro a b h
    have h' : ((@Additive.toMul (localUnits w) a : localUnits w) : (w.adicCompletion E)ˣ) =
        ((@Additive.toMul (localUnits w) b : localUnits w) : (w.adicCompletion E)ˣ) := h
    exact congrArg Additive.ofMul (Subtype.ext h')
  · intro x hx
    have hx' : unitsExponent w (@Additive.toMul (w.adicCompletion E)ˣ x) = 1 :=
      Multiplicative.toAdd.injective (congrArg ULift.down hx)
    exact ⟨(Additive.ofMul (⟨@Additive.toMul (w.adicCompletion E)ˣ x, hx'⟩ : localUnits w) :
      Additive (localUnits w)), rfl⟩
  · intro n
    obtain ⟨x, hx⟩ := unitsExponent_surjective w (Multiplicative.ofAdd n.down)
    exact ⟨Additive.ofMul x, ULift.ext _ _ (congrArg Multiplicative.toAdd hx)⟩

end LocalAut

section TrivialIntegers

variable {G : Type u} [Group G] [Finite G]

/-- `H¹(G, ℤ) = Hom(G, ℤ)` vanishes for a finite group `G`. -/
theorem isZero_H1_trivial_integers :
    IsZero (groupCohomology (Rep.trivial IntegerScalars.{u} G IntegerScalars.{u}) 1) := by
  have h : ∀ φ : Additive G →+ IntegerScalars.{u}, φ = 0 := by
    intro φ
    refine AddMonoidHom.ext fun x => ?_
    have := Fintype.ofFinite G
    have hx : Fintype.card (Additive G) • x = 0 := card_nsmul_eq_zero
    have hφ : Fintype.card (Additive G) • φ x = 0 := by rw [← map_nsmul, hx, map_zero]
    have hpos : 0 < Fintype.card (Additive G) := Fintype.card_pos
    apply ULift.ext
    have h2 : Fintype.card (Additive G) • (φ x).down = 0 := congrArg ULift.down hφ
    rcases smul_eq_zero.mp h2 with h0 | h0
    · omega
    · exact h0
  have : Subsingleton
      (Additive G →+ (Rep.trivial IntegerScalars.{u} G IntegerScalars.{u} : Type u)) :=
    ⟨fun f g => (h f).trans (h g).symm⟩
  exact IsZero.of_iso (ModuleCat.isZero_of_subsingleton _)
    (groupCohomology.H1IsoOfIsTrivial _)

end TrivialIntegers

section Injective

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal]

/-- `H²(Gal(E_w/F_v), U_w) → H²(Gal(E_w/F_v), E_wˣ)` is injective. -/
theorem mono_map_localUnitsInclusion_two :
    Mono (groupCohomology.map (A := localUnitsRepresentation v w)
      (B := unitsRepresentation (padicField v).Carrier (w.adicCompletion E))
      (MonoidHom.id _) (localUnitsInclusion v w) 2) := by
  have := FiniteExtension.local_finite v w
  have hX := unitsValuationSequence_shortExact v w
  exact (groupCohomology.mapShortComplex₁_exact hX (i := 1) (j := 2) rfl).mono_g
    ((isZero_H1_trivial_integers).eq_of_src _ _)

end Injective

end Langlands.ClassField.Global
