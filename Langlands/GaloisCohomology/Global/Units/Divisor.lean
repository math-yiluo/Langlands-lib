import Langlands.GaloisCohomology.Global.Units.SUnits

/-!
# Divisors prime to `S`, and the divisor of an `S`-invariant unit of `K_S`

For a number field `F` and a set `S` of finite places, the divisors prime to `S` are the
finitely supported integer functions on the finite places outside `S` (`SDivisor`), and a unit `x`
of `F` has the divisor `v ↦ ord_v(x)` (`sDivisorOf`).

A unit `x` of `K_S` is `S`-invariant when `σ(x)/x` is an `S`-unit for every `σ ∈ G_S`
(`IsSInvariant`, `sInvariantSubgroup`); `S`-units are `S`-invariant
(`isSInvariant_of_mem_maximalSUnits`), and so is a unit with an `S`-invariant power `x ^ N`,
`N ≠ 0` (`isSInvariant_of_isSInvariant_pow`). For a place `v ∉ S`, all places above `v` of a finite Galois
subextension of `K_S` containing `x` give `x` the same valuation (`valuation_eq_of_isSInvariant`),
because `G_S` permutes them and is unramified there; this common order is `ordAbove v x`, and
`divAbove` is the resulting divisor prime to `S`. On units of `F` it is `sDivisorOf`
(`divAbove_algebraMap`); an `S`-invariant unit with divisor zero is an `S`-unit
(`mem_maximalSUnits_of_divAbove_eq_zero`). Kummer capitulation (`exists_divAbove_eq`): if `N` is
invertible outside `S` and `N • D` is the divisor of `a ∈ Fˣ`, then an `N`-th root of `a` (which lies
in `K_S`) is an `S`-invariant unit with divisor `D`.
-/

namespace Langlands.GaloisCohomology

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open Langlands.Galois

open scoped Pointwise

universe u

noncomputable section

section Divisor

variable {F : Type*} [Field F] [NumberField F]

/-- The order `ord_v(x)` of a unit `x` of `F` at a finite place `v`. -/
noncomputable def ordAt (v : HeightOneSpectrum (𝓞 F)) (x : Fˣ) : ℤ :=
  -Multiplicative.toAdd (v.valuationOfNeZero x)

/-- `ord_v` is additive. -/
theorem ordAt_mul (v : HeightOneSpectrum (𝓞 F)) (x y : Fˣ) :
    ordAt v (x * y) = ordAt v x + ordAt v y := by
  simp only [ordAt, map_mul, toAdd_mul, neg_add]

/-- `ord_v(1) = 0`. -/
theorem ordAt_one (v : HeightOneSpectrum (𝓞 F)) : ordAt v (1 : Fˣ) = 0 := by
  simp [ordAt]

/-- `ord_v(x⁻¹) = -ord_v(x)`. -/
theorem ordAt_inv (v : HeightOneSpectrum (𝓞 F)) (x : Fˣ) : ordAt v x⁻¹ = -ordAt v x := by
  simp [ordAt]

/-- `ord_v(x) = 0` exactly when `x` is a `v`-adic unit. -/
theorem ordAt_eq_zero_iff (v : HeightOneSpectrum (𝓞 F)) (x : Fˣ) :
    ordAt v x = 0 ↔ v.valuation F (x : F) = 1 := by
  rw [ordAt, neg_eq_zero, ← valuationOfNeZero_eq, ← WithZero.coe_one, WithZero.coe_inj,
    ← toAdd_one]
  exact Multiplicative.toAdd.injective.eq_iff

/-- The valuation of `x` at `v` is `exp(-ord_v(x))`. -/
theorem valuation_eq_exp_neg_ordAt (v : HeightOneSpectrum (𝓞 F)) (x : Fˣ) :
    v.valuation F (x : F) = WithZero.exp (-ordAt v x) := by
  rw [ordAt, neg_neg, ← valuationOfNeZero_eq]
  rfl

/-- A unit has nonzero order at only finitely many places. -/
theorem finite_ordAt_ne_zero (x : Fˣ) : {v : HeightOneSpectrum (𝓞 F) | ordAt v x ≠ 0}.Finite := by
  refine ((Support.finite (𝓞 F) (x : F)).union (Support.finite (𝓞 F) ((x⁻¹ : Fˣ) : F))).subset ?_
  intro v hv
  have hv' : v.valuation F (x : F) ≠ 1 := fun h => hv ((ordAt_eq_zero_iff v x).2 h)
  rcases lt_or_gt_of_ne hv' with h | h
  · right
    change 1 < v.valuation F ((x⁻¹ : Fˣ) : F)
    rw [Units.val_inv_eq_inv_val, map_inv₀]
    exact one_lt_inv₀ (lt_of_le_of_ne zero_le (((map_ne_zero (v.valuation F)).2 x.ne_zero)).symm)
      |>.2 h
  · left
    exact h

variable (S : Set (HeightOneSpectrum (𝓞 F)))

/-- The divisors of `F` prime to `S`: finitely supported functions on the finite places outside `S`. -/
abbrev SDivisor := {v : HeightOneSpectrum (𝓞 F) // v ∉ S} →₀ ℤ

/-- The divisor prime to `S` of a unit of `F`. -/
noncomputable def sDivisorOf : Additive Fˣ →+ SDivisor S where
  toFun x := Finsupp.ofSupportFinite (fun v => ordAt v.1 (Additive.toMul x)) (by
    refine ((finite_ordAt_ne_zero (Additive.toMul x)).preimage
      Subtype.val_injective.injOn).subset ?_
    intro v hv
    exact hv)
  map_zero' := by
    ext v
    simp [Finsupp.ofSupportFinite_coe, ordAt_one]
  map_add' x y := by
    ext v
    simp [Finsupp.ofSupportFinite_coe, toMul_add, ordAt_mul]

/-- The coefficient of `sDivisorOf S x` at `v` is `ord_v(x)`. -/
theorem sDivisorOf_apply (x : Additive Fˣ) (v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}) :
    sDivisorOf S x v = ordAt v.1 (Additive.toMul x) :=
  rfl

end Divisor

section Tower

variable {F : Type u} [Field F] [NumberField F] (S : Set (HeightOneSpectrum (𝓞 F)))
variable {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra F K]
  [Algebra F L] [Algebra K L] [IsScalarTower F K L]

omit [NumberField F] in
/-- Every finite place of `F` has a place of `L` above it. -/
theorem exists_under_eq (v : HeightOneSpectrum (𝓞 F)) :
    ∃ w : HeightOneSpectrum (𝓞 L), w.under (𝓞 F) = v := by
  obtain ⟨⟨Q, hQ, hQv⟩⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 L)))
  exact ⟨⟨Q, hQ, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩,
    (liesOver_iff_eq_under.1 hQv).symm⟩

omit [NumberField F] [NumberField K] [NumberField L] in
/-- The place below the place below is the place below, in a tower `F ⊆ K ⊆ L`. -/
theorem under_under_of_tower (W : HeightOneSpectrum (𝓞 L)) :
    (W.under (𝓞 K)).under (𝓞 F) = W.under (𝓞 F) :=
  HeightOneSpectrum.ext (Ideal.under_under (A := 𝓞 F) (B := 𝓞 K) W.asIdeal)

/-- At a place `W` of `L` unramified over `F`, the valuation of `y ∈ K` is that of the place of `K` below `W`. -/
theorem valuation_algebraMap_under (W : HeightOneSpectrum (𝓞 L))
    (hW : Algebra.IsUnramifiedAt (𝓞 F) W.asIdeal) (y : K) :
    W.valuation L (algebraMap K L y) = (W.under (𝓞 K)).valuation K y := by
  have hu := ((isUnramifiedAt_tower_iff (F := F) (L := K) W.asIdeal).1 hW).2
  exact valuation_algebraMap_of_isUnramifiedAt (W.under (𝓞 K)) W y

end Tower

section Field

variable {F Ω : Type u} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
variable (S : Set (HeightOneSpectrum (𝓞 F)))

/-- A unit of `K_S` is `S`-invariant when every Galois conjugate differs from it by an `S`-unit. -/
def IsSInvariant (x : (maximalUnramifiedOutside F Ω S)ˣ) : Prop :=
  ∀ σ : GaloisGroupUnramifiedOutside F Ω S, galUnitsHom F _ σ x * x⁻¹ ∈ maximalSUnits F Ω S

/-- `S`-units of `K_S` are `S`-invariant. -/
theorem isSInvariant_of_mem_maximalSUnits {y : (maximalUnramifiedOutside F Ω S)ˣ}
    (hy : y ∈ maximalSUnits F Ω S) : IsSInvariant S y := fun σ =>
  mul_mem (galUnitsHom_mem_sUnitsOf σ hy) (inv_mem hy)

/-- A unit of `K_S` with an `S`-invariant power `x ^ N`, `N ≠ 0`, is `S`-invariant. -/
theorem isSInvariant_of_isSInvariant_pow {x : (maximalUnramifiedOutside F Ω S)ˣ} {N : ℕ}
    (hN : N ≠ 0) (hx : IsSInvariant S (x ^ N)) : IsSInvariant S x := fun σ => by
  refine mem_sUnitsOf_of_pow_mem S _ hN ?_
  rw [mul_pow, ← map_pow, inv_pow]
  exact hx σ

/-- `x` has order `m` above `v`: at some place above `v` of some finite subextension of `K_S` containing `x`, its valuation is `exp(-m)`. -/
def IsOrdAbove (v : HeightOneSpectrum (𝓞 F)) (x : (maximalUnramifiedOutside F Ω S)ˣ) (m : ℤ) : Prop :=
  ∃ (E : IntermediateField F Ω) (_ : FiniteDimensional F E) (_ : E ≤ maximalUnramifiedOutside F Ω S)
    (hx : ((x : maximalUnramifiedOutside F Ω S) : Ω) ∈ E),
    letI := NumberField.of_module_finite F E
    ∃ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v ∧
      w.valuation E ⟨_, hx⟩ = WithZero.exp (-m)

variable [IsGalois F Ω]

/-- Every unit of `K_S` has an order above each place. -/
theorem exists_isOrdAbove (v : HeightOneSpectrum (𝓞 F)) (x : (maximalUnramifiedOutside F Ω S)ˣ) :
    ∃ m, IsOrdAbove S v x m := by
  obtain ⟨E, hf, hu, hx⟩ :=
    (mem_maximalUnramifiedOutside_iff S).1 (x : maximalUnramifiedOutside F Ω S).2
  have := NumberField.of_module_finite F E
  obtain ⟨w, hw⟩ := exists_under_eq (L := E) v
  have h0 : w.valuation E ⟨_, hx⟩ ≠ 0 := by
    rw [Ne, map_eq_zero]
    intro h
    apply x.ne_zero
    apply Subtype.ext
    have := congrArg Subtype.val h
    simp at this
  refine ⟨-WithZero.log (w.valuation E ⟨_, hx⟩), E, hf, le_maximalUnramifiedOutside S hu, hx, w, hw, ?_⟩
  rw [neg_neg, WithZero.exp_log h0]

end Field

section Galois

variable {F Ω : Type u} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]
variable (S : Set (HeightOneSpectrum (𝓞 F)))

/-- Every automorphism of a normal subextension of `K_S` extends to `K_S`. -/
theorem exists_galoisGroupUnramifiedOutside_restrict {M : IntermediateField F Ω} [Normal F M]
    (hMle : M ≤ maximalUnramifiedOutside F Ω S) (τ : Gal(M/F)) :
    ∃ ρ : GaloisGroupUnramifiedOutside F Ω S, ∀ y : M,
      ((ρ ⟨y, hMle y.2⟩ : maximalUnramifiedOutside F Ω S) : Ω) = ((τ y : M) : Ω) := by
  refine ⟨(τ.liftNormal Ω).restrictNormal (maximalUnramifiedOutside F Ω S), fun y => ?_⟩
  have h1 := AlgEquiv.restrictNormal_commutes (τ.liftNormal Ω) (maximalUnramifiedOutside F Ω S)
    ⟨y, hMle y.2⟩
  have h2 := AlgEquiv.liftNormal_commutes τ Ω y
  exact h1.trans h2

/-- An `S`-invariant unit has the same valuation at all places of a Galois subextension of `K_S` above a place outside `S`. -/
theorem valuation_eq_of_isSInvariant {M : IntermediateField F Ω} [FiniteDimensional F M]
    [IsGalois F M] [NumberField M] (hMle : M ≤ maximalUnramifiedOutside F Ω S)
    {x : (maximalUnramifiedOutside F Ω S)ˣ} (hx : IsSInvariant S x)
    (hxM : ((x : maximalUnramifiedOutside F Ω S) : Ω) ∈ M) (W W' : HeightOneSpectrum (𝓞 M))
    (hWW' : W.under (𝓞 F) = W'.under (𝓞 F))
    (hWS : W.under (𝓞 F) ∉ S) :
    W.valuation M ⟨_, hxM⟩ = W'.valuation M ⟨_, hxM⟩ := by
  have : IsGaloisGroup Gal(M/F) (𝓞 F) (𝓞 M) := IsGaloisGroup.of_isFractionRing _ _ _ F M
  have : W'.asIdeal.LiesOver (W.under (𝓞 F)).asIdeal := by
    rw [hWW']
    infer_instance
  obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (W.under (𝓞 F)).asIdeal
    W.asIdeal W'.asIdeal Gal(M/F)
  have hW' : W' = smulPlace σ W := HeightOneSpectrum.ext hσ.symm
  rw [hW', valuation_smulPlace_apply]
  set y : M := ⟨_, hxM⟩ with hy
  have hy0 : y ≠ 0 := by
    intro h
    apply x.ne_zero
    apply Subtype.ext
    have := congrArg Subtype.val h
    simp [hy] at this
  obtain ⟨ρ, hρ⟩ := exists_galoisGroupUnramifiedOutside_restrict S hMle σ⁻¹
  have hyu : (σ⁻¹ y / y : M) ≠ 0 := div_ne_zero ((map_ne_zero _).2 hy0) hy0
  let u : Mˣ := Units.mk0 _ hyu
  have hmap : Units.map (IntermediateField.inclusion hMle : M →* maximalUnramifiedOutside F Ω S) u =
      galUnitsHom F _ ρ x * x⁻¹ := by
    apply Units.ext
    apply Subtype.ext
    have h1 := hρ y
    simp only [Units.coe_map, Units.val_mk0, MonoidHom.coe_ofClass, Units.val_mul,
      coe_galUnitsHom_apply, Units.val_inv_eq_inv_val, IntermediateField.coe_mul,
      IntermediateField.coe_inv, u]
    rw [IntermediateField.coe_inclusion, IntermediateField.coe_div, div_eq_mul_inv]
    congr 1
    exact h1.symm
  have hu : u ∈ sUnitsOf S M := by
    rw [← map_inclusion_mem_maximalSUnits_iff F Ω S hMle, hmap]
    exact hx ρ
  have hu1 := (mem_sUnitsOf_iff_mem_unit S).1 hu W (fun h => hWS (mem_finitePlacesAbove_iff_under.1 h))
  have hu1' : W.valuation M (σ⁻¹ y / y) = 1 := hu1
  rw [map_div₀, div_eq_one_iff_eq ((map_ne_zero _).2 hy0)] at hu1'
  exact hu1'.symm

end Galois

section Ord

variable {F Ω : Type u} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]
variable (S : Set (HeightOneSpectrum (𝓞 F)))

omit [IsGalois F Ω] in
/-- An intermediate field which is a number field is finite over `F`. -/
theorem finiteDimensional_of_numberField (E : IntermediateField F Ω) [NumberField E] :
    FiniteDimensional F E :=
  Module.Finite.of_restrictScalars_finite ℚ F E

/-- A place of a smaller subextension extends, with the same valuations, to a place of a larger one. -/
theorem exists_place_valuation_eq_of_le {E M : IntermediateField F Ω} [NumberField E]
    [NumberField M] (hEM : E ≤ M) (hMle : M ≤ maximalUnramifiedOutside F Ω S)
    (w : HeightOneSpectrum (𝓞 E)) (hwS : w.under (𝓞 F) ∉ S) :
    ∃ W : HeightOneSpectrum (𝓞 M), W.under (𝓞 F) = w.under (𝓞 F) ∧
      ∀ y : E, W.valuation M ⟨y, hEM y.2⟩ = w.valuation E y := by
  have := finiteDimensional_of_numberField M
  let _ : Algebra E M := (IntermediateField.inclusion hEM).toAlgebra
  have : IsScalarTower F E M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hMu : IsUnramifiedOutside S M :=
    (isUnramifiedOutside_iff_le S).2 hMle
  obtain ⟨W, hW⟩ := exists_under_eq (F := E) (L := M) w
  have hWF : W.under (𝓞 F) = w.under (𝓞 F) := by
    rw [← hW, under_under_of_tower]
  refine ⟨W, hWF, fun y => ?_⟩
  have hun : Algebra.IsUnramifiedAt (𝓞 F) W.asIdeal :=
    hMu (W.under (𝓞 F)) (hWF ▸ hwS) W.asIdeal inferInstance inferInstance
  have := valuation_algebraMap_under (F := F) W hun y
  rw [hW] at this
  exact this

/-- For an `S`-invariant unit and a place outside `S`, the order above the place is unique. -/
theorem IsOrdAbove.unique {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S)
    {x : (maximalUnramifiedOutside F Ω S)ˣ} (hx : IsSInvariant S x) {m m' : ℤ}
    (h : IsOrdAbove S v x m) (h' : IsOrdAbove S v x m') : m = m' := by
  obtain ⟨E, hEf, hEle, hxE, hh⟩ := h
  obtain ⟨E', hE'f, hE'le, hxE', hh'⟩ := h'
  have := NumberField.of_module_finite F E
  have := NumberField.of_module_finite F E'
  obtain ⟨w, hw, hwx⟩ := hh
  obtain ⟨w', hw', hw'x⟩ := hh'
  let M : IntermediateField F Ω := IntermediateField.normalClosure F ↥(E ⊔ E') Ω
  have hMle : M ≤ maximalUnramifiedOutside F Ω S :=
    (IntermediateField.normalClosure_le_iff_of_normal (K₂ := maximalUnramifiedOutside F Ω S)).2 (sup_le hEle hE'le)
  have hEM : E ≤ M := le_sup_left.trans (IntermediateField.le_normalClosure _)
  have hE'M : E' ≤ M := le_sup_right.trans (IntermediateField.le_normalClosure _)
  have : FiniteDimensional F M := inferInstance
  have : IsGalois F M := ⟨⟩
  have := NumberField.of_module_finite F M
  obtain ⟨W, hW, hWx⟩ := exists_place_valuation_eq_of_le S hEM hMle w (hw ▸ hv)
  obtain ⟨W', hW', hW'x⟩ := exists_place_valuation_eq_of_le S hE'M hMle w' (hw' ▸ hv)
  have e1 := hWx ⟨_, hxE⟩
  have e2 := hW'x ⟨_, hxE'⟩
  have e3 := valuation_eq_of_isSInvariant S hMle hx (hEM hxE) W W' (by rw [hW, hW', hw, hw'])
    (by rw [hW, hw]; exact hv)
  have : WithZero.exp (-m) = WithZero.exp (-m') := by
    rw [← hwx, ← hw'x, ← e1, ← e2]
    exact e3
  simpa using this

/-- The order of a unit of `K_S` above a place of `F` (meaningful outside `S` for `S`-invariant units). -/
noncomputable def ordAbove (v : HeightOneSpectrum (𝓞 F)) (x : (maximalUnramifiedOutside F Ω S)ˣ) : ℤ :=
  (exists_isOrdAbove S v x).choose

/-- `ordAbove v x` is an order of `x` above `v`. -/
theorem isOrdAbove_ordAbove (v : HeightOneSpectrum (𝓞 F)) (x : (maximalUnramifiedOutside F Ω S)ˣ) :
    IsOrdAbove S v x (ordAbove S v x) :=
  (exists_isOrdAbove S v x).choose_spec

/-- `ordAbove` is the order above `v` for `S`-invariant units and `v ∉ S`. -/
theorem ordAbove_eq_of_isOrdAbove {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S)
    {x : (maximalUnramifiedOutside F Ω S)ˣ} (hx : IsSInvariant S x) {m : ℤ}
    (h : IsOrdAbove S v x m) : ordAbove S v x = m :=
  IsOrdAbove.unique S hv hx (isOrdAbove_ordAbove S v x) h

/-- At every place above `v ∉ S` of a subextension containing an `S`-invariant `x`, the valuation of `x` is `exp(-ordAbove v x)`. -/
theorem valuation_eq_exp_ordAbove {x : (maximalUnramifiedOutside F Ω S)ˣ} (hx : IsSInvariant S x)
    {E : IntermediateField F Ω} [NumberField E] (hEle : E ≤ maximalUnramifiedOutside F Ω S)
    (hxE : ((x : maximalUnramifiedOutside F Ω S) : Ω) ∈ E) (w : HeightOneSpectrum (𝓞 E))
    (hwS : w.under (𝓞 F) ∉ S) :
    w.valuation E ⟨_, hxE⟩ = WithZero.exp (-ordAbove S (w.under (𝓞 F)) x) := by
  have h0 : w.valuation E ⟨_, hxE⟩ ≠ 0 := by
    rw [Ne, map_eq_zero]
    intro h
    apply x.ne_zero
    apply Subtype.ext
    have := congrArg Subtype.val h
    simp at this
  have hE := finiteDimensional_of_numberField E
  have hw : IsOrdAbove S (w.under (𝓞 F)) x (-WithZero.log (w.valuation E ⟨_, hxE⟩)) :=
    ⟨E, hE, hEle, hxE, w, rfl, by rw [neg_neg, WithZero.exp_log h0]⟩
  rw [ordAbove_eq_of_isOrdAbove S hwS hx hw, neg_neg, WithZero.exp_log h0]

end Ord

section Div

variable {F Ω : Type u} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]
variable (S : Set (HeightOneSpectrum (𝓞 F)))

omit [NumberField F] [IsGalois F Ω] in
/-- The Galois action on a quotient of units. -/
theorem galUnitsHom_mul_inv_eq (σ : GaloisGroupUnramifiedOutside F Ω S) (x y : (maximalUnramifiedOutside F Ω S)ˣ) :
    galUnitsHom F _ σ (x * y) * (x * y)⁻¹ = (galUnitsHom F _ σ x * x⁻¹) * (galUnitsHom F _ σ y * y⁻¹) := by
  rw [map_mul, mul_inv]
  ac_rfl

variable (Ω) in

/-- The subgroup of `S`-invariant units of `K_S`. -/
def sInvariantSubgroup : Subgroup (maximalUnramifiedOutside F Ω S)ˣ where
  carrier := {x | IsSInvariant S x}
  mul_mem' {x y} hx hy σ := by
    rw [galUnitsHom_mul_inv_eq]
    exact mul_mem (hx σ) (hy σ)
  one_mem' σ := by
    rw [map_one, inv_one, mul_one]
    exact one_mem _
  inv_mem' {x} hx σ := by
    have : galUnitsHom F _ σ x⁻¹ * x⁻¹⁻¹ = (galUnitsHom F _ σ x * x⁻¹)⁻¹ := by
      rw [map_inv, inv_inv, mul_inv, inv_inv, mul_comm]
    rw [this]
    exact inv_mem (hx σ)

omit [IsGalois F Ω] in
/-- Membership in `sInvariantSubgroup`. -/
theorem mem_sInvariantSubgroup {x : (maximalUnramifiedOutside F Ω S)ˣ} :
    x ∈ sInvariantSubgroup Ω S ↔ IsSInvariant S x :=
  Iff.rfl

omit [IsGalois F Ω] in
/-- Units of `F` are `S`-invariant. -/
theorem map_algebraMap_mem_sInvariantSubgroup (a : Fˣ) :
    Units.map (algebraMap F (maximalUnramifiedOutside F Ω S) : F →* _) a ∈ sInvariantSubgroup Ω S := by
  intro σ
  have : galUnitsHom F _ σ (Units.map (algebraMap F (maximalUnramifiedOutside F Ω S) : F →* _) a) =
      Units.map (algebraMap F (maximalUnramifiedOutside F Ω S) : F →* _) a :=
    Units.ext (σ.commutes _)
  rw [this, mul_inv_cancel]
  exact one_mem _

/-- Every element of `K_S` lies in a finite subextension. -/
theorem exists_numberField_mem (x : (maximalUnramifiedOutside F Ω S)ˣ) :
    ∃ E : IntermediateField F Ω, NumberField E ∧ E ≤ maximalUnramifiedOutside F Ω S ∧
      ((x : maximalUnramifiedOutside F Ω S) : Ω) ∈ E := by
  obtain ⟨E, hf, hu, hx⟩ :=
    (mem_maximalUnramifiedOutside_iff S).1 (x : maximalUnramifiedOutside F Ω S).2
  exact ⟨E, NumberField.of_module_finite F E, le_maximalUnramifiedOutside S hu, hx⟩

/-- An `S`-invariant unit has nonzero order above only finitely many places outside `S`. -/
theorem finite_ordAbove_ne_zero {x : (maximalUnramifiedOutside F Ω S)ˣ} (hx : IsSInvariant S x) :
    {v : HeightOneSpectrum (𝓞 F) | v ∉ S ∧ ordAbove S v x ≠ 0}.Finite := by
  obtain ⟨E, hE, hEle, hxE⟩ := exists_numberField_mem S x
  have hx0 : (⟨_, hxE⟩ : E) ≠ 0 := by
    intro h
    apply x.ne_zero
    apply Subtype.ext
    have := congrArg Subtype.val h
    simp at this
  refine ((finite_ordAt_ne_zero (Units.mk0 _ hx0)).image (fun w : HeightOneSpectrum (𝓞 E) => w.under (𝓞 F))).subset ?_
  rintro v ⟨hv, hvo⟩
  obtain ⟨w, hw⟩ := exists_under_eq (L := E) v
  refine ⟨w, ?_, hw⟩
  intro h0
  apply hvo
  have h1 := valuation_eq_exp_ordAbove S hx hEle hxE w (hw ▸ hv)
  have h2 := (ordAt_eq_zero_iff w _).1 h0
  rw [Units.val_mk0] at h2
  rw [h2, hw] at h1
  have := congrArg WithZero.log h1
  simpa using this.symm

/-- `ordAbove v 1 = 0`. -/
theorem ordAbove_one {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) :
    ordAbove S v (1 : (maximalUnramifiedOutside F Ω S)ˣ) = 0 := by
  refine ordAbove_eq_of_isOrdAbove S hv (one_mem (sInvariantSubgroup Ω S)) ?_
  obtain ⟨E, hE, hEle, hxE⟩ := exists_numberField_mem S (1 : (maximalUnramifiedOutside F Ω S)ˣ)
  obtain ⟨w, hw⟩ := exists_under_eq (L := E) v
  refine ⟨E, finiteDimensional_of_numberField E, hEle, hxE, w, hw, ?_⟩
  have : (⟨_, hxE⟩ : E) = 1 := Subtype.ext (by simp)
  rw [this, map_one, neg_zero, WithZero.exp_zero]

/-- `ordAbove v` is additive on `S`-invariant units. -/
theorem ordAbove_mul {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S)
    {x y : (maximalUnramifiedOutside F Ω S)ˣ} (hx : IsSInvariant S x) (hy : IsSInvariant S y) :
    ordAbove S v (x * y) = ordAbove S v x + ordAbove S v y := by
  obtain ⟨E, hE, hEle, hxE⟩ := exists_numberField_mem S x
  obtain ⟨E', hE', hE'le, hyE'⟩ := exists_numberField_mem S y
  have : FiniteDimensional F E := finiteDimensional_of_numberField E
  have : FiniteDimensional F E' := finiteDimensional_of_numberField E'
  have := NumberField.of_module_finite F ↥(E ⊔ E')
  have hle := sup_le hEle hE'le
  have hxE'' : ((x : maximalUnramifiedOutside F Ω S) : Ω) ∈ E ⊔ E' :=
    le_sup_left (α := IntermediateField F Ω) hxE
  have hyE'' : ((y : maximalUnramifiedOutside F Ω S) : Ω) ∈ E ⊔ E' :=
    le_sup_right (α := IntermediateField F Ω) hyE'
  have hxy : (((x * y : (maximalUnramifiedOutside F Ω S)ˣ) : maximalUnramifiedOutside F Ω S) : Ω) ∈
      E ⊔ E' := by
    simp only [Units.val_mul, IntermediateField.coe_mul]
    exact mul_mem hxE'' hyE''
  obtain ⟨w, hw⟩ := exists_under_eq (L := ↥(E ⊔ E')) v
  have hxy' : IsSInvariant S (x * y) := (mul_mem hx hy : x * y ∈ sInvariantSubgroup Ω S)
  have h1 := valuation_eq_exp_ordAbove S hxy' hle hxy w (hw ▸ hv)
  have h2 := valuation_eq_exp_ordAbove S hx hle hxE'' w (hw ▸ hv)
  have h3 := valuation_eq_exp_ordAbove S hy hle hyE'' w (hw ▸ hv)
  have hmul : (⟨_, hxy⟩ : ↥(E ⊔ E')) = ⟨_, hxE''⟩ * ⟨_, hyE''⟩ := Subtype.ext (by simp)
  rw [hmul, map_mul, h2, h3, hw, ← WithZero.exp_add] at h1
  have := congrArg WithZero.log h1
  simp only [WithZero.log_exp] at this
  omega

/-- The divisor prime to `S` of an `S`-invariant unit of `K_S`. -/
noncomputable def divAbove : Additive (sInvariantSubgroup Ω S) →+ SDivisor S where
  toFun x := Finsupp.ofSupportFinite
    (fun v => ordAbove S v.1 ((Additive.toMul x : sInvariantSubgroup Ω S) : (maximalUnramifiedOutside F Ω S)ˣ))
    (((finite_ordAbove_ne_zero S (Additive.toMul x).2).preimage Subtype.val_injective.injOn).subset
      fun v hv => ⟨v.2, Function.mem_support.1 hv⟩)
  map_zero' := by
    ext v
    exact ordAbove_one S v.2
  map_add' x y := by
    ext v
    exact ordAbove_mul S v.2 (Additive.toMul x).2 (Additive.toMul y).2

/-- The coefficient of `divAbove S x` at `v` is `ordAbove v x`. -/
theorem divAbove_apply (x : Additive (sInvariantSubgroup Ω S)) (v : {v // v ∉ S}) :
    divAbove S x v =
      ordAbove S v.1 ((Additive.toMul x : sInvariantSubgroup Ω S) : (maximalUnramifiedOutside F Ω S)ˣ) :=
  rfl

end Div

section Descent

variable {F Ω : Type u} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]
variable (S : Set (HeightOneSpectrum (𝓞 F)))

/-- An `S`-invariant unit with divisor zero is an `S`-unit. -/
theorem mem_maximalSUnits_of_divAbove_eq_zero {x : sInvariantSubgroup Ω S}
    (h : divAbove S (Additive.ofMul x) = 0) :
    (x : (maximalUnramifiedOutside F Ω S)ˣ) ∈ maximalSUnits F Ω S := by
  obtain ⟨E, hE, hEle, hxE⟩ := exists_numberField_mem S (x : (maximalUnramifiedOutside F Ω S)ˣ)
  have hx0 : (⟨_, hxE⟩ : E) ≠ 0 := by
    intro h
    apply (x : (maximalUnramifiedOutside F Ω S)ˣ).ne_zero
    apply Subtype.ext
    have := congrArg Subtype.val h
    simp at this
  have hmem : Units.mk0 _ hx0 ∈ sUnitsOf S E := by
    rw [mem_sUnitsOf_iff_mem_unit]
    intro w hw
    have hwS : w.under (𝓞 F) ∉ S := fun h => hw (mem_finitePlacesAbove_iff_under.2 h)
    have h1 := valuation_eq_exp_ordAbove S x.2 hEle hxE w hwS
    have h2 : ordAbove S (w.under (𝓞 F)) (x : (maximalUnramifiedOutside F Ω S)ˣ) = 0 := by
      have := congrArg (fun D : SDivisor S => D ⟨_, hwS⟩) h
      simpa [divAbove_apply] using this
    rw [Units.val_mk0, h1, h2, neg_zero, WithZero.exp_zero]
  have hmap : Units.map (IntermediateField.inclusion hEle : E →* maximalUnramifiedOutside F Ω S)
      (Units.mk0 _ hx0) = x := Units.ext rfl
  rw [← hmap]
  exact (map_inclusion_mem_maximalSUnits_iff F Ω S hEle).2 hmem

/-- On units of `F`, `divAbove` is `sDivisorOf`. -/
theorem divAbove_algebraMap (a : Fˣ) :
    divAbove S (Additive.ofMul ⟨_, map_algebraMap_mem_sInvariantSubgroup (Ω := Ω) S a⟩) =
      sDivisorOf S (Additive.ofMul a) := by
  ext v
  rw [divAbove_apply, sDivisorOf_apply]
  refine ordAbove_eq_of_isOrdAbove S v.2 (map_algebraMap_mem_sInvariantSubgroup (Ω := Ω) S a) ?_
  obtain ⟨E, hE, hEle, hxE⟩ := exists_numberField_mem (Ω := Ω) S
    (Units.map (algebraMap F (maximalUnramifiedOutside F Ω S) : F →* _) a)
  obtain ⟨w, hw⟩ := exists_under_eq (L := E) v.1
  have hEf := finiteDimensional_of_numberField E
  refine ⟨E, hEf, hEle, hxE, w, hw, ?_⟩
  have hE : IsUnramifiedOutside S E := (isUnramifiedOutside_iff_le S).2 hEle
  have : w.asIdeal.LiesOver v.1.asIdeal := liesOver_iff_eq_under.2 hw.symm
  have : Algebra.IsUnramifiedAt (𝓞 F) w.asIdeal := hE v.1 v.2 w.asIdeal inferInstance this
  have he : (⟨_, hxE⟩ : E) = algebraMap F E (a : F) := rfl
  rw [he, valuation_algebraMap_of_isUnramifiedAt v.1 w, valuation_eq_exp_neg_ordAt]
  rfl

end Descent

section Capitulation

variable {F Ω : Type u} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]
  [IsSepClosed Ω]
variable (S : Set (HeightOneSpectrum (𝓞 F)))

/-- Capitulation by Kummer theory: if `N` is invertible outside `S` and `N • D` is the divisor of a unit of `F`, then `D` is the divisor of an `S`-invariant unit of `K_S`. -/
theorem exists_divAbove_eq {N : ℕ} (hN : N ≠ 0) (hNS : ∀ v ∉ S, ((N : ℕ) : 𝓞 F) ∉ v.asIdeal)
    (D : SDivisor S) (a : Fˣ) (ha : sDivisorOf S (Additive.ofMul a) = N • D) :
    ∃ x : sInvariantSubgroup Ω S, divAbove S (Additive.ofMul x) = D := by
  have : NeZero ((N : ℕ) : Ω) := ⟨by
    rw [← map_natCast (algebraMap F Ω)]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hN)⟩
  obtain ⟨α, hα⟩ := IsSepClosed.exists_pow_nat_eq (algebraMap F Ω (a : F)) N
  have hαint : IsIntegral F α := IsIntegral.of_pow (Nat.pos_of_ne_zero hN) (hα ▸ isIntegral_algebraMap)
  let E : IntermediateField F Ω := IntermediateField.adjoin F {α}
  have : FiniteDimensional F E := IntermediateField.adjoin.finiteDimensional hαint
  have : NumberField E := NumberField.of_module_finite F E
  have hβ : IntermediateField.AdjoinSimple.gen F α ^ N = algebraMap F E (a : F) := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, IntermediateField.AdjoinSimple.coe_gen, hα]
    rfl
  have hdiv : ∀ v ∉ S, (N : ℤ) ∣ WithZero.log (v.valuation F (a : F)) := by
    intro v hv
    have := congrArg (fun D' : SDivisor S => D' ⟨v, hv⟩) ha
    simp only [sDivisorOf_apply, toMul_ofMul, Finsupp.smul_apply, nsmul_eq_mul] at this
    rw [valuation_eq_exp_neg_ordAt, WithZero.log_exp, this]
    exact ⟨-D ⟨v, hv⟩, by ring⟩
  have hEu : IsUnramifiedOutside S E := fun v hv =>
    isUnramifiedIn_of_pow_eq a hβ (adjoin_gen_eq_top F α) v (hNS v hv) (hdiv v hv)
  have hEle : E ≤ maximalUnramifiedOutside F Ω S := le_maximalUnramifiedOutside S hEu
  have hαS : α ∈ maximalUnramifiedOutside F Ω S := hEle (IntermediateField.mem_adjoin_simple_self F α)
  have hα0 : (⟨α, hαS⟩ : maximalUnramifiedOutside F Ω S) ≠ 0 := by
    intro h
    have h' : α = 0 := congrArg Subtype.val h
    rw [h', zero_pow hN] at hα
    exact a.ne_zero ((map_eq_zero _).1 hα.symm)
  let x : (maximalUnramifiedOutside F Ω S)ˣ := Units.mk0 _ hα0
  have hxN : x ^ N = Units.map (algebraMap F (maximalUnramifiedOutside F Ω S) : F →* _) a :=
    Units.ext (Subtype.ext (by
      rw [Units.val_pow_eq_pow_val, Units.val_mk0, SubmonoidClass.coe_pow]
      exact hα))
  have hx : IsSInvariant S x := by
    intro σ
    apply mem_sUnitsOf_of_mem_rootsOfUnity hN
    rw [mem_rootsOfUnity, mul_pow, ← map_pow, hxN, inv_pow, hxN]
    have : galUnitsHom F _ σ (Units.map (algebraMap F (maximalUnramifiedOutside F Ω S) : F →* _) a) =
        Units.map (algebraMap F (maximalUnramifiedOutside F Ω S) : F →* _) a :=
      Units.ext (σ.commutes _)
    rw [this, mul_inv_cancel]
  refine ⟨⟨x, hx⟩, ?_⟩
  ext v
  rw [divAbove_apply]
  obtain ⟨w, hw⟩ := exists_under_eq (L := E) v.1
  have hαE : ((x : maximalUnramifiedOutside F Ω S) : Ω) ∈ E := IntermediateField.mem_adjoin_simple_self F α
  have h1 := valuation_eq_exp_ordAbove S hx hEle hαE w (hw ▸ v.2)
  have : w.asIdeal.LiesOver v.1.asIdeal := liesOver_iff_eq_under.2 hw.symm
  have : Algebra.IsUnramifiedAt (𝓞 F) w.asIdeal := hEu v.1 v.2 w.asIdeal inferInstance this
  have h2 := valuation_algebraMap_of_isUnramifiedAt v.1 w (a : F)
  rw [← hβ, map_pow, valuation_eq_exp_neg_ordAt] at h2
  have hgen : IntermediateField.AdjoinSimple.gen F α = ⟨_, hαE⟩ := rfl
  rw [hgen, h1, hw, ← WithZero.exp_nsmul] at h2
  have h3 := congrArg WithZero.log h2
  simp only [WithZero.log_exp, smul_neg, nsmul_eq_mul] at h3
  have h4 := congrArg (fun D' : SDivisor S => D' v) ha
  simp only [sDivisorOf_apply, toMul_ofMul, Finsupp.smul_apply, nsmul_eq_mul] at h4
  rw [h4] at h3
  have hN' : (N : ℤ) ≠ 0 := Nat.cast_ne_zero.2 hN
  have := mul_left_cancel₀ hN' (neg_injective h3)
  exact this

end Capitulation

end

end Langlands.GaloisCohomology
