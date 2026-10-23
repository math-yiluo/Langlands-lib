import Langlands.ClassField.Global.CompletionTower

/-! # The local Artin symbol of a cyclotomic extension and the abstract invariants -/

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Topology
open scoped NumberField Langlands.Global.AdelicFunctoriality.FiniteExtension
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic
open Langlands.ClassFieldTheory.Local Langlands.Global.CyclotomicSymbol

namespace Langlands.ClassField.Global

universe u

namespace LocalSymbolIdentity

open FundamentalClass CompletionTower

section Artin

variable {F L : Type u} [Field F] [Field L] [NumberField F] [NumberField L] [Algebra F L]
  [IsGalois F L] {m : ℕ} [NeZero m] {ζ : L} (hζ : IsPrimitiveRoot ζ m)
  (hinj : Function.Injective (hζ.autToPow F)) (v : HeightOneSpectrum (𝓞 F))

/-- The place `v` as a place above its rational place. -/
def placeAboveRational : FinitePlacesAbove F (rationalPlace v) := ⟨v, inferInstance⟩

/-- The local Artin symbol `F_vˣ → Gal(L/F)` of a cyclotomic extension: the unique `σ` acting on
`ζ` by the cyclotomic symbol of the local norm. -/
def artinSymbol : (v.adicCompletion F)ˣ →* (L ≃ₐ[F] L) :=
  ((MonoidHom.ofInjective hinj).symm.toMonoidHom).comp
    ((normSymbolAt m (rationalPlace v) v).codRestrict (galoisImage F hζ)
      fun b => normSymbolAt_mem_galoisImage m hζ (rationalPlace v) (placeAboveRational v) b)

theorem autToPow_artinSymbol (b : (v.adicCompletion F)ˣ) :
    hζ.autToPow F (artinSymbol hζ hinj v b) = normSymbolAt m (rationalPlace v) v b := by
  have h := (MonoidHom.ofInjective hinj).apply_symm_apply
    ⟨normSymbolAt m (rationalPlace v) v b,
      normSymbolAt_mem_galoisImage m hζ (rationalPlace v) (placeAboveRational v) b⟩
  exact congrArg Subtype.val h

omit [NumberField F] [NumberField L] [IsGalois F L] in
/-- `autToPow` does not depend on the base field. -/
theorem autToPow_restrictScalars {K : Type*} [Field K] [Algebra F K] [Algebra K L]
    [IsScalarTower F K L] (τ : L ≃ₐ[K] L) :
    hζ.autToPow F (τ.restrictScalars F) = hζ.autToPow K τ := by
  apply Units.ext
  have h1 := hζ.autToPow_spec F (τ.restrictScalars F)
  have h2 := hζ.autToPow_spec K τ
  have h3 : ζ ^ ((hζ.autToPow F (τ.restrictScalars F) : (ZMod m)ˣ) : ZMod m).val =
      ζ ^ ((hζ.autToPow K τ : (ZMod m)ˣ) : ZMod m).val := h1.trans h2.symm
  exact ZMod.val_injective _ (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h3)

variable (H : Subgroup (L ≃ₐ[F] L)) [H.Normal] (u : HeightOneSpectrum (𝓞 L))
  [u.asIdeal.LiesOver v.asIdeal]

omit [H.Normal] in
/-- **Norms lie in the norm group.** The Artin symbol of a local norm from the completion of the
fixed field `L^H` lies in `H`. -/
theorem artinSymbol_norm_mem
    (b : ((fixedFieldPlace H u).adicCompletion (IntermediateField.fixedField H))ˣ) :
    artinSymbol hζ hinj v (Units.map (FiniteExtension.localNorm v (fixedFieldPlace H u)) b) ∈ H := by
  have : (fixedFieldPlace H u).asIdeal.LiesOver (rationalPlace v).asIdeal :=
    Ideal.LiesOver.trans (fixedFieldPlace H u).asIdeal v.asIdeal (rationalPlace v).asIdeal
  have hmem := normSymbolAt_mem_galoisImage m hζ (K := IntermediateField.fixedField H)
    (rationalPlace v) ⟨fixedFieldPlace H u, this⟩ b
  rw [← normSymbolAt_localNorm (rationalPlace v) v (fixedFieldPlace H u) m b] at hmem
  obtain ⟨τ, hτ⟩ := hmem
  have h1 : artinSymbol hζ hinj v
      (Units.map (FiniteExtension.localNorm v (fixedFieldPlace H u)) b) =
      τ.restrictScalars F := by
    apply hinj
    rw [autToPow_artinSymbol, autToPow_restrictScalars]
    exact hτ.symm
  rw [h1]
  have hfix : τ.restrictScalars F ∈
      IntermediateField.fixingSubgroup (IntermediateField.fixedField H) :=
    (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => τ.commutes ⟨x, hx⟩
  rwa [IntermediateField.fixingSubgroup_fixedField] at hfix

end Artin

section RationalClass

/-- An element of `ℚ/ℤ` killed by `e > 0` is `k / e` for some `0 ≤ k < e`. -/
theorem exists_nat_of_nsmul_eq_zero {e : ℕ} (he : 0 < e) (x : RationalModIntegers)
    (h : e • x = 0) : ∃ k : ℕ, k < e ∧ x = rationalClass ((k : ℚ) / e) := by
  obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective x
  have h1 : ((e : ℚ) * q) ∈ AddSubgroup.zmultiples (1 : ℚ) := by
    have h2 : ((e • q : ℚ) : RationalModIntegers) = 0 := by
      rw [← h]
      rfl
    rw [QuotientAddGroup.eq_zero_iff, nsmul_eq_mul] at h2
    exact h2
  obtain ⟨z, hz⟩ := AddSubgroup.mem_zmultiples_iff.1 h1
  rw [zsmul_eq_mul, mul_one] at hz
  have he' : (e : ℚ) ≠ 0 := by exact_mod_cast he.ne'
  refine ⟨(z % (e : ℤ)).toNat, ?_, ?_⟩
  · have h3 := Int.emod_lt_of_pos z (by exact_mod_cast he : (0 : ℤ) < e)
    have h4 := Int.emod_nonneg z (by exact_mod_cast he.ne' : (e : ℤ) ≠ 0)
    omega
  · have h4 := Int.emod_nonneg z (by exact_mod_cast he.ne' : (e : ℤ) ≠ 0)
    have hq : q = (z : ℚ) / e := by
      rw [eq_div_iff he', mul_comm, hz]
    have hk : (((z % (e : ℤ)).toNat : ℕ) : ℚ) = ((z % (e : ℤ) : ℤ) : ℚ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg h4]
    rw [hk, hq]
    change rationalClass ((z : ℚ) / e) = rationalClass (((z % (e : ℤ) : ℤ) : ℚ) / e)
    rw [← sub_eq_zero, ← map_sub]
    apply (QuotientAddGroup.eq_zero_iff _).2
    refine AddSubgroup.mem_zmultiples_iff.2 ⟨z / e, ?_⟩
    rw [zsmul_eq_mul, mul_one]
    have h5 := Int.ediv_mul_add_emod z (e : ℤ)
    have h6 : ((z / (e : ℤ) : ℤ) : ℚ) * e = (z : ℚ) - ((z % (e : ℤ) : ℤ) : ℚ) := by
      rw [eq_sub_iff_add_eq]
      exact_mod_cast h5
    field_simp
    linarith

end RationalClass

section ZModClass

/-- The additive map `ℤ/e → ℚ/ℤ`, `z ↦ z.val / e`. -/
def zmodClass (e : ℕ) [NeZero e] : ZMod e →+ RationalModIntegers where
  toFun z := rationalClass ((z.val : ℚ) / e)
  map_zero' := by simp
  map_add' x y := by
    rw [← map_add]
    have h := cyclicCarry_rational x y
    rw [← sub_eq_zero, ← map_sub]
    apply (QuotientAddGroup.eq_zero_iff _).2
    refine AddSubgroup.mem_zmultiples_iff.2 ⟨-(cyclicCarry x y : ℤ), ?_⟩
    rw [zsmul_eq_mul, mul_one]
    push_cast
    linarith

theorem zmodClass_apply (e : ℕ) [NeZero e] (z : ZMod e) :
    zmodClass e z = rationalClass ((z.val : ℚ) / e) := rfl

end ZModClass

section Theta

variable {F L : Type u} [Field F] [Field L] [NumberField F] [NumberField L] [Algebra F L]
  [IsGalois F L] (hcomm : ∀ σ τ : L ≃ₐ[F] L, σ * τ = τ * σ)
  {m : ℕ} [NeZero m] {ζ : L} (hζ : IsPrimitiveRoot ζ m)
  (hinj : Function.Injective (hζ.autToPow F))
  (v : HeightOneSpectrum (𝓞 F)) (u : HeightOneSpectrum (𝓞 L)) [u.asIdeal.LiesOver v.asIdeal]

omit [NumberField F] [NumberField L] [IsGalois F L] in
include hcomm in
theorem normal_of_comm (H : Subgroup (L ≃ₐ[F] L)) : H.Normal :=
  ⟨fun n hn g => by rw [hcomm g n, mul_inv_cancel_right]; exact hn⟩

include hcomm in
/-- **The θ-trick.** Let `U = L^{H_U}` have an unramified completion with arithmetic coordinate
`χ_U`, and let the Artin symbol of `π` (of order `1`) restrict to the arithmetic Frobenius
of `U`. Then for every character `ψ` of `Gal(L/F)` into `ℤ/e`, the abstract invariant of the
local carry class of `π` is `ψ(Art π) / e`. -/
theorem relative_cyclicClass_uniformizer (I : InvariantFamily.{u, u} (residuePrime v))
    (hI : I.RelativeClassFormation ∧ I.ArithmeticNormalization)
    (HU : Subgroup (L ≃ₐ[F] L)) [HU.Normal] {e : ℕ} [NeZero e]
    (χU : (((fixedFieldPlace HU u).adicCompletion (IntermediateField.fixedField HU)) ≃ₐ[v.adicCompletion F]
      ((fixedFieldPlace HU u).adicCompletion (IntermediateField.fixedField HU))) ≃*
        Multiplicative (ZMod e))
    (hχU : IsArithmeticUnramifiedCoordinate (padicField v)
      ((fixedFieldPlace HU u).adicCompletion (IntermediateField.fixedField HU)) χU)
    (π : (v.adicCompletion F)ˣ) (hπ : (padicField v).canonicalTopologicalData.ord (π : v.adicCompletion F) = 1)
    (hfrob : decompositionHom v (fixedFieldPlace HU u) (χU.symm (Multiplicative.ofAdd 1)) =
      (artinSymbol hζ hinj v π).restrictNormal (IntermediateField.fixedField HU))
    (ψ : (L ≃ₐ[F] L) →* Multiplicative (ZMod e)) :
    haveI := isGalois_adicCompletion v u
    haveI := FiniteExtension.local_finite v u
    I.relative (padicField v) (u.adicCompletion L)
        (cyclicClass (v.adicCompletion F) (u.adicCompletion L) (ψ.comp (decompositionHom v u)) π) =
      rationalClass (((ψ (artinSymbol hζ hinj v π)).toAdd.val : ℚ) / e) := by
  obtain ⟨⟨_, hImages, hInf, _⟩, hNorm⟩ := hI
  have := isGalois_adicCompletion v u
  have := FiniteExtension.local_finite v u
  set U := IntermediateField.fixedField HU
  set wU := fixedFieldPlace HU u
  have := isGalois_adicCompletion v wU
  have := FiniteExtension.local_finite v wU
  have := FiniteExtension.local_finite wU u
  set ψloc := ψ.comp (decompositionHom v u)
  set rU := AlgEquiv.restrictNormalHom (F := v.adicCompletion F) (K₁ := u.adicCompletion L)
    (wU.adicCompletion U)
  set χ' := χU.toMonoidHom.comp rU
  have he : 0 < e := Nat.pos_of_ne_zero (NeZero.ne e)
  -- (1) the invariant of the class of `ψ` is `k / e`
  set x := I.relative (padicField v) (u.adicCompletion L)
    (cyclicClass (v.adicCompletion F) (u.adicCompletion L) ψloc π) with hx
  have hex : e • x = 0 := by
    rw [hx, ← map_nsmul, ← CyclicClassAlgebra.cyclicClass_pow_character]
    have h1 : ψloc ^ e = 1 := by
      ext g
      simp only [MonoidHom.pow_apply, MonoidHom.one_apply]
      rw [← ofAdd_toAdd (ψloc g), ← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul,
        ofAdd_zero]
    rw [h1, CyclicClassAlgebra.cyclicClass_one_character, map_zero]
  obtain ⟨k, hk, hxk⟩ := exists_nat_of_nsmul_eq_zero he x hex
  -- (2) the invariant of the inflated arithmetic coordinate is `1 / e`
  have hy : I.relative (padicField v) (u.adicCompletion L)
      (cyclicClass (v.adicCompletion F) (u.adicCompletion L) χ' π) = rationalClass ((e : ℚ)⁻¹) := by
    rw [← CyclicClassAlgebra.relativeInflation_cyclicClass,
      hInf (padicField v) (wU.adicCompletion U) (u.adicCompletion L)]
    exact hNorm (padicField v) (wU.adicCompletion U) e χU hχU π hπ
  -- (3) the character `θ = ψ - k χ'` has invariant `0`
  set θ := ψloc * (χ' ^ k)⁻¹ with hθ
  have hθ0 : I.relative (padicField v) (u.adicCompletion L)
      (cyclicClass (v.adicCompletion F) (u.adicCompletion L) θ π) = 0 := by
    rw [hθ, CyclicClassAlgebra.cyclicClass_mul_character,
      CyclicClassAlgebra.cyclicClass_inv_character, CyclicClassAlgebra.cyclicClass_pow_character,
      map_add, map_neg, map_nsmul, hy, ← hx, hxk, ← map_nsmul, nsmul_eq_mul, ← map_neg,
      ← map_add]
    rw [show ((k : ℚ) / e + -(k * (e : ℚ)⁻¹)) = 0 by ring, map_zero]
  -- (4) the fixed field of the global image of `ker θ`
  set H := θ.ker.map (decompositionHom v u) with hH
  have : H.Normal := normal_of_comm hcomm H
  set K₁ := IntermediateField.fixedField H
  set w₁ := fixedFieldPlace H u
  have := isGalois_adicCompletion v w₁
  have := FiniteExtension.local_finite v w₁
  have := FiniteExtension.local_finite w₁ u
  set r₁ := AlgEquiv.restrictNormalHom (F := v.adicCompletion F) (K₁ := u.adicCompletion L)
    (w₁.adicCompletion K₁)
  have hker : ∀ σ, r₁ σ = 1 ↔ θ σ = 1 := by
    intro σ
    change σ.restrictNormal (w₁.adicCompletion K₁) = 1 ↔ _
    rw [restrictNormal_eq_one_iff H v u σ, hH,
      Subgroup.mem_map_iff_mem (decompositionHom_injective v u), MonoidHom.mem_ker]
  obtain ⟨θ', hθ'inj, hθ'r⟩ := exists_injective_factor r₁
    (restrictNormalHom_surjective_completion v w₁ u) θ hker
  have hθ'comp : θ'.comp r₁ = θ := MonoidHom.ext hθ'r
  -- (5) the class of `θ'` over the completion of `K₁` vanishes, so `π` is a norm
  have hθ'0 : I.relative (padicField v) (w₁.adicCompletion K₁)
      (cyclicClass (v.adicCompletion F) (w₁.adicCompletion K₁) θ' π) = 0 := by
    rw [← hInf (padicField v) (w₁.adicCompletion K₁) (u.adicCompletion L),
      CyclicClassAlgebra.relativeInflation_cyclicClass]
    erw [hθ'comp]
    exact hθ0
  have hz : I.relative (padicField v) (w₁.adicCompletion K₁) 0 = 0 :=
    (I.relative (padicField v) (w₁.adicCompletion K₁)).map_zero
  have hclass : cyclicClass (v.adicCompletion F) (w₁.adicCompletion K₁) θ' π = 0 :=
    (hImages (padicField v) (w₁.adicCompletion K₁)).1 (hθ'0.trans hz.symm)
  obtain ⟨b, hb⟩ := (CyclicClassAlgebra.cyclicClass_eq_zero_iff_of_injective θ' hθ'inj π).1 hclass
  -- (6) the Artin symbol of `π` lies in `H`
  have hnorm : Units.map (FiniteExtension.localNorm v w₁) b = π := hb
  have hArt := artinSymbol_norm_mem hζ hinj v H u b
  rw [hnorm] at hArt
  obtain ⟨σ₀, hσ₀, hσ₀eq⟩ := Subgroup.mem_map.1 hArt
  -- (7) `θ σ₀ = 1`
  have h7 : ψloc σ₀ = (χ' σ₀) ^ k := by
    have h := (MonoidHom.mem_ker).1 hσ₀
    rw [hθ, MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.pow_apply, mul_inv_eq_one] at h
    exact h
  -- (8) `σ₀` restricts to the arithmetic Frobenius of `U`
  have h8 : rU σ₀ = χU.symm (Multiplicative.ofAdd 1) := by
    apply decompositionHom_injective v wU
    rw [hfrob, ← hσ₀eq]
    exact (decompositionHom_restrictNormal v wU u σ₀).symm
  have h9 : χ' σ₀ = Multiplicative.ofAdd 1 := by
    change χU (rU σ₀) = _
    rw [h8, MulEquiv.apply_symm_apply]
  -- (9) conclusion
  have h10 : ψ (artinSymbol hζ hinj v π) = Multiplicative.ofAdd (k : ZMod e) := by
    rw [← hσ₀eq]
    change ψloc σ₀ = _
    rw [h7, h9, ← ofAdd_nsmul, nsmul_eq_mul, mul_one]
  rw [hxk, h10, toAdd_ofAdd, ZMod.val_natCast, Nat.mod_eq_of_lt hk]

include hcomm in
/-- **The local identity.** Under the hypotheses of the θ-trick for every element of order `1`,
the abstract invariant of the local carry class of every `a ∈ F_vˣ` is `ψ(Art a) / e`. -/
theorem relative_cyclicClass (I : InvariantFamily.{u, u} (residuePrime v))
    (hI : I.RelativeClassFormation ∧ I.ArithmeticNormalization)
    (HU : Subgroup (L ≃ₐ[F] L)) [HU.Normal] {e : ℕ} [NeZero e]
    (χU : (((fixedFieldPlace HU u).adicCompletion (IntermediateField.fixedField HU)) ≃ₐ[v.adicCompletion F]
      ((fixedFieldPlace HU u).adicCompletion (IntermediateField.fixedField HU))) ≃*
        Multiplicative (ZMod e))
    (hχU : IsArithmeticUnramifiedCoordinate (padicField v)
      ((fixedFieldPlace HU u).adicCompletion (IntermediateField.fixedField HU)) χU)
    (hfrob : ∀ π : (v.adicCompletion F)ˣ,
      (padicField v).canonicalTopologicalData.ord (π : v.adicCompletion F) = 1 →
      decompositionHom v (fixedFieldPlace HU u) (χU.symm (Multiplicative.ofAdd 1)) =
        (artinSymbol hζ hinj v π).restrictNormal (IntermediateField.fixedField HU))
    (ψ : (L ≃ₐ[F] L) →* Multiplicative (ZMod e)) (a : (v.adicCompletion F)ˣ) :
    haveI := isGalois_adicCompletion v u
    haveI := FiniteExtension.local_finite v u
    I.relative (padicField v) (u.adicCompletion L)
        (cyclicClass (v.adicCompletion F) (u.adicCompletion L) (ψ.comp (decompositionHom v u)) a) =
      rationalClass (((ψ (artinSymbol hζ hinj v a)).toAdd.val : ℚ) / e) := by
  have := isGalois_adicCompletion v u
  have := FiniteExtension.local_finite v u
  set T := (padicField v).canonicalTopologicalData
  -- both sides as additive maps on `Additive F_vˣ`
  let Φ : Additive (v.adicCompletion F)ˣ →+ RationalModIntegers :=
    (I.relative (padicField v) (u.adicCompletion L)).comp
      (CyclicClassAlgebra.cyclicClassHom (ψ.comp (decompositionHom v u)))
  let Ψ : Additive (v.adicCompletion F)ˣ →+ RationalModIntegers :=
    (zmodClass e).comp ((ψ.comp (artinSymbol hζ hinj v)).toAdditive)
  have hΦ : ∀ b, Φ (Additive.ofMul b) = I.relative (padicField v) (u.adicCompletion L)
      (cyclicClass (v.adicCompletion F) (u.adicCompletion L) (ψ.comp (decompositionHom v u)) b) :=
    fun b => rfl
  have hΨ : ∀ b, Ψ (Additive.ofMul b) =
      rationalClass (((ψ (artinSymbol hζ hinj v b)).toAdd.val : ℚ) / e) := fun b => rfl
  have hone : ∀ π : (v.adicCompletion F)ˣ, T.ord (π : v.adicCompletion F) = 1 →
      Φ (Additive.ofMul π) = Ψ (Additive.ofMul π) := fun π hπ => by
    rw [hΦ, hΨ]
    exact relative_cyclicClass_uniformizer hcomm hζ hinj v u I hI HU χU hχU π hπ (hfrob π hπ) ψ
  -- an element of order one
  obtain ⟨x₀, hx₀, hx₀ord⟩ := Langlands.PadicField.TopologicalData.ord_surjective_nonzero T 1
  set π₀ : (v.adicCompletion F)ˣ := Units.mk0 x₀ hx₀
  have hπ₀ : T.ord (π₀ : v.adicCompletion F) = 1 := hx₀ord
  set n := T.ord (a : v.adicCompletion F)
  set c : (v.adicCompletion F)ˣ := a * (π₀ ^ n)⁻¹ * π₀
  have hc : T.ord (c : v.adicCompletion F) = 1 := by
    simp only [c, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val]
    have h0 : ((π₀ : v.adicCompletion F) ^ n)⁻¹ ≠ 0 := inv_ne_zero (zpow_ne_zero n π₀.ne_zero)
    rw [Langlands.PadicField.TopologicalData.ord_mul T (mul_ne_zero a.ne_zero h0) π₀.ne_zero,
      Langlands.PadicField.TopologicalData.ord_mul T a.ne_zero h0,
      Langlands.PadicField.TopologicalData.ord_inv, Langlands.PadicField.TopologicalData.ord_zpow,
      hπ₀]
    ring
  have hac : a = c * π₀ ^ (n - 1) := by
    simp only [c]
    group
  rw [← hΦ, ← hΨ, hac, ofMul_mul, ofMul_zpow, map_add, map_add, map_zsmul, map_zsmul,
    hone c hc, hone π₀ hπ₀]

end Theta

end LocalSymbolIdentity

end Langlands.ClassField.Global
