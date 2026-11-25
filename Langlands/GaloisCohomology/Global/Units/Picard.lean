import Langlands.GaloisCohomology.Global.Units.Divisor

/-!
# The `S`-Picard group and `H¹(G_S, 𝒪_Sˣ)`

The `S`-Picard group `Pic(𝒪_S)` is the group of divisors prime to `S` modulo divisors of units of
`F` (`SPicardGroup`); it is finite and killed by the class number (`finite_sPicardGroup`,
`classNumber_nsmul_sPicardGroup`).

The short exact sequence `0 → 𝒪_Sˣ → K_Sˣ → K_Sˣ/𝒪_Sˣ → 0` of `G_S`-modules
(`sUnitsQuotSequence`) and Hilbert 90 for `K_S / K` give `H¹(G_S, 𝒪_Sˣ)` as the cokernel of
`Fˣ → (K_Sˣ/𝒪_Sˣ)^{G_S}`; the invariants are the classes of `S`-invariant units, and taking their
divisors (`divAbove`) gives an injection `H¹(G_S, 𝒪_Sˣ) → Pic(𝒪_S)`
(`cohomologyOneSUnitsToSPicard_injective`). `S`-units have divisor zero (`divAbove_eq_zero_of_mem`),
so if `x ^ N` is a unit `a` of `F` times an `S`-unit, `N` times the divisor of `x` is the divisor
of `a` (`nsmul_divAbove_eq_sDivisorOf`). Its image contains every class killed by an `N` that is
invertible outside `S` (`exists_cohomologyOneSUnitsToSPicard_eq`), so it is an isomorphism when the
order of `Pic(𝒪_S)` is invertible outside `S` (`cohomologyOneSUnitsEquiv`).
-/

namespace Langlands.GaloisCohomology

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum CategoryTheory
open Langlands.Galois Langlands.ProfiniteCohomology
open scoped NumberField nonZeroDivisors

universe u

noncomputable section

section Picard

variable {F : Type*} [Field F] [NumberField F] (S : Set (HeightOneSpectrum (𝓞 F)))

/-- The `S`-Picard group `Pic(𝒪_S)`: divisors prime to `S` modulo divisors of units of `F`. -/
abbrev SPicardGroup := SDivisor S ⧸ (sDivisorOf S).range

/-- The class of a divisor in `Pic(𝒪_S)`. -/
noncomputable abbrev sPicardMk : SDivisor S →+ SPicardGroup S := QuotientAddGroup.mk' (sDivisorOf S).range

/-- A divisor has trivial class exactly when it is the divisor of a unit. -/
theorem sPicardMk_eq_zero_iff (D : SDivisor S) : sPicardMk S D = 0 ↔ ∃ x : Fˣ, sDivisorOf S (Additive.ofMul x) = D := by
  rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, AddMonoidHom.mem_range]
  exact ⟨fun ⟨x, hx⟩ => ⟨Additive.toMul x, hx⟩, fun ⟨x, hx⟩ => ⟨Additive.ofMul x, hx⟩⟩

end Picard

section Finite

variable {F : Type*} [Field F] [NumberField F]

/-- A nonzero integer of `F` as a unit of `F`. -/
noncomputable def integerUnit {a : 𝓞 F} (ha : a ≠ 0) : Fˣ :=
  Units.mk0 (algebraMap (𝓞 F) F a) (by
    rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)]
    exact ha)

/-- `integerUnit` is the integer. -/
theorem coe_integerUnit {a : 𝓞 F} (ha : a ≠ 0) : (integerUnit ha : F) = algebraMap (𝓞 F) F a :=
  rfl

/-- `integerUnit` is multiplicative. -/
theorem integerUnit_mul {a b : 𝓞 F} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a * b ≠ 0) :
    integerUnit hab = integerUnit ha * integerUnit hb :=
  Units.ext (by simp [coe_integerUnit])

/-- `integerUnit` commutes with powers. -/
theorem integerUnit_pow {a : 𝓞 F} (ha : a ≠ 0) (k : ℕ) (hak : a ^ k ≠ 0) :
    integerUnit hak = integerUnit ha ^ k :=
  Units.ext (by simp [coe_integerUnit])

/-- `ord_v(xᵏ) = k ord_v(x)`. -/
theorem ordAt_pow (v : HeightOneSpectrum (𝓞 F)) (x : Fˣ) (k : ℕ) :
    ordAt v (x ^ k) = k * ordAt v x := by
  simp only [ordAt, map_pow, toAdd_pow, nsmul_eq_mul]
  ring

/-- Associated integers have the same orders. -/
theorem ordAt_integerUnit_eq_of_associated {a b : 𝓞 F} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : Associated a b) (w : HeightOneSpectrum (𝓞 F)) :
    ordAt w (integerUnit ha) = ordAt w (integerUnit hb) := by
  obtain ⟨u, rfl⟩ := h
  have hu : integerUnit hb = integerUnit ha * Units.map (algebraMap (𝓞 F) F : 𝓞 F →* F) u :=
    Units.ext (by simp [coe_integerUnit])
  rw [hu, ordAt_mul]
  simp [ordAt, valuation_of_unit_eq]

open scoped Classical in

/-- The orders of `placeUnit v`: `h_F` at `v`, `0` elsewhere. -/
theorem ordAt_placeUnit (v w : HeightOneSpectrum (𝓞 F)) :
    ordAt w (placeUnit v) = if w = v then (classNumber F : ℤ) else 0 := by
  rw [ordAt, valuationOfNeZero_placeUnit]
  split_ifs <;> simp

/-- `placeUnit v` as an `integerUnit`. -/
theorem placeUnit_eq_integerUnit (v : HeightOneSpectrum (𝓞 F)) :
    placeUnit v =
      integerUnit (exists_pow_classNumber_eq_span v).choose_spec.1 :=
  Units.ext rfl

/-- The prime of `v` as a nonzero ideal. -/
def primeNonZeroDivisor (v : HeightOneSpectrum (𝓞 F)) : (Ideal (𝓞 F))⁰ :=
  ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩

open scoped Classical in

/-- Two primes with the same ideal class differ by a principal fractional ideal. -/
theorem exists_ordAt_eq_of_mk0_eq {v p : HeightOneSpectrum (𝓞 F)}
    (h : ClassGroup.mk0 (primeNonZeroDivisor v) = ClassGroup.mk0 (primeNonZeroDivisor p)) :
    ∃ x : Fˣ, ∀ w, ordAt w x = (if w = v then 1 else 0) - (if w = p then 1 else 0) := by
  obtain ⟨a, b, ha, hb, hab⟩ := ClassGroup.mk0_eq_mk0_iff.1 h
  change Ideal.span {a} * v.asIdeal = Ideal.span {b} * p.asIdeal at hab
  set hF := classNumber F with hhF
  have hv := exists_pow_classNumber_eq_span v
  have hp := exists_pow_classNumber_eq_span p
  set πv := hv.choose
  set πp := hp.choose
  have hπv : πv ≠ 0 := hv.choose_spec.1
  have hπp : πp ≠ 0 := hp.choose_spec.1
  have hav : a ^ hF * πv ≠ 0 := mul_ne_zero (pow_ne_zero _ ha) hπv
  have hbp : b ^ hF * πp ≠ 0 := mul_ne_zero (pow_ne_zero _ hb) hπp
  have hspan : Ideal.span {a ^ hF * πv} = Ideal.span {b ^ hF * πp} := by
    have := congrArg (· ^ hF) hab
    simp only [mul_pow, Ideal.span_singleton_pow] at this
    rw [hv.choose_spec.2, hp.choose_spec.2, Ideal.span_singleton_mul_span_singleton,
      Ideal.span_singleton_mul_span_singleton] at this
    exact this
  have hassoc := Ideal.span_singleton_eq_span_singleton.1 hspan
  refine ⟨integerUnit hb * (integerUnit ha)⁻¹, fun w => ?_⟩
  have key := ordAt_integerUnit_eq_of_associated hav hbp hassoc w
  rw [integerUnit_mul (pow_ne_zero _ ha) hπv hav, integerUnit_mul (pow_ne_zero _ hb) hπp hbp,
    integerUnit_pow ha hF (pow_ne_zero _ ha), integerUnit_pow hb hF (pow_ne_zero _ hb),
    ordAt_mul, ordAt_mul, ordAt_pow, ordAt_pow] at key
  have hv' : ordAt w (integerUnit hπv) = if w = v then (hF : ℤ) else 0 := by
    rw [← ordAt_placeUnit v w, placeUnit_eq_integerUnit]
  have hp' : ordAt w (integerUnit hπp) = if w = p then (hF : ℤ) else 0 := by
    rw [← ordAt_placeUnit p w, placeUnit_eq_integerUnit]
  rw [hv', hp'] at key
  have hh : (hF : ℤ) ≠ 0 := by exact_mod_cast classNumber_ne_zero F
  rw [ordAt_mul, ordAt_inv]
  apply mul_left_cancel₀ hh
  split_ifs at key ⊢ <;> linarith

variable (S : Set (HeightOneSpectrum (𝓞 F)))

/-- The divisor of `placeUnit v` is `h_F • v`. -/
theorem sDivisorOf_placeUnit (v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}) :
    sDivisorOf S (Additive.ofMul (placeUnit v.1)) =
      (classNumber F : ℤ) • Finsupp.single v 1 := by
  classical
  ext w
  rw [sDivisorOf_apply, toMul_ofMul, ordAt_placeUnit, Finsupp.smul_apply, Finsupp.single_apply]
  by_cases h : w = v
  · subst h
    simp
  · have h' : w.1 ≠ v.1 := fun e => h (Subtype.ext e)
    simp [h', Ne.symm h]

/-- `Pic(𝒪_S)` is killed by the class number of `F`. -/
theorem classNumber_nsmul_sPicardGroup (c : SPicardGroup S) : classNumber F • c = 0 := by
  obtain ⟨D, rfl⟩ := QuotientAddGroup.mk'_surjective (sDivisorOf S).range c
  rw [← map_nsmul]
  refine (QuotientAddGroup.eq_zero_iff _).2 ?_
  induction D using Finsupp.induction_linear with
  | zero => rw [smul_zero]; exact zero_mem _
  | add f g hf hg => rw [smul_add]; exact add_mem hf hg
  | single v m =>
    refine ⟨m • Additive.ofMul (placeUnit v.1), ?_⟩
    rw [map_zsmul, sDivisorOf_placeUnit]
    ext w
    by_cases hw : v = w <;> simp [hw]
    ring

open scoped Classical in

/-- The image in `Pic(𝒪_S)` of an ideal class of `F`. -/
noncomputable def sPicardGen (c : ClassGroup (𝓞 F)) : SPicardGroup S :=
  if h : ∃ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, ClassGroup.mk0 (primeNonZeroDivisor v.1) = c then
    sPicardMk S (Finsupp.single h.choose 1)
  else 0

/-- The class of a prime `v ∉ S` in `Pic(𝒪_S)` is the image of its ideal class. -/
theorem sPicardMk_single_eq_sPicardGen (v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}) :
    sPicardMk S (Finsupp.single v 1) = sPicardGen S (ClassGroup.mk0 (primeNonZeroDivisor v.1)) := by
  classical
  have hex : ∃ u : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
      ClassGroup.mk0 (primeNonZeroDivisor u.1) = ClassGroup.mk0 (primeNonZeroDivisor v.1) := ⟨v, rfl⟩
  rw [sPicardGen, dite_eq_left hex]
  obtain ⟨x, hx⟩ := exists_ordAt_eq_of_mk0_eq hex.choose_spec.symm
  rw [← sub_eq_zero, ← map_sub]
  refine (QuotientAddGroup.eq_zero_iff _).2 ⟨Additive.ofMul x, ?_⟩
  ext w
  rw [sDivisorOf_apply, toMul_ofMul, hx, Finsupp.sub_apply, Finsupp.single_apply, Finsupp.single_apply]
  have e1 : (w.1 = v.1) ↔ (v = w) := ⟨fun e => (Subtype.ext e).symm, fun e => by rw [e]⟩
  have e2 : (w.1 = hex.choose.1) ↔ (hex.choose = w) := ⟨fun e => (Subtype.ext e).symm, fun e => by rw [e]⟩
  simp only [e1, e2]

/-- `Pic(𝒪_S)` is generated by the images of the ideal classes. -/
theorem closure_range_sPicardGen : AddSubgroup.closure (Set.range (sPicardGen S)) = ⊤ := by
  rw [eq_top_iff]
  rintro c -
  obtain ⟨D, rfl⟩ := QuotientAddGroup.mk'_surjective (sDivisorOf S).range c
  induction D using Finsupp.induction_linear with
  | zero => rw [map_zero]; exact zero_mem _
  | add f g hf hg => rw [map_add]; exact add_mem hf hg
  | single v m =>
    rw [← Finsupp.smul_single_one, map_zsmul]
    refine AddSubgroup.zsmul_mem _ ?_ m
    change sPicardMk S (Finsupp.single v 1) ∈ _
    rw [sPicardMk_single_eq_sPicardGen]
    exact AddSubgroup.subset_closure ⟨_, rfl⟩

/-- `Pic(𝒪_S)` is finite. -/
instance finite_sPicardGroup : Finite (SPicardGroup S) := by
  have : AddGroup.FG (SPicardGroup S) :=
    AddGroup.fg_iff.2 ⟨_, closure_range_sPicardGen S, Set.finite_range _⟩
  refine AddCommGroup.finite_of_fg_isAddTorsion _ fun c => ?_
  exact isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨classNumber F, classNumber_pos F,
    classNumber_nsmul_sPicardGroup S c⟩

end Finite

section Quot

variable (F Ω : Type u) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
variable (S : Set (HeightOneSpectrum (𝓞 F)))

/-- The `S`-units of `K_S` as a submodule of the units module. -/
def sUnitsSubmodule : Submodule (ULift.{u} ℤ) (unitsModule F (maximalUnramifiedOutside F Ω S)) where
  carrier := {z | Additive.toMul (α := (maximalUnramifiedOutside F Ω S)ˣ) z ∈ maximalSUnits F Ω S}
  add_mem' {a b} ha hb := by
    change Additive.toMul (α := (maximalUnramifiedOutside F Ω S)ˣ) a *
      Additive.toMul (α := (maximalUnramifiedOutside F Ω S)ˣ) b ∈ maximalSUnits F Ω S
    exact mul_mem ha hb
  zero_mem' := by
    change (1 : (maximalUnramifiedOutside F Ω S)ˣ) ∈ maximalSUnits F Ω S
    exact one_mem _
  smul_mem' r z hz := by
    change Additive.toMul (α := (maximalUnramifiedOutside F Ω S)ˣ)
      (r.down • (show Additive (maximalUnramifiedOutside F Ω S)ˣ from z)) ∈ maximalSUnits F Ω S
    rw [toMul_zsmul]
    exact zpow_mem hz _

/-- The Galois action preserves the `S`-units. -/
theorem sUnitsSubmodule_le_comap (σ : GaloisGroupUnramifiedOutside F Ω S) :
    sUnitsSubmodule F Ω S ≤ (sUnitsSubmodule F Ω S).comap
      ((unitsModule F (maximalUnramifiedOutside F Ω S)).ρ σ) :=
  fun _ hz => galUnitsHom_mem_sUnitsOf (S := S) σ hz

/-- `K_Sˣ / 𝒪_Sˣ` as a `G_S`-module. -/
noncomputable abbrev unitsModSUnitsModule : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside F Ω S) :=
  (unitsModule F (maximalUnramifiedOutside F Ω S)).quotient (sUnitsSubmodule F Ω S)
    (sUnitsSubmodule_le_comap F Ω S)

/-- The short complex `0 → 𝒪_Sˣ → K_Sˣ → K_Sˣ/𝒪_Sˣ → 0`. -/
noncomputable def sUnitsQuotSequence :
    ShortComplex (Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside F Ω S)) :=
  ShortComplex.mk (sUnitsToUnits S (maximalUnramifiedOutside F Ω S))
    (Rep.mkQ _ (sUnitsSubmodule F Ω S) (sUnitsSubmodule_le_comap F Ω S)) (by
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro x
      exact (Submodule.Quotient.mk_eq_zero _).2
        (show Additive.toMul (α := (maximalUnramifiedOutside F Ω S)ˣ) _ ∈ maximalSUnits F Ω S from
          (Additive.toMul x).2))

/-- `0 → 𝒪_Sˣ → K_Sˣ → K_Sˣ/𝒪_Sˣ → 0` is exact. -/
theorem sUnitsQuotSequence_shortExact : (sUnitsQuotSequence F Ω S).ShortExact where
  exact := by
    apply shortComplex_exact_of_forall_exists
    intro x hx
    exact ⟨Additive.ofMul ⟨Additive.toMul (α := (maximalUnramifiedOutside F Ω S)ˣ) x,
      (Submodule.Quotient.mk_eq_zero _).1 hx⟩, rfl⟩
  mono_f := (Rep.mono_iff_injective _).2 (sUnitsToUnits_injective S _)
  epi_g := (Rep.epi_iff_surjective _).2 (Submodule.mkQ_surjective _)

variable [IsGalois F Ω]

/-- Smoothness of the terms of `sUnitsQuotSequence`. -/
instance isSmoothRep_sUnitsQuotSequence_X₁ : IsSmoothRep (sUnitsQuotSequence F Ω S).X₁ :=
  inferInstanceAs (IsSmoothRep (sUnitsModule S (maximalUnramifiedOutside F Ω S)))

/-- Smoothness of the terms of `sUnitsQuotSequence`. -/
instance isSmoothRep_sUnitsQuotSequence_X₂ : IsSmoothRep (sUnitsQuotSequence F Ω S).X₂ :=
  inferInstanceAs (IsSmoothRep (unitsModule F (maximalUnramifiedOutside F Ω S)))

/-- Smoothness of the terms of `sUnitsQuotSequence`. -/
instance isSmoothRep_sUnitsQuotSequence_X₃ : IsSmoothRep (sUnitsQuotSequence F Ω S).X₃ :=
  isSmoothRep_quotient _ _ _

end Quot

section Phi

variable {F Ω : Type u} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]
variable (S : Set (HeightOneSpectrum (𝓞 F)))

omit [IsGalois F Ω] in
/-- The class of a unit in `K_Sˣ/𝒪_Sˣ` is invariant exactly when the unit is `S`-invariant. -/
theorem mk_mem_invariants_iff (x : (maximalUnramifiedOutside F Ω S)ˣ) :
    (Rep.mkQ _ (sUnitsSubmodule F Ω S) (sUnitsSubmodule_le_comap F Ω S)).hom
        (Additive.ofMul x : Additive (maximalUnramifiedOutside F Ω S)ˣ) ∈
      (unitsModSUnitsModule F Ω S).ρ.invariants ↔ IsSInvariant S x :=
  forall_congr' fun _ => (Submodule.Quotient.eq _).trans Iff.rfl

/-- `S`-invariant units map onto the invariants of `K_Sˣ/𝒪_Sˣ`. -/
noncomputable def sInvariantToInvariants :
    Additive (sInvariantSubgroup Ω S) →+ (unitsModSUnitsModule F Ω S).ρ.invariants where
  toFun x := ⟨(Rep.mkQ _ (sUnitsSubmodule F Ω S) (sUnitsSubmodule_le_comap F Ω S)).hom
      (Additive.ofMul (Additive.toMul x : sInvariantSubgroup Ω S).1 :
        Additive (maximalUnramifiedOutside F Ω S)ˣ),
    (mk_mem_invariants_iff S _).2 (Additive.toMul x).2⟩
  map_zero' := rfl
  map_add' _ _ := rfl

omit [IsGalois F Ω] in
/-- `sInvariantToInvariants` is surjective. -/
theorem sInvariantToInvariants_surjective : Function.Surjective (sInvariantToInvariants (Ω := Ω) S) := by
  rintro ⟨q, hq⟩
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  exact ⟨Additive.ofMul ⟨Additive.toMul (α := (maximalUnramifiedOutside F Ω S)ˣ) z,
    (mk_mem_invariants_iff S _).1 hq⟩, rfl⟩

omit [IsGalois F Ω] in
/-- The kernel of `sInvariantToInvariants` is the `S`-units. -/
theorem sInvariantToInvariants_eq_zero_iff (x : Additive (sInvariantSubgroup Ω S)) :
    sInvariantToInvariants (Ω := Ω) S x = 0 ↔
      ((Additive.toMul x : sInvariantSubgroup Ω S) : (maximalUnramifiedOutside F Ω S)ˣ) ∈ maximalSUnits F Ω S := by
  rw [Subtype.ext_iff]
  exact Submodule.Quotient.mk_eq_zero _

/-- `S`-units have divisor zero. -/
theorem divAbove_eq_zero_of_mem {x : sInvariantSubgroup Ω S}
    (hx : (x : (maximalUnramifiedOutside F Ω S)ˣ) ∈ maximalSUnits F Ω S) :
    divAbove S (Additive.ofMul x) = 0 := by
  ext v
  rw [divAbove_apply, Finsupp.coe_zero, Pi.zero_apply]
  obtain ⟨L, hf, hL, y, hy, hyx⟩ := exists_of_mem_maximalSUnits F Ω S hx
  have := NumberField.of_module_finite F L
  have hyL : (((x : (maximalUnramifiedOutside F Ω S)ˣ) : maximalUnramifiedOutside F Ω S) : Ω) ∈ L := by
    rw [← hyx]
    exact (y : L).2
  obtain ⟨w, hw⟩ := exists_under_eq (L := L) v.1
  have h1 := valuation_eq_exp_ordAbove S x.2 hL hyL w (hw ▸ v.2)
  have hyy : (⟨_, hyL⟩ : L) = (y : L) :=
    Subtype.ext (congrArg (fun u : (maximalUnramifiedOutside F Ω S)ˣ =>
      ((u : maximalUnramifiedOutside F Ω S) : Ω)) hyx).symm
  have h2 := (mem_sUnitsOf_iff_mem_unit S).1 hy w (fun h => (hw ▸ v.2) (mem_finitePlacesAbove_iff_under.1 h))
  rw [hyy, h2, hw] at h1
  have := congrArg WithZero.log h1
  simp only [WithZero.log_one, WithZero.log_exp] at this
  simp only [toMul_ofMul]
  omega

/-- The divisor class of an invariant of `K_Sˣ/𝒪_Sˣ`. -/
noncomputable def invariantsToSPicard : (unitsModSUnitsModule F Ω S).ρ.invariants →+ SPicardGroup S :=
  (QuotientAddGroup.lift (sInvariantToInvariants (Ω := Ω) S).ker ((sPicardMk S).comp (divAbove S))
    (fun x hx => by
      rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply]
      have := divAbove_eq_zero_of_mem S
        ((sInvariantToInvariants_eq_zero_iff S x).1 (AddMonoidHom.mem_ker.1 hx))
      rw [ofMul_toMul] at this
      rw [this, map_zero])).comp
    (QuotientAddGroup.quotientKerEquivOfSurjective _
      (sInvariantToInvariants_surjective (Ω := Ω) S)).symm.toAddMonoidHom

/-- `invariantsToSPicard` on the class of an `S`-invariant unit. -/
theorem invariantsToSPicard_apply (x : Additive (sInvariantSubgroup Ω S)) :
    invariantsToSPicard (Ω := Ω) S (sInvariantToInvariants (Ω := Ω) S x) = sPicardMk S (divAbove S x) := by
  have h : (QuotientAddGroup.quotientKerEquivOfSurjective _
      (sInvariantToInvariants_surjective (Ω := Ω) S)).symm (sInvariantToInvariants (Ω := Ω) S x) =
      (x : Additive (sInvariantSubgroup Ω S) ⧸ (sInvariantToInvariants (Ω := Ω) S).ker) :=
    (AddEquiv.symm_apply_eq _).2 rfl
  simp only [invariantsToSPicard, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, h]
  rfl

/-- The connecting map `(K_Sˣ/𝒪_Sˣ)^{G_S} → H¹(G_S, 𝒪_Sˣ)`. -/
noncomputable def invariantsToCohomologyOne :
    (unitsModSUnitsModule F Ω S).ρ.invariants →+ cohomology (sUnitsModule S (maximalUnramifiedOutside F Ω S)) 1 :=
  (δ (sUnitsQuotSequence_shortExact F Ω S) 0 1 rfl).hom.toAddMonoidHom.comp
    (zeroIso (sUnitsQuotSequence F Ω S).X₃).inv.hom.toAddMonoidHom

/-- The connecting map is onto, by Hilbert 90 for `K_S`. -/
theorem invariantsToCohomologyOne_surjective : Function.Surjective (invariantsToCohomologyOne (Ω := Ω) S) := fun x =>
  exists_δ_zeroIso_inv_eq (sUnitsQuotSequence_shortExact F Ω S)
    (subsingleton_cohomology_one_unitsModule (K := F) (L := maximalUnramifiedOutside F Ω S)) x

/-- The kernel of the connecting map is the image of `Fˣ`. -/
theorem invariantsToCohomologyOne_eq_zero_iff (q : (unitsModSUnitsModule F Ω S).ρ.invariants) :
    invariantsToCohomologyOne (Ω := Ω) S q = 0 ↔ ∃ a : Fˣ,
      sInvariantToInvariants (Ω := Ω) S (Additive.ofMul ⟨_, map_algebraMap_mem_sInvariantSubgroup (Ω := Ω) S a⟩) = q := by
  refine (δ_zeroIso_inv_eq_zero_iff (sUnitsQuotSequence_shortExact F Ω S) q).trans ?_
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨a, rfl⟩ := unitsToInvariants_surjective F (maximalUnramifiedOutside F Ω S) w
    exact ⟨Additive.toMul a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨unitsToInvariants F (maximalUnramifiedOutside F Ω S) (Additive.ofMul a), rfl⟩

end Phi

section Power

variable {F Ω : Type u} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
variable (S : Set (HeightOneSpectrum (𝓞 F))) [IsGalois F Ω]

/-- If `x ^ N` is a unit `a` of `F` times an `S`-unit, then `N` times the divisor of `x` is the
divisor of `a`. -/
theorem nsmul_divAbove_eq_sDivisorOf {N : ℕ} (x : sInvariantSubgroup Ω S) (a : Fˣ)
    {y : (maximalUnramifiedOutside F Ω S)ˣ} (hy : y ∈ maximalSUnits F Ω S)
    (h : (x : (maximalUnramifiedOutside F Ω S)ˣ) ^ N =
      Units.map (algebraMap F (maximalUnramifiedOutside F Ω S) : F →* _) a * y) :
    N • divAbove S (Additive.ofMul x) = sDivisorOf S (Additive.ofMul a) := by
  let A : sInvariantSubgroup Ω S := ⟨_, map_algebraMap_mem_sInvariantSubgroup (Ω := Ω) S a⟩
  let Y : sInvariantSubgroup Ω S := ⟨y, isSInvariant_of_mem_maximalSUnits S hy⟩
  have hxAY : x ^ N = A * Y := Subtype.ext h
  have hY : divAbove S (Additive.ofMul Y) = 0 := divAbove_eq_zero_of_mem S hy
  rw [← map_nsmul, ← ofMul_pow, hxAY, ofMul_mul, map_add, hY, add_zero]
  exact divAbove_algebraMap S a

end Power

section H1

variable {F Ω : Type u} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]
variable (S : Set (HeightOneSpectrum (𝓞 F)))

/-- The injection `H¹(G_S, 𝒪_Sˣ) → Pic(𝒪_S)`. -/
noncomputable def cohomologyOneSUnitsToSPicard :
    cohomology (sUnitsModule S (maximalUnramifiedOutside F Ω S)) 1 →+ SPicardGroup S :=
  (QuotientAddGroup.lift (invariantsToCohomologyOne (Ω := Ω) S).ker (invariantsToSPicard (Ω := Ω) S) (fun q hq => by
      obtain ⟨a, rfl⟩ := (invariantsToCohomologyOne_eq_zero_iff S q).1 (AddMonoidHom.mem_ker.1 hq)
      rw [AddMonoidHom.mem_ker, invariantsToSPicard_apply, divAbove_algebraMap]
      exact (sPicardMk_eq_zero_iff S _).2 ⟨a, rfl⟩)).comp
    (QuotientAddGroup.quotientKerEquivOfSurjective _
      (invariantsToCohomologyOne_surjective (Ω := Ω) S)).symm.toAddMonoidHom

/-- `cohomologyOneSUnitsToSPicard` after the connecting map is `invariantsToSPicard`. -/
theorem cohomologyOneSUnitsToSPicard_invariantsToCohomologyOne (q : (unitsModSUnitsModule F Ω S).ρ.invariants) :
    cohomologyOneSUnitsToSPicard (Ω := Ω) S (invariantsToCohomologyOne (Ω := Ω) S q) = invariantsToSPicard (Ω := Ω) S q := by
  have h : (QuotientAddGroup.quotientKerEquivOfSurjective _
      (invariantsToCohomologyOne_surjective (Ω := Ω) S)).symm (invariantsToCohomologyOne (Ω := Ω) S q) =
      (q : (unitsModSUnitsModule F Ω S).ρ.invariants ⧸ (invariantsToCohomologyOne (Ω := Ω) S).ker) :=
    (AddEquiv.symm_apply_eq _).2 rfl
  simp only [cohomologyOneSUnitsToSPicard, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, h]
  rfl

/-- `cohomologyOneSUnitsToSPicard` on the class of an `S`-invariant unit is its divisor class. -/
theorem cohomologyOneSUnitsToSPicard_apply (x : Additive (sInvariantSubgroup Ω S)) :
    cohomologyOneSUnitsToSPicard (Ω := Ω) S (invariantsToCohomologyOne (Ω := Ω) S (sInvariantToInvariants (Ω := Ω) S x)) = sPicardMk S (divAbove S x) := by
  rw [cohomologyOneSUnitsToSPicard_invariantsToCohomologyOne, invariantsToSPicard_apply]

/-- `H¹(G_S, 𝒪_Sˣ) → Pic(𝒪_S)` is injective. -/
theorem cohomologyOneSUnitsToSPicard_injective : Function.Injective (cohomologyOneSUnitsToSPicard (Ω := Ω) S) := by
  refine (injective_iff_map_eq_zero _).2 fun h hh => ?_
  obtain ⟨q, rfl⟩ := invariantsToCohomologyOne_surjective (Ω := Ω) S h
  obtain ⟨x, rfl⟩ := sInvariantToInvariants_surjective (Ω := Ω) S q
  rw [cohomologyOneSUnitsToSPicard_apply, sPicardMk_eq_zero_iff] at hh
  obtain ⟨a, ha⟩ := hh
  let y : Additive (sInvariantSubgroup Ω S) :=
    Additive.ofMul ⟨_, map_algebraMap_mem_sInvariantSubgroup (Ω := Ω) S a⟩
  have hxy : divAbove S (x - y) = 0 := by
    rw [map_sub, divAbove_algebraMap, ha, sub_self]
  have hmem := mem_maximalSUnits_of_divAbove_eq_zero S (x := Additive.toMul (x - y)) hxy
  have h0 : sInvariantToInvariants (Ω := Ω) S (x - y) = 0 := (sInvariantToInvariants_eq_zero_iff S _).2 hmem
  rw [map_sub, sub_eq_zero] at h0
  rw [h0]
  exact (invariantsToCohomologyOne_eq_zero_iff S _).2 ⟨a, rfl⟩

variable [IsSepClosed Ω]

/-- Every class of `Pic(𝒪_S)` killed by an `N` invertible outside `S` is in the image. -/
theorem exists_cohomologyOneSUnitsToSPicard_eq {N : ℕ} (hN : N ≠ 0)
    (hNS : ∀ v ∉ S, ((N : ℕ) : 𝓞 F) ∉ v.asIdeal) (c : SPicardGroup S) (hc : N • c = 0) :
    ∃ h, cohomologyOneSUnitsToSPicard (Ω := Ω) S h = c := by
  obtain ⟨D, rfl⟩ := QuotientAddGroup.mk'_surjective _ c
  rw [← map_nsmul, sPicardMk_eq_zero_iff] at hc
  obtain ⟨a, ha⟩ := hc
  obtain ⟨x, hx⟩ := exists_divAbove_eq (Ω := Ω) S hN hNS D a ha
  exact ⟨invariantsToCohomologyOne (Ω := Ω) S (sInvariantToInvariants (Ω := Ω) S (Additive.ofMul x)),
    by rw [cohomologyOneSUnitsToSPicard_apply, hx]⟩

/-- The same for classes killed by a power of an `n` invertible outside `S`. -/
theorem exists_cohomologyOneSUnitsToSPicard_eq_of_pow {n : ℕ} (hn : n ≠ 0)
    (hnS : ∀ v ∉ S, ((n : ℕ) : 𝓞 F) ∉ v.asIdeal) (c : SPicardGroup S) (k : ℕ) (hc : n ^ k • c = 0) :
    ∃ h, cohomologyOneSUnitsToSPicard (Ω := Ω) S h = c := by
  refine exists_cohomologyOneSUnitsToSPicard_eq S (pow_ne_zero k hn) (fun v hv h => hnS v hv ?_) c hc
  rw [Nat.cast_pow] at h
  exact v.isPrime.mem_of_pow_mem k h

/-- **`H¹(G_S, 𝒪_Sˣ) = Pic(𝒪_S)`** when the order of `Pic(𝒪_S)` is invertible outside `S`: the
injection `cohomologyOneSUnitsToSPicard` is onto. (Without the hypothesis the injection is still onto, by
the principal ideal theorem: `cohomologyOneSUnitsPicardEquiv` of the module
`Langlands.GaloisCohomology.Global.Units.PicardCapitulation`.) -/
noncomputable def cohomologyOneSUnitsEquiv
    (hS : ∀ v ∉ S, ((Nat.card (SPicardGroup S) : ℕ) : 𝓞 F) ∉ v.asIdeal) :
    cohomology (maximalSUnitsModule F Ω S) 1 ≃+ SPicardGroup S :=
  AddEquiv.ofBijective (cohomologyOneSUnitsToSPicard (Ω := Ω) S)
    ⟨cohomologyOneSUnitsToSPicard_injective S, fun c =>
      exists_cohomologyOneSUnitsToSPicard_eq S Nat.card_pos.ne' hS c (card_nsmul_eq_zero')⟩

/-- `cohomologyOneSUnitsEquiv` is `cohomologyOneSUnitsToSPicard`. -/
theorem cohomologyOneSUnitsEquiv_apply
    (hS : ∀ v ∉ S, ((Nat.card (SPicardGroup S) : ℕ) : 𝓞 F) ∉ v.asIdeal)
    (x : cohomology (maximalSUnitsModule F Ω S) 1) :
    cohomologyOneSUnitsEquiv (Ω := Ω) S hS x = cohomologyOneSUnitsToSPicard (Ω := Ω) S x :=
  rfl

end H1

end

end Langlands.GaloisCohomology
