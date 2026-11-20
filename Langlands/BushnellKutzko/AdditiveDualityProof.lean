import Langlands.BushnellKutzko.AdditiveDualityStatement
import Langlands.BushnellKutzko.CorestrictionLatticeDual
import Langlands.BushnellKutzko.RadicalFiltrationProof
import Langlands.BushnellKutzko.UnitFiltrationQuotient

/-! # Proof of additive duality for the hereditary-order filtration -/

noncomputable section

open ValuativeRel
open scoped Pointwise

namespace Langlands.BushnellKutzko

universe u v

section LocalField

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

private theorem mem_maximalIdealInField_iff_valuation_lt_one {x : F} :
    x ∈ maximalIdealInField 𝒪[F] F ↔ valuation F x < 1 := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (valuation F).mem_maximalIdeal_iff.mp ha
  · intro hx
    let a : 𝒪[F] := ⟨x, hx.le⟩
    exact ⟨a, (valuation F).mem_maximalIdeal_iff.mpr hx, rfl⟩

private theorem mem_maximalIdealInField_iff_annihilates_integers (ψF : AddChar F ℂ)
    (htriv : ∀ a ∈ 𝓂[F], ψF (a : F) = 1) (hnontriv : ∃ a : 𝒪[F], ψF (a : F) ≠ 1)
    (x : F) : x ∈ maximalIdealInField 𝒪[F] F ↔ ∀ a : 𝒪[F], ψF ((a : F) * x) = 1 := by
  constructor
  · rintro ⟨x, hx, rfl⟩ a
    exact htriv (a * x) (Ideal.mul_mem_left _ _ hx)
  · intro h
    rw [mem_maximalIdealInField_iff_valuation_lt_one]
    by_contra! hx
    obtain ⟨s, hs⟩ := hnontriv
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hx
    have hdiv : valuation F ((s : F) / x) ≤ 1 := by
      have hvx : 0 < valuation F x := zero_lt_one.trans_le hx
      rw [map_div₀, div_le_one₀ hvx]
      exact s.property.trans hx
    exact hs (by simpa only [div_mul_cancel₀ _ hx0] using h ⟨(s : F) / x, hdiv⟩)

variable {V : Type v} [AddCommGroup V] [Module F V] (𝓛 : LatticeChain 𝒪[F] F V)

private theorem mem_endFiltration_iff_character (ψF : AddChar F ℂ)
    (htriv : ∀ a ∈ 𝓂[F], ψF (a : F) = 1) (hnontriv : ∃ a : 𝒪[F], ψF (a : F) ≠ 1)
    (n : ℤ) (b : Module.End F V) :
    b ∈ 𝓛.endFiltration (1 - n) ↔
      ∀ x ∈ 𝓛.endFiltration n, traceCharacter ψF (b * x) = 1 := by
  have := 𝓛.finiteDimensional
  rw [𝓛.mem_endFiltration_iff_trace_mul]
  constructor
  · intro h x hx
    simpa [traceCharacter_apply] using
      (mem_maximalIdealInField_iff_annihilates_integers ψF htriv hnontriv _).mp (h x hx) 1
  · intro h x hx
    apply (mem_maximalIdealInField_iff_annihilates_integers ψF htriv hnontriv _).mpr
    intro a
    have ha := h (a • x) (Submodule.smul_mem _ a hx)
    change traceCharacter ψF (b * ((a : F) • x)) = 1 at ha
    simpa only [traceCharacter_apply, mul_smul_comm, map_smul, smul_eq_mul] using ha

/-! ## Finite additive quotients of filtration steps -/

private abbrev relativeEndFiltration (i j : ℤ) : Submodule 𝒪[F] (𝓛.endFiltration i) :=
  (𝓛.endFiltration j).comap (𝓛.endFiltration i).subtype

private abbrev endFiltrationQuotient (i j : ℤ) :=
  (𝓛.endFiltration i) ⧸ relativeEndFiltration 𝓛 i j

private theorem finite_endFiltrationQuotient (i j : ℤ) (hij : i ≤ j) :
    Finite (endFiltrationQuotient 𝓛 i j) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  have hshift (a : ℤ) : 𝓂[F] • 𝓛.endFiltration a = 𝓛.endFiltration (a + 𝓛.period) := by
    rw [hπ.maximalIdeal_eq, Submodule.ideal_span_singleton_smul,
      𝓛.endFiltration_add_period_eq_smul hπ]
  have hpow (k : ℕ) : 𝓂[F] ^ k • 𝓛.endFiltration i =
      𝓛.endFiltration (i + (k : ℤ) * 𝓛.period) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Submodule.mul_smul, ih, hshift]
      congr 1
      push_cast
      ring
  let k := (j - i).toNat
  let I : Ideal 𝒪[F] := 𝓂[F] ^ k
  have hI : I • 𝓛.endFiltration i ≤ 𝓛.endFiltration j := by
    change 𝓂[F] ^ k • 𝓛.endFiltration i ≤ _
    rw [hpow]
    apply 𝓛.endFiltration_antitone
    have hk : (k : ℤ) = j - i := Int.toNat_of_nonneg (by omega)
    have hle : (k : ℤ) * 1 ≤ (k : ℤ) * 𝓛.period :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast 𝓛.period_pos) (Int.natCast_nonneg k)
    omega
  have hann : Module.IsTorsionBySet 𝒪[F] (endFiltrationQuotient 𝓛 i j) (I : Set 𝒪[F]) :=
    (Module.isTorsionBySet_quotient_iff _ _).mpr fun x a ha =>
      hI (Submodule.smul_mem_smul ha x.property)
  let := hann.module
  have : IsScalarTower 𝒪[F] (𝒪[F] ⧸ I) (endFiltrationQuotient 𝓛 i j) :=
    hann.isScalarTower
  have : Module.Finite 𝒪[F] (𝓛.endFiltration i) :=
    Module.Finite.iff_fg.mpr (𝓛.fg_endFiltration i)
  have : Finite (𝒪[F] ⧸ 𝓂[F]) := inferInstanceAs (Finite 𝓀[F])
  have : Finite (𝒪[F] ⧸ I) := Ideal.finite_quotient_pow (IsNoetherian.noetherian 𝓂[F]) k
  have : Module.Finite (𝒪[F] ⧸ I) (endFiltrationQuotient 𝓛 i j) :=
    Module.Finite.of_restrictScalars_finite 𝒪[F] _ _
  exact Module.finite_of_finite (𝒪[F] ⧸ I)

/-! ## Duality of the finite additive quotients -/

variable (ψF : AddChar F ℂ) (htriv : ∀ a ∈ 𝓂[F], ψF (a : F) = 1)
  (hnontriv : ∃ a : 𝒪[F], ψF (a : F) ≠ 1)

private def endFiltrationCharacter (i j : ℤ) :
    𝓛.endFiltration (1 - j) →+ AddChar (endFiltrationQuotient 𝓛 i j) ℂ where
  toFun b :=
    let ψ := (traceCharacter ψF).compAddMonoidHom
      ((AddMonoidHom.mulLeft (b : Module.End F V)).comp
        (𝓛.endFiltration i).subtype.toAddMonoidHom)
    AddChar.toAddMonoidHomEquiv.symm <|
      QuotientAddGroup.lift (relativeEndFiltration 𝓛 i j).toAddSubgroup ψ.toAddMonoidHom
        (fun x hx => (mem_endFiltration_iff_character 𝓛 ψF htriv hnontriv j b).mp
          b.property x hx)
  map_zero' := by
    ext q : 1
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    change traceCharacter ψF (0 * (x : Module.End F V)) = 1
    rw [zero_mul, AddChar.map_zero_eq_one]
  map_add' b c := by
    ext q : 1
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    change traceCharacter ψF
        (((b : Module.End F V) + (c : Module.End F V)) * (x : Module.End F V)) =
      traceCharacter ψF ((b : Module.End F V) * (x : Module.End F V)) *
        traceCharacter ψF ((c : Module.End F V) * (x : Module.End F V))
    rw [add_mul, AddChar.map_add_eq_mul]

private def endFiltrationQuotientPairing (i j : ℤ) :
    endFiltrationQuotient 𝓛 (1 - j) (1 - i) →+ AddChar (endFiltrationQuotient 𝓛 i j) ℂ :=
  QuotientAddGroup.lift (relativeEndFiltration 𝓛 (1 - j) (1 - i)).toAddSubgroup
    (endFiltrationCharacter 𝓛 ψF htriv hnontriv i j) (by
      intro b hb
      apply AddChar.eq_zero_iff.mpr
      intro q
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      exact (mem_endFiltration_iff_character 𝓛 ψF htriv hnontriv i b).mp hb x x.property)

private theorem endFiltrationQuotientPairing_mk (i j : ℤ)
    (b : 𝓛.endFiltration (1 - j)) (x : 𝓛.endFiltration i) :
    endFiltrationQuotientPairing 𝓛 ψF htriv hnontriv i j
      (Submodule.Quotient.mk b) (Submodule.Quotient.mk x) =
      traceCharacter ψF ((b : Module.End F V) * (x : Module.End F V)) :=
  rfl

private theorem endFiltrationQuotientPairing_injective (i j : ℤ) :
    Function.Injective (endFiltrationQuotientPairing 𝓛 ψF htriv hnontriv i j) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro q hq
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  change (b : Module.End F V) ∈ 𝓛.endFiltration (1 - i)
  apply (mem_endFiltration_iff_character 𝓛 ψF htriv hnontriv i b).mpr
  intro x hx
  exact (endFiltrationQuotientPairing_mk 𝓛 ψF htriv hnontriv i j b ⟨x, hx⟩).symm.trans
    ((AddChar.eq_zero_iff.mp hq) _)

private theorem endFiltrationQuotientPairing_surjective (i j : ℤ) (hij : i ≤ j) :
    Function.Surjective (endFiltrationQuotientPairing 𝓛 ψF htriv hnontriv i j) := by
  have := finite_endFiltrationQuotient 𝓛 i j hij
  have hdual : 1 - j ≤ 1 - i := by omega
  have := finite_endFiltrationQuotient 𝓛 (1 - j) (1 - i) hdual
  have hcard (a b : ℤ) (hab : a ≤ b) :
      Nat.card (AddChar (endFiltrationQuotient 𝓛 a b) ℂ) =
        Nat.card (endFiltrationQuotient 𝓛 a b) := by
    have := finite_endFiltrationQuotient 𝓛 a b hab
    let := Fintype.ofFinite (endFiltrationQuotient 𝓛 a b)
    simp only [Nat.card_eq_fintype_card, AddChar.card_eq]
  have hinj := endFiltrationQuotientPairing_injective 𝓛 ψF htriv hnontriv i j
  have hle := Nat.card_le_card_of_injective _
    (endFiltrationQuotientPairing_injective 𝓛 ψF htriv hnontriv (1 - j) (1 - i))
  rw [hcard _ _ hdual, sub_sub_cancel, sub_sub_cancel] at hle
  exact (hinj.bijective_of_nat_card_le ((hcard i j hij).le.trans hle)).surjective

end LocalField

/-- Additive duality of hereditary-order filtrations and the characters `ψ_b`
    of Bushnell–Kutzko (1.1.4)–(1.1.6). -/
theorem additiveDuality : AdditiveDualityStatement.{u, v} := by
  intro F _ _ _ _ V _ _ 𝓛 ψF htriv hnontriv
  refine ⟨?_, ?_⟩
  · intro n
    ext b
    exact (mem_endFiltration_iff_character 𝓛 ψF htriv hnontriv n b).symm
  intro n r hrn hhalf
  let i : ℤ := (r : ℤ) + 1
  let j : ℤ := (n : ℤ) + 1
  have hi : 1 - i = -(r : ℤ) := by dsimp [i]; omega
  have hj : 1 - j = -(n : ℤ) := by dsimp [j]; omega
  have hij : i ≤ j := by dsimp [i, j]; omega
  have hdepth : n + 1 ≤ (r + 1) + (r + 1) := by omega
  let q := 𝓛.unitFiltrationToQuotient hdepth
  have hqsurj := 𝓛.unitFiltrationToQuotient_surjective hdepth (by omega)
  have hker (g : 𝓛.unitFiltration (r + 1)) :
      q g = 1 ↔ (g : (Module.End F V)ˣ) ∈ 𝓛.unitFiltration (n + 1) :=
    𝓛.mem_ker_unitFiltrationToQuotient hdepth g
  let pairing := endFiltrationQuotientPairing 𝓛 ψF htriv hnontriv i j
  have hpair (b : 𝓛.endFiltration (1 - j)) (g : 𝓛.unitFiltration (r + 1)) :
      pairing (Submodule.Quotient.mk b) (q g).toAdd =
        elementCharacter (traceCharacter ψF) (b : Module.End F V) g := by
    change pairing (Submodule.Quotient.mk b) (𝓛.unitFiltrationToQuotient hdepth g).toAdd = _
    rw [𝓛.unitFiltrationToQuotient_apply]
    exact endFiltrationQuotientPairing_mk 𝓛 ψF htriv hnontriv i j b _
  refine ⟨?_, ?_, ?_⟩
  · intro b hb
    let b' : 𝓛.endFiltration (1 - j) := ⟨b, by simpa only [hj] using hb⟩
    let ψ := pairing (Submodule.Quotient.mk b')
    let χ := ((AddChar.toMonoidHomEquiv ψ).comp q).toHomUnits
    refine ⟨χ, hpair b', fun g hg => ?_⟩
    apply Units.ext
    change ψ (q g).toAdd = 1
    rw [(hker g).mpr hg]
    exact ψ.map_zero_eq_one
  · intro b _
    rw [← hi, mem_endFiltration_iff_character 𝓛 ψF htriv hnontriv]
    constructor
    · intro h x hx
      obtain ⟨g, hg, hval⟩ := 𝓛.exists_mem_unitFiltration (n := r + 1) (by omega) hx
      simpa [elementCharacter_apply, hval, add_sub_cancel_left] using h g hg
    · intro h g hg
      exact h _ hg.2.2
  · intro χ hχ
    have hkerχ : q.ker ≤ χ.ker := fun g hg => hχ g ((hker g).mp hg)
    let χ' := q.liftOfSurjective hqsurj ⟨χ, hkerχ⟩
    have hχ' (g : 𝓛.unitFiltration (r + 1)) : χ' (q g) = χ g := by
      simp [χ', MonoidHom.liftOfSurjective]
    let φ := AddChar.toMonoidHomEquiv.symm ((Units.coeHom ℂ).comp χ')
    obtain ⟨z, hz⟩ := endFiltrationQuotientPairing_surjective 𝓛 ψF htriv hnontriv i j hij φ
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    refine ⟨b, by simpa only [hj] using b.property, fun g => ?_⟩
    calc
      (χ g : ℂ) = φ (q g).toAdd :=
        congrArg (fun a : ℂˣ => (a : ℂ)) (hχ' g).symm
      _ = pairing (Submodule.Quotient.mk b) (q g).toAdd := DFunLike.congr_fun hz.symm _
      _ = elementCharacter (traceCharacter ψF) (b : Module.End F V) g := hpair b g

end Langlands.BushnellKutzko
