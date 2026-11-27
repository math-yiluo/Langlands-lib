import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Langlands.BushnellKutzko.AdditiveDualityProof
import Langlands.BushnellKutzko.UnitFiltrationQuotient

/-! # Characters of a subgroup of `U^{k}/U^{k+1}` are additive characters -/

noncomputable section

open ValuativeRel
open scoped Pointwise

namespace Langlands.BushnellKutzko

universe u v

section Extension

/-- A complex additive character of a subgroup of a finite abelian group extends to the whole
group. -/
theorem AddChar.exists_extend_of_finite {W : Type*} [AddCommGroup W] [Finite W]
    (M : AddSubgroup W) (ξ : AddChar M ℂ) : ∃ Λ : AddChar W ℂ, ∀ x : M, Λ (x : W) = ξ x := by
  classical
  let R : AddChar W ℂ →+ AddChar M ℂ :=
    { toFun := fun Λ => Λ.compAddMonoidHom M.subtype
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  suffices hξ : ξ ∈ R.range by
    obtain ⟨Λ, hΛ⟩ := hξ
    exact ⟨Λ, fun x => by rw [← hΛ]; rfl⟩
  by_contra hξ
  let I := R.range
  have hne : (QuotientAddGroup.mk' I ξ : AddChar M ℂ ⧸ I) ≠ 0 := by
    rwa [Ne, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
  obtain ⟨ψ', hψ'⟩ := AddChar.exists_apply_ne_zero.mpr hne
  let Ψ : AddChar (AddChar M ℂ) ℂ := ψ'.compAddMonoidHom (QuotientAddGroup.mk' I)
  obtain ⟨m, hm⟩ := (AddChar.doubleDualEmb_bijective (α := M)).2 Ψ
  have hΨI : ∀ Λ : AddChar W ℂ, Ψ (R Λ) = 1 := by
    intro Λ
    change ψ' (QuotientAddGroup.mk' I (R Λ)) = 1
    have hI : R Λ ∈ I := ⟨Λ, rfl⟩
    have h0 : QuotientAddGroup.mk' I (R Λ) = 0 := (QuotientAddGroup.eq_zero_iff (R Λ)).mpr hI
    rw [h0, AddChar.map_zero_eq_one]
  have hm0 : (m : W) = 0 := by
    apply AddChar.forall_apply_eq_zero.mp
    intro Λ
    have h := hΨI Λ
    rw [← hm, AddChar.doubleDualEmb_apply] at h
    exact h
  have hm0' : m = 0 := Subtype.ext hm0
  apply hψ'
  change Ψ ξ = 1
  rw [← hm, hm0', map_zero]
  rfl

end Extension

section LocalField

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type v} [AddCommGroup V] [Module F V]

local notation "G" => (Module.End F V)ˣ

/-- The quotient `𝔓^i/𝔓^j` of filtration steps is finite for `i ≤ j`. -/
theorem LatticeChain.finite_endFiltration_quotient (𝓛 : LatticeChain 𝒪[F] F V) (i j : ℤ)
    (hij : i ≤ j) :
    Finite ((𝓛.endFiltration i) ⧸ (𝓛.endFiltration j).comap (𝓛.endFiltration i).subtype) := by
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
  have hann : Module.IsTorsionBySet 𝒪[F]
      ((𝓛.endFiltration i) ⧸ (𝓛.endFiltration j).comap (𝓛.endFiltration i).subtype)
      (I : Set 𝒪[F]) :=
    (Module.isTorsionBySet_quotient_iff _ _).mpr fun x a ha =>
      hI (Submodule.smul_mem_smul ha x.property)
  let := hann.module
  have : IsScalarTower 𝒪[F] (𝒪[F] ⧸ I)
      ((𝓛.endFiltration i) ⧸ (𝓛.endFiltration j).comap (𝓛.endFiltration i).subtype) :=
    hann.isScalarTower
  have : Module.Finite 𝒪[F] (𝓛.endFiltration i) :=
    Module.Finite.iff_fg.mpr (𝓛.fg_endFiltration i)
  have : Finite (𝒪[F] ⧸ 𝓂[F]) := inferInstanceAs (Finite 𝓀[F])
  have : Finite (𝒪[F] ⧸ I) := Ideal.finite_quotient_pow (IsNoetherian.noetherian 𝓂[F]) k
  have : Module.Finite (𝒪[F] ⧸ I)
      ((𝓛.endFiltration i) ⧸ (𝓛.endFiltration j).comap (𝓛.endFiltration i).subtype) :=
    Module.Finite.of_restrictScalars_finite 𝒪[F] _ _
  exact Module.finite_of_finite (𝒪[F] ⧸ I)

/-- **Characters of subgroups of `U^{i+1}/U^{i+2}`.** Let `H ≤ U^{i+1}(𝔄)` and let `χ` be a
character of `H` trivial on `H ∩ U^{i+2}(𝔄)`. Then `χ = ψ_b` on `H` for some `b ∈ 𝔓^{−(i+1)}`. -/
theorem exists_elementCharacter_eq_of_trivial_on_succ (ψF : AddChar F ℂ)
    (htriv : ∀ a ∈ 𝓂[F], ψF (a : F) = 1) (hnontriv : ∃ a : 𝒪[F], ψF (a : F) ≠ 1)
    (𝓛 : LatticeChain 𝒪[F] F V) (i : ℕ) (H : Subgroup G)
    (hH : H ≤ 𝓛.unitFiltration (i + 1)) (χ : H →* ℂˣ)
    (hχ : ∀ h : H, (h : G) ∈ 𝓛.unitFiltration (i + 1 + 1) → χ h = 1) :
    ∃ b ∈ 𝓛.endFiltration (-((i + 1 : ℕ) : ℤ)), ∀ h : H,
      (χ h : ℂ) = elementCharacter (traceCharacter ψF) b h := by
  classical
  have hdepth : i + 1 + 1 ≤ (i + 1) + (i + 1) := by omega
  let W := (𝓛.endFiltration ((i + 1 : ℕ) : ℤ)) ⧸
    (𝓛.endFiltration ((i + 1 + 1 : ℕ) : ℤ)).comap (𝓛.endFiltration ((i + 1 : ℕ) : ℤ)).subtype
  have : Finite W := 𝓛.finite_endFiltration_quotient _ _ (by push_cast; omega)
  let q := 𝓛.unitFiltrationToQuotient hdepth
  let ι : H →* 𝓛.unitFiltration (i + 1) := Subgroup.inclusion hH
  let qH := q.comp ι
  have hker : qH.rangeRestrict.ker ≤ χ.ker := by
    intro g hg
    have hg' : q (ι g) = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.mp hg)
      exact this
    exact hχ g ((𝓛.mem_ker_unitFiltrationToQuotient hdepth (ι g)).mp hg')
  let χbar := qH.rangeRestrict.liftOfSurjective qH.rangeRestrict_surjective ⟨χ, hker⟩
  have hχbar (g : H) : χbar (qH.rangeRestrict g) = χ g := by
    simp [χbar, MonoidHom.liftOfSurjective]
  let M : AddSubgroup W := Subgroup.toAddSubgroup' qH.range
  let ξ : AddChar M ℂ :=
    { toFun := fun x => (χbar ⟨Multiplicative.ofAdd (x : W),
        (Subgroup.mem_toAddSubgroup' _ _).mp x.2⟩ : ℂ)
      map_zero_eq_one' := by
        have h1 : (⟨Multiplicative.ofAdd ((0 : M) : W),
            (Subgroup.mem_toAddSubgroup' _ _).mp (0 : M).2⟩ : qH.range) = 1 := rfl
        simp only [h1, map_one, Units.val_one]
      map_add_eq_mul' := fun x y => by
        have h1 : (⟨Multiplicative.ofAdd ((x + y : M) : W),
            (Subgroup.mem_toAddSubgroup' _ _).mp (x + y : M).2⟩ : qH.range) =
            ⟨Multiplicative.ofAdd (x : W), (Subgroup.mem_toAddSubgroup' _ _).mp x.2⟩ *
              ⟨Multiplicative.ofAdd (y : W), (Subgroup.mem_toAddSubgroup' _ _).mp y.2⟩ := rfl
        simp only [h1, map_mul, Units.val_mul] }
  obtain ⟨Λ, hΛ⟩ := AddChar.exists_extend_of_finite M ξ
  let χ' : 𝓛.unitFiltration (i + 1) →* ℂˣ := ((AddChar.toMonoidHomEquiv Λ).comp q).toHomUnits
  have hχ'triv : ∀ g : 𝓛.unitFiltration (i + 1),
      (g : G) ∈ 𝓛.unitFiltration (i + 1 + 1) → χ' g = 1 := by
    intro g hg
    apply Units.ext
    change Λ (q g).toAdd = 1
    rw [(𝓛.mem_ker_unitFiltrationToQuotient hdepth g).mpr hg]
    exact Λ.map_zero_eq_one
  obtain ⟨b, hb, hbχ⟩ := ((additiveDuality.{u, v} F V 𝓛 ψF htriv hnontriv).2 (i + 1) i (by omega)
    (by omega)).2.2 χ' hχ'triv
  refine ⟨b, hb, fun h => ?_⟩
  have hmem : (q (ι h)).toAdd ∈ M := by
    rw [Subgroup.mem_toAddSubgroup']
    exact ⟨h, rfl⟩
  calc (χ h : ℂ) = (χbar (qH.rangeRestrict h) : ℂ) := by rw [hχbar]
    _ = ξ ⟨(q (ι h)).toAdd, hmem⟩ := rfl
    _ = Λ (q (ι h)).toAdd := (hΛ ⟨(q (ι h)).toAdd, hmem⟩).symm
    _ = (χ' (ι h) : ℂ) := rfl
    _ = elementCharacter (traceCharacter ψF) b h := hbχ (ι h)

end LocalField

end Langlands.BushnellKutzko
