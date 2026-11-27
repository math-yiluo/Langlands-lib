import Langlands.BushnellKutzko.TameCorestrictionProof
import Langlands.BushnellKutzko.StratumEquivalenceResidue

/-! # Filtration steps of the values of a tame corestriction by trace duality

Let `E/F` act on `V`, with `E^×` normalizing the `𝔬_F`-lattice chain `𝓛`. For a tame
corestriction `s : A → B` (`A = End_F(V)`, `B = End_E(V)`) and `x ∈ A`, the value `s(x)`
lies in `𝔓^{1−k} ∩ B` exactly when `tr_{A}(x y) ∈ 𝔭_F` for every `y ∈ 𝔓^k ∩ B`.

The proof uses the trace-adjoint construction of tame corestrictions (BK93 (1.3.4)): for a
nonzero `F`-linear form `ℓ` on `E` with `ℓ(z𝔬_E) ⊆ 𝔭_F ⟺ z ∈ 𝔭_E`, the map `s_ℓ` with
`ℓ(tr_B(s_ℓ(x) b)) = tr_A(x b)` is a tame corestriction, and every tame corestriction is a
unit multiple of it.
-/

noncomputable section

open Module ValuativeRel

namespace Langlands.BushnellKutzko

namespace TraceAdjoint

universe uF uE uV

section LinearAlgebra

variable (F : Type uF) [Field F] (E : Type uE) [Field E] [Algebra F E]
  (V : Type uV) [AddCommGroup V] [Module F V] [Module E V] [IsScalarTower F E V]

local notation "A" => Module.End F V
local notation "B" => Module.End E V

/-- Restriction of scalars `End_E(V) → End_F(V)` as an `F`-linear map. -/
def restrictEnd : B →ₗ[F] A :=
  LinearMap.restrictScalarsₗ (S := E) (M := V) (N := V) (R := F) (R₁ := F)

theorem restrictEnd_injective : Function.Injective (restrictEnd F E V) := by
  intro x y h
  ext v
  exact LinearMap.congr_fun h v

/-- The bilinear form `(b, b') ↦ ℓ(tr_B(b b'))` on `B`. -/
def traceForm (ℓ : E →ₗ[F] F) : LinearMap.BilinForm F B :=
  (LinearMap.mul F B).compr₂ (ℓ.comp ((LinearMap.trace E V).restrictScalars F))

variable [FiniteDimensional E V]

theorem traceForm_nondegenerate (ℓ : E →ₗ[F] F) (hℓ : ℓ ≠ 0) :
    (traceForm F E V ℓ).Nondegenerate := by
  obtain ⟨z, hz⟩ := DFunLike.ne_iff.mp hℓ
  have hleft : (traceForm F E V ℓ).SeparatingLeft := by
    intro x hx
    ext v
    by_contra hv
    have hm : x v ∉ (⊥ : Submodule E V) := by simpa using hv
    obtain ⟨f, _, hf⟩ := LinearMap.exists_extend_of_notMem (0 : (⊥ : Submodule E V) →ₗ[E] E)
      hm z
    have heq : x * f.smulRight v = f.smulRight (x v) := by
      ext w
      simp [Module.End.mul_apply]
    have ht := hx (f.smulRight v)
    change ℓ (LinearMap.trace E V (x * f.smulRight v)) = 0 at ht
    rw [heq, LinearMap.trace_smulRight, hf] at ht
    exact hz ht
  refine ⟨hleft, fun y hy => hleft y fun x => ?_⟩
  change ℓ (LinearMap.trace E V (y * x)) = 0
  rw [LinearMap.trace_mul_comm E]
  exact hy x

/-- The isomorphism `B ≅ Hom_F(B, F)` given by the form `traceForm`. -/
abbrev traceDual [FiniteDimensional F B] (ℓ : E →ₗ[F] F) (hℓ : ℓ ≠ 0) :
    B ≃ₗ[F] Module.Dual F B :=
  (traceForm F E V ℓ).toDual (traceForm_nondegenerate F E V ℓ hℓ)

theorem linearMap_id_ne_zero : (LinearMap.id : F →ₗ[F] F) ≠ 0 := by
  intro h
  exact one_ne_zero (show (1 : F) = 0 from LinearMap.congr_fun h 1)

variable [FiniteDimensional F V]

omit [FiniteDimensional E V] in
theorem finite_restrictEnd : FiniteDimensional F B :=
  Module.Finite.of_injective (restrictEnd F E V) (restrictEnd_injective F E V)

/-- The trace adjoint `s_ℓ : A → B`, characterized by `ℓ(tr_B(s_ℓ(x) b)) = tr_A(x b)`. -/
def traceAdjoint (ℓ : E →ₗ[F] F) (hℓ : ℓ ≠ 0) : A →ₗ[F] B :=
  letI := finite_restrictEnd F E V
  (traceDual F E V ℓ hℓ).symm.toLinearMap.comp
    ((restrictEnd F E V).dualMap.comp
      (traceDual F F V LinearMap.id (linearMap_id_ne_zero F)).toLinearMap)

theorem traceAdjoint_spec (ℓ : E →ₗ[F] F) (hℓ : ℓ ≠ 0) (x : A) (b : B) :
    ℓ (LinearMap.trace E V (traceAdjoint F E V ℓ hℓ x * b)) =
      LinearMap.trace F V (x * b.restrictScalars F) := by
  let := finite_restrictEnd F E V
  let d := traceDual F E V ℓ hℓ
  change d (d.symm ((restrictEnd F E V).dualMap
    (traceDual F F V LinearMap.id (linearMap_id_ne_zero F) x))) b = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem eq_of_trace_tests (ℓ : E →ₗ[F] F) (hℓ : ℓ ≠ 0) {x y : B}
    (h : ∀ b : B, ℓ (LinearMap.trace E V (x * b)) = ℓ (LinearMap.trace E V (y * b))) :
    x = y := by
  have := finite_restrictEnd F E V
  exact (traceDual F E V ℓ hℓ).injective (LinearMap.ext h)

theorem traceAdjoint_mul_left (ℓ : E →ₗ[F] F) (hℓ : ℓ ≠ 0) (b : B) (x : A) :
    traceAdjoint F E V ℓ hℓ (b.restrictScalars F * x) = b * traceAdjoint F E V ℓ hℓ x := by
  apply eq_of_trace_tests F E V ℓ hℓ
  intro d
  rw [traceAdjoint_spec]
  calc
    LinearMap.trace F V (b.restrictScalars F * x * d.restrictScalars F) =
        LinearMap.trace F V (x * (d * b).restrictScalars F) := by
      rw [mul_assoc, LinearMap.trace_mul_comm F]
      rfl
    _ = ℓ (LinearMap.trace E V (traceAdjoint F E V ℓ hℓ x * (d * b))) :=
      (traceAdjoint_spec F E V ℓ hℓ x (d * b)).symm
    _ = ℓ (LinearMap.trace E V (b * traceAdjoint F E V ℓ hℓ x * d)) := by
      rw [← mul_assoc, LinearMap.trace_mul_cycle E]

theorem traceAdjoint_mul_right (ℓ : E →ₗ[F] F) (hℓ : ℓ ≠ 0) (x : A) (b : B) :
    traceAdjoint F E V ℓ hℓ (x * b.restrictScalars F) = traceAdjoint F E V ℓ hℓ x * b := by
  apply eq_of_trace_tests F E V ℓ hℓ
  intro d
  rw [traceAdjoint_spec, mul_assoc]
  have hr : (b * d).restrictScalars F = b.restrictScalars F * d.restrictScalars F := rfl
  rw [← hr, ← traceAdjoint_spec, mul_assoc]

end LinearAlgebra

section LocalField

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {E : Type uE} [Field E] [Algebra F E] [FiniteDimensional F E]

local notation "O" => 𝒪[F]
local notation "S" => subfieldIntegers F E

/-- A nonzero `F`-linear form `ℓ` on `E` with `ℓ(z𝔬_E) ⊆ 𝔭_F` exactly when `z ∈ 𝔭_E`. -/
theorem exists_conductor_form :
    ∃ ℓ : E →ₗ[F] F, ℓ ≠ 0 ∧ ∀ z : E,
      (∀ a : S, ℓ (z * (a : E)) ∈ maximalIdealInField O F) ↔
        z ∈ maximalIdealInField S E := by
  let m := IsLocalRing.maximalIdeal S
  let M := (m.restrictScalars O).map (subfieldIntegers F E).val.toLinearMap
  have hM : M.FG := (IsNoetherian.noetherian (m.restrictScalars O)).map _
  have h1 : (1 : E) ∉ M := by
    rintro ⟨a, ha, he⟩
    have ha1 : a = 1 := Subtype.ext he
    exact Ideal.one_notMem m (ha1 ▸ ha)
  obtain ⟨ℓ, hℓ, hℓ1⟩ := separates_fg_submodule (K := F) M hM h1
  refine ⟨ℓ, ?_, fun z => ⟨?_, ?_⟩⟩
  · rintro rfl
    exact hℓ1 ⟨0, zero_mem _, by simp⟩
  · intro h
    by_contra hz
    have hz0 : z ≠ 0 := by
      rintro rfl
      exact hz ⟨0, zero_mem _, map_zero _⟩
    have hinv : ∃ a : S, z * (a : E) = 1 := by
      by_cases hzS : z ∈ S
      · let r : S := ⟨z, hzS⟩
        have hu : IsUnit r := by
          by_contra hnu
          exact hz ⟨r, hnu, rfl⟩
        obtain ⟨a, ha⟩ := isUnit_iff_exists_inv.mp hu
        exact ⟨a, congrArg (fun x : S => (x : E)) ha⟩
      · let := Langlands.LocalField.FiniteExtension.normedField F E
        have hle : 1 ≤ ‖z‖ :=
          (lt_of_not_ge (fun h => hzS ((mem_subfieldIntegers_iff_norm_le_one F E z).mpr h))).le
        have hz' : z⁻¹ ∈ S := (mem_subfieldIntegers_iff_norm_le_one F E z⁻¹).mpr (by
          rw [norm_inv]
          exact inv_le_one_of_one_le₀ hle)
        exact ⟨⟨z⁻¹, hz'⟩, mul_inv_cancel₀ hz0⟩
    obtain ⟨a, ha⟩ := hinv
    exact hℓ1 (ha ▸ h a)
  · rintro ⟨r, hr, rfl⟩ a
    apply hℓ
    exact ⟨r * a, m.mul_mem_right a hr, rfl⟩

variable {V : Type uV} [AddCommGroup V] [Module F V] [Module E V] [IsScalarTower F E V]
  [FiniteDimensional F V] [FiniteDimensional E V]

local notation "A" => Module.End F V
local notation "B" => Module.End E V

omit [FiniteDimensional F V] in
/-- Trace duality on the extension chain, tested with a conductor form. -/
theorem mem_extensionChain_endFiltration_iff_trace (ℓ : E →ₗ[F] F)
    (hcond : ∀ z : E, (∀ a : S, ℓ (z * (a : E)) ∈ maximalIdealInField O F) ↔
        z ∈ maximalIdealInField S E)
    (𝓛 : LatticeChain O F V) (h : ∀ a : Eˣ, subfieldUnits F E V a ∈ 𝓛.stabilizer)
    (k : ℤ) (b : B) :
    b ∈ (𝓛.extensionChain h).endFiltration (1 - k) ↔
      ∀ y ∈ (𝓛.extensionChain h).endFiltration k,
        ℓ (LinearMap.trace E V (b * y)) ∈ maximalIdealInField O F := by
  let 𝓜 := 𝓛.extensionChain h
  rw [𝓜.mem_endFiltration_iff_trace_mul]
  constructor
  · intro hb y hy
    simpa using (hcond _).mpr (hb y hy) (1 : S)
  · intro hb y hy
    apply (hcond _).mp
    intro a
    have hm : b * (a • y) = (a : E) • (b * y) := by
      ext v
      change b ((a : E) • y v) = (a : E) • b (y v)
      exact b.map_smul (a : E) (y v)
    have ht := hb (a • y) ((𝓜.endFiltration k).smul_mem a hy)
    rw [hm, map_smul, smul_eq_mul, mul_comm] at ht
    exact ht

/-- The image of each filtration step under the trace adjoint. -/
theorem traceAdjoint_image (ℓ : E →ₗ[F] F) (hℓ : ℓ ≠ 0)
    (hcond : ∀ z : E, (∀ a : S, ℓ (z * (a : E)) ∈ maximalIdealInField O F) ↔
        z ∈ maximalIdealInField S E)
    (𝓛 : LatticeChain O F V) (h : ∀ a : Eˣ, subfieldUnits F E V a ∈ 𝓛.stabilizer)
    (n : ℤ) :
    traceAdjoint F E V ℓ hℓ '' (𝓛.endFiltration n : Set A) =
      {b : B | b.restrictScalars F ∈ 𝓛.endFiltration n} := by
  have := finite_restrictEnd F E V
  let 𝓜 := 𝓛.extensionChain h
  let s := traceAdjoint F E V ℓ hℓ
  let I := (𝓛.endFiltration n).map (s.restrictScalars O)
  have hI : I.FG := (𝓛.fg_endFiltration n).map _
  have hQ (k : ℤ) (b : B) : b ∈ 𝓜.endFiltration k ↔
      b.restrictScalars F ∈ 𝓛.endFiltration k :=
    𝓛.mem_extensionChain_endFiltration h k b
  have hdual := mem_extensionChain_endFiltration_iff_trace ℓ hcond 𝓛 h
  have hnn : 1 - (1 - n) = n := by omega
  ext b
  change b ∈ I ↔ b.restrictScalars F ∈ 𝓛.endFiltration n
  rw [← hQ n b]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [← hnn, hdual]
    intro y hy
    change ℓ (LinearMap.trace E V (s x * y)) ∈ maximalIdealInField O F
    rw [traceAdjoint_spec]
    exact (𝓛.mem_endFiltration_iff_trace_mul (1 - n) x).mp (hnn.symm ▸ hx)
      _ ((hQ _ y).mp hy)
  · intro hb
    by_contra hi
    obtain ⟨f, hf, hfb⟩ := separates_fg_submodule (K := F) I hI hi
    obtain ⟨c, hc⟩ := (traceDual F E V ℓ hℓ).surjective f
    have he (y : B) : f y = ℓ (LinearMap.trace E V (c * y)) :=
      (LinearMap.congr_fun hc y).symm
    have hr : c.restrictScalars F ∈ 𝓛.endFiltration (1 - n) := by
      apply (𝓛.mem_endFiltration_iff_trace_mul n _).mpr
      intro x hx
      have ht := hf (s x) ⟨x, hx, rfl⟩
      rw [he, LinearMap.trace_mul_comm E c, traceAdjoint_spec,
        LinearMap.trace_mul_comm F x] at ht
      exact ht
    have ht := (hdual (1 - n) b).mp (hnn.symm ▸ hb) c ((hQ _ c).mpr hr)
    apply hfb
    rw [he, LinearMap.trace_mul_comm E c]
    exact ht

/-- The trace adjoint of a conductor form as a tame corestriction. -/
def traceAdjointCorestriction (ℓ : E →ₗ[F] F) (hℓ : ℓ ≠ 0)
    (hcond : ∀ z : E, (∀ a : S, ℓ (z * (a : E)) ∈ maximalIdealInField O F) ↔
        z ∈ maximalIdealInField S E) : TameCorestriction O F E V where
  toAddMonoidHom := (traceAdjoint F E V ℓ hℓ).toAddMonoidHom
  map_mul_left := traceAdjoint_mul_left F E V ℓ hℓ
  map_mul_right := traceAdjoint_mul_right F E V ℓ hℓ
  image_order := fun 𝓛 h𝓛 => traceAdjoint_image ℓ hℓ hcond 𝓛 h𝓛 0

end LocalField

end TraceAdjoint

section Kernel

universe uF uE uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {E : Type uE} [Field E] [Algebra F E]
  {V : Type uV} [AddCommGroup V] [Module F V] [Module E V] [IsScalarTower F E V]
  [FiniteDimensional F V]

/-- **Trace duality for a tame corestriction.** For a tame corestriction `s` relative to `E/F`,
with `E^×` normalizing `𝓛`, the value `s(x)` lies in `𝔓^{1−k}` exactly when
`tr(x y) ∈ 𝔭_F` for every `E`-linear `y ∈ 𝔓^k`. -/
theorem TameCorestriction.restrictScalars_mem_endFiltration_iff_trace
    (s : TameCorestriction 𝒪[F] F E V) (𝓛 : LatticeChain 𝒪[F] F V)
    (h𝓛 : ∀ a : Eˣ, subfieldUnits F E V a ∈ 𝓛.stabilizer) (k : ℤ) (x : Module.End F V) :
    (s x).restrictScalars F ∈ 𝓛.endFiltration (1 - k) ↔
      ∀ y ∈ 𝓛.endFiltration k, y ∈ StratumEquivalence.fieldCommutant E →
        LinearMap.trace F V (x * y) ∈ maximalIdealInField 𝒪[F] F := by
  have : Nontrivial V := by
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    exact (ne_of_lt (𝓛.lattice_succ_lt 0)) (Subsingleton.elim _ _)
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let j : E →ₗ[F] V := ((LinearMap.id : E →ₗ[E] E).smulRight v).restrictScalars F
  have : FiniteDimensional F E := Module.Finite.of_injective j (smul_left_injective E hv)
  have : FiniteDimensional E V := Module.Finite.of_restrictScalars_finite F E V
  obtain ⟨ℓ, hℓ, hcond⟩ := TraceAdjoint.exists_conductor_form (F := F) (E := E)
  let s₀ := TraceAdjoint.traceAdjointCorestriction (V := V) ℓ hℓ hcond
  obtain ⟨u, hu⟩ := (tameCorestriction F V E).2.1 s₀ s
  let 𝓜 := 𝓛.extensionChain h𝓛
  have hunit : s x ∈ 𝓜.endFiltration (1 - k) ↔ s₀ x ∈ 𝓜.endFiltration (1 - k) := by
    rw [hu x]
    constructor
    · intro h
      have h' := (𝓜.endFiltration (1 - k)).smul_mem (↑u⁻¹ : subfieldIntegers F E) h
      change ((↑u⁻¹ : subfieldIntegers F E) : E) • (((u : subfieldIntegers F E) : E) • s₀ x) ∈
        𝓜.endFiltration (1 - k) at h'
      rwa [smul_smul, ← Subalgebra.coe_mul, Units.inv_mul, Subalgebra.coe_one, one_smul] at h'
    · intro h
      exact (𝓜.endFiltration (1 - k)).smul_mem (u : subfieldIntegers F E) h
  rw [← 𝓛.mem_extensionChain_endFiltration h𝓛, hunit,
    TraceAdjoint.mem_extensionChain_endFiltration_iff_trace ℓ hcond 𝓛 h𝓛]
  constructor
  · intro h y hy hyE
    let y' : Module.End E V :=
      { toFun := y
        map_add' := y.map_add
        map_smul' := fun a w => hyE a w }
    have h' := h y' ((𝓛.mem_extensionChain_endFiltration h𝓛 k y').mpr hy)
    change ℓ (LinearMap.trace E V (TraceAdjoint.traceAdjoint F E V ℓ hℓ x * y')) ∈ _ at h'
    rwa [TraceAdjoint.traceAdjoint_spec] at h'
  · intro h y hy
    change ℓ (LinearMap.trace E V (TraceAdjoint.traceAdjoint F E V ℓ hℓ x * y)) ∈ _
    rw [TraceAdjoint.traceAdjoint_spec]
    exact h _ ((𝓛.mem_extensionChain_endFiltration h𝓛 k y).mp hy)
      (fun a w => y.map_smul a w)

end Kernel

end Langlands.BushnellKutzko
