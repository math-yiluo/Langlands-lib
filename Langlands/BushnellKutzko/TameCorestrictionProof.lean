import Langlands.BushnellKutzko.TameCorestrictionStatement
import Langlands.BushnellKutzko.CorestrictionChains

/-! # Tame corestriction by the trace adjoint -/

noncomputable section

open Module ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uE uV

section LinearAlgebra

variable (F : Type uF) [Field F] (E : Type uE) [Field E] [Algebra F E]
  (V : Type uV) [AddCommGroup V] [Module F V] [Module E V] [IsScalarTower F E V]

local notation "A" => Module.End F V
local notation "B" => Module.End E V

private def restrictEnd : B →ₗ[F] A :=
  LinearMap.restrictScalarsₗ (S := E) (M := V) (N := V) (R := F) (R₁ := F)

private theorem restrictEnd_injective : Function.Injective (restrictEnd F E V) := by
  intro x y h
  ext v
  exact LinearMap.congr_fun h v

private def traceForm (ℓ : E →ₗ[F] F) : LinearMap.BilinForm F B :=
  (LinearMap.mul F B).compr₂ (ℓ.comp ((LinearMap.trace E V).restrictScalars F))

variable [FiniteDimensional E V]

private theorem traceForm_nondegenerate (ℓ : E →ₗ[F] F) (hℓ : ℓ ≠ 0) :
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

private abbrev traceDual [FiniteDimensional F B] (ℓ : E →ₗ[F] F) (hℓ : ℓ ≠ 0) :
    B ≃ₗ[F] Module.Dual F B :=
  (traceForm F E V ℓ).toDual (traceForm_nondegenerate F E V ℓ hℓ)

private theorem linearMap_id_ne_zero : (LinearMap.id : F →ₗ[F] F) ≠ 0 := by
  intro h
  exact one_ne_zero (show (1 : F) = 0 from LinearMap.congr_fun h 1)

variable [FiniteDimensional F V]

omit [FiniteDimensional E V] in
private theorem finite_restrictEnd : FiniteDimensional F B :=
  Module.Finite.of_injective (restrictEnd F E V) (restrictEnd_injective F E V)

private def traceAdjoint (ℓ : E →ₗ[F] F) (hℓ : ℓ ≠ 0) : A →ₗ[F] B :=
  letI := finite_restrictEnd F E V
  (traceDual F E V ℓ hℓ).symm.toLinearMap.comp
    ((restrictEnd F E V).dualMap.comp
      (traceDual F F V LinearMap.id (linearMap_id_ne_zero F)).toLinearMap)

private theorem traceAdjoint_spec (ℓ : E →ₗ[F] F) (hℓ : ℓ ≠ 0) (x : A) (b : B) :
    ℓ (LinearMap.trace E V (traceAdjoint F E V ℓ hℓ x * b)) =
      LinearMap.trace F V (x * b.restrictScalars F) := by
  let := finite_restrictEnd F E V
  let d := traceDual F E V ℓ hℓ
  change d (d.symm ((restrictEnd F E V).dualMap
    (traceDual F F V LinearMap.id (linearMap_id_ne_zero F) x))) b = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

private theorem eq_of_trace_tests (ℓ : E →ₗ[F] F) (hℓ : ℓ ≠ 0) {x y : B}
    (h : ∀ b : B, ℓ (LinearMap.trace E V (x * b)) = ℓ (LinearMap.trace E V (y * b))) :
    x = y := by
  have := finite_restrictEnd F E V
  exact (traceDual F E V ℓ hℓ).injective (LinearMap.ext h)

private theorem traceAdjoint_mul_left (ℓ : E →ₗ[F] F) (hℓ : ℓ ≠ 0) (b : B) (x : A) :
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

private theorem traceAdjoint_mul_right (ℓ : E →ₗ[F] F) (hℓ : ℓ ≠ 0) (x : A) (b : B) :
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

private theorem exists_conductor_form :
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

private theorem traceAdjoint_image (ℓ : E →ₗ[F] F) (hℓ : ℓ ≠ 0)
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
  have hdual (k : ℤ) (b : B) : b ∈ 𝓜.endFiltration (1 - k) ↔
      ∀ y ∈ 𝓜.endFiltration k, ℓ (LinearMap.trace E V (b * y)) ∈ maximalIdealInField O F := by
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

local notation "Corestriction" => TameCorestriction O F E V

private def baseLinearMap (t : Corestriction) : A →ₗ[F] B where
  toFun := t
  map_add' := t.toAddMonoidHom.map_add
  map_smul' := by
    intro a x
    let b : B := (algebraMap F E a) • 1
    have h := t.map_mul_left b x
    change t (b.restrictScalars F * x) = b * t x at h
    have hleft : b.restrictScalars F * x = a • x := by
      ext v
      exact algebraMap_smul E a (x v)
    have hright : b * t x = a • t x := by
      ext v
      exact algebraMap_smul E a (t x v)
    rw [hleft, hright] at h
    exact h

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FiniteDimensional F E] in
private theorem eq_scalar_traceAdjoint [Nontrivial V] (ℓ : E →ₗ[F] F) (hℓ : ℓ ≠ 0)
    (t : Corestriction) :
    ∃ z : E, ∀ x : A, t x = z • traceAdjoint F E V ℓ hℓ x := by
  let d := traceDual F F V LinearMap.id (linearMap_id_ne_zero F)
  let f := (ℓ.comp ((LinearMap.trace E V).restrictScalars F)).comp (baseLinearMap t)
  let c := d.symm f
  have hc (x : A) : LinearMap.trace F V (c * x) = ℓ (LinearMap.trace E V (t x)) := by
    change d (d.symm f) x = f x
    rw [LinearEquiv.apply_symm_apply]
  have hleft (b : B) (x : A) : t (b.restrictScalars F * x) = b * t x :=
    t.map_mul_left b x
  have hright (x : A) (b : B) : t (x * b.restrictScalars F) = t x * b :=
    t.map_mul_right x b
  have hcomm (b : B) : c * b.restrictScalars F = b.restrictScalars F * c := by
    apply d.injective
    ext x
    change LinearMap.trace F V (c * b.restrictScalars F * x) =
      LinearMap.trace F V (b.restrictScalars F * c * x)
    calc
      _ = LinearMap.trace F V (c * (b.restrictScalars F * x)) := by rw [mul_assoc]
      _ = ℓ (LinearMap.trace E V (b * t x)) := by rw [hc, hleft]
      _ = ℓ (LinearMap.trace E V (t x * b)) := by rw [LinearMap.trace_mul_comm E]
      _ = LinearMap.trace F V (c * (x * b.restrictScalars F)) := by rw [hc, hright]
      _ = _ := by rw [← mul_assoc, LinearMap.trace_mul_cycle F]
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hv' : v ∉ (⊥ : Submodule E V) := by simpa using hv
  obtain ⟨g, _, hgv⟩ := LinearMap.exists_extend_of_notMem (0 : (⊥ : Submodule E V) →ₗ[E] E)
    hv' 1
  let z := g (c v)
  have hscalar : c = (z • (1 : B)).restrictScalars F := by
    ext w
    have ht := LinearMap.congr_fun (hcomm (g.smulRight w)) v
    change c (g v • w) = g (c v) • w at ht
    rw [hgv, one_smul] at ht
    exact ht
  refine ⟨z, fun x => ?_⟩
  apply eq_of_trace_tests F E V ℓ hℓ
  intro b
  calc
    _ = LinearMap.trace F V (c * (x * b.restrictScalars F)) := by rw [hc, hright]
    _ = LinearMap.trace F V ((c * x) * b.restrictScalars F) := by rw [mul_assoc]
    _ = ℓ (LinearMap.trace E V (traceAdjoint F E V ℓ hℓ (c * x) * b)) :=
      (traceAdjoint_spec F E V ℓ hℓ (c * x) b).symm
    _ = _ := by
      rw [hscalar, traceAdjoint_mul_left]
      rfl

omit [FiniteDimensional F V] in
private theorem unit_of_order_images [Nontrivial V] (s t : Corestriction) {z : E}
    (h : ∀ x : A, t x = z • s x) : ∃ u : Sˣ, ((u : S) : E) = z := by
  let b := Module.finBasis E V
  have := b.index_nonempty
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible S
  let 𝓛 := subfieldBasisChain (F := F) b hπ
  have h𝓛 : ∀ a : Eˣ, subfieldUnits F E V a ∈ 𝓛.stabilizer :=
    subfieldBasisChain_normalized b hπ
  let Q := {v : B | v.restrictScalars F ∈ 𝓛.order}
  have h1 : (1 : B) ∈ Q := 𝓛.order.one_mem
  have hs : s '' (𝓛.order : Set A) = Q := s.image_order 𝓛 h𝓛
  have ht : t '' (𝓛.order : Set A) = Q := t.image_order 𝓛 h𝓛
  have hdetect (a : E) (ha : a • (1 : B) ∈ Q) : a ∈ S := by
    apply mem_subfieldIntegers_of_mem_subfieldBasisChain_order b hπ
    exact ha
  obtain ⟨x, hx, hsx⟩ := (Set.ext_iff.mp hs 1).mpr h1
  have hz : z ∈ S := by
    apply hdetect
    rw [← hsx, ← h]
    exact (Set.ext_iff.mp ht _).mp ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hty⟩ := (Set.ext_iff.mp ht 1).mpr h1
  have hzy : z • s y = 1 := (h y).symm.trans hty
  have hz0 : z ≠ 0 := by
    intro hz0
    rw [hz0, zero_smul] at hzy
    exact zero_ne_one hzy
  have hz' : z⁻¹ ∈ S := by
    apply hdetect
    rw [← hzy, inv_smul_smul₀ hz0]
    exact (Set.ext_iff.mp hs _).mp ⟨y, hy, rfl⟩
  let a : S := ⟨z, hz⟩
  let a' : S := ⟨z⁻¹, hz'⟩
  have haa' : a * a' = 1 := Subtype.ext (mul_inv_cancel₀ hz0)
  exact ⟨⟨a, a', haa', by rw [mul_comm, haa']⟩, rfl⟩

omit [FiniteDimensional F V] [FiniteDimensional E V] in
private theorem image_of_unit_mul (s t : Corestriction) (u : Sˣ)
    (hu : ∀ x : A, t x = ((u : S) : E) • s x)
    (𝓛 : LatticeChain O F V) (h𝓛 : ∀ a : Eˣ, subfieldUnits F E V a ∈ 𝓛.stabilizer)
    (n : ℤ) (hs : s '' (𝓛.endFiltration n : Set A) =
      {b : B | b.restrictScalars F ∈ 𝓛.endFiltration n}) :
    t '' (𝓛.endFiltration n : Set A) = {b : B | b.restrictScalars F ∈ 𝓛.endFiltration n} := by
  let Q := (𝓛.extensionChain h𝓛).endFiltration n
  have hQ (b : B) : b ∈ Q ↔ b.restrictScalars F ∈ 𝓛.endFiltration n :=
    𝓛.mem_extensionChain_endFiltration h𝓛 n b
  have hs' (b : B) : b ∈ s '' (𝓛.endFiltration n : Set A) ↔ b ∈ Q :=
    (Set.ext_iff.mp hs b).trans (hQ b).symm
  ext b
  change (∃ x ∈ 𝓛.endFiltration n, t x = b) ↔ b.restrictScalars F ∈ 𝓛.endFiltration n
  rw [← hQ b]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [hu]
    exact Q.smul_mem (u : S) ((hs' _).mp ⟨x, hx, rfl⟩)
  · intro hb
    obtain ⟨x, hx, he⟩ := (hs' _).mpr (Q.smul_mem (↑u⁻¹ : S) hb)
    refine ⟨x, hx, ?_⟩
    rw [hu, he]
    change (u : S) • ((↑u⁻¹ : S) • b) = b
    rw [← mul_smul, Units.mul_inv, one_smul]

end LocalField

/-- Tame corestrictions exist, differ by extension-integer units, and have the stated
images at every integer depth. -/
theorem tameCorestriction : TameCorestrictionStatement := by
  intro F _ _ _ _ V _ _ _ E _ _ _ _
  let O := 𝒪[F]
  let S := subfieldIntegers F E
  let A := Module.End F V
  rcases subsingleton_or_nontrivial V with hV | hV
  · have : Subsingleton V := hV
    have noChain (𝓛 : LatticeChain O F V) : False :=
      (ne_of_lt (𝓛.lattice_succ_lt 0)) (Subsingleton.elim _ _)
    let s : TameCorestriction O F E V :=
      { toAddMonoidHom := 0
        map_mul_left := fun _ _ => Subsingleton.elim _ _
        map_mul_right := fun _ _ => Subsingleton.elim _ _
        image_order := fun 𝓛 _ => (noChain 𝓛).elim }
    exact ⟨⟨s⟩, fun _ _ => ⟨1, fun _ => Subsingleton.elim _ _⟩,
      fun _ 𝓛 _ _ => (noChain 𝓛).elim⟩
  · have : Nontrivial V := hV
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    let j : E →ₗ[F] V := ((LinearMap.id : E →ₗ[E] E).smulRight v).restrictScalars F
    have : FiniteDimensional F E := Module.Finite.of_injective j (smul_left_injective E hv)
    have : FiniteDimensional E V := Module.Finite.of_restrictScalars_finite F E V
    obtain ⟨ℓ, hℓ, hcond⟩ := exists_conductor_form (F := F) (E := E)
    let s₀ := traceAdjoint F E V ℓ hℓ
    let s : TameCorestriction O F E V :=
      { toAddMonoidHom := s₀.toAddMonoidHom
        map_mul_left := traceAdjoint_mul_left F E V ℓ hℓ
        map_mul_right := traceAdjoint_mul_right F E V ℓ hℓ
        image_order := fun 𝓛 h𝓛 => traceAdjoint_image ℓ hℓ hcond 𝓛 h𝓛 0 }
    have hunit (t : TameCorestriction O F E V) :
        ∃ u : Sˣ, ∀ x : A, t x = ((u : S) : E) • s x := by
      obtain ⟨a, ha⟩ := eq_scalar_traceAdjoint ℓ hℓ t
      obtain ⟨u, hu⟩ := unit_of_order_images s t ha
      exact ⟨u, fun x => hu ▸ ha x⟩
    refine ⟨⟨s⟩, ?_, ?_⟩
    · intro t t'
      obtain ⟨u, hu⟩ := hunit t
      obtain ⟨u', hu'⟩ := hunit t'
      refine ⟨u' * u⁻¹, fun x => ?_⟩
      rw [hu', hu]
      change (u' : S) • s x = ((u' : S) * (↑u⁻¹ : S)) • ((u : S) • s x)
      rw [← mul_smul, mul_assoc, Units.inv_mul, mul_one]
    · intro t 𝓛 h𝓛 n
      obtain ⟨u, hu⟩ := hunit t
      exact image_of_unit_mul s t u hu 𝓛 h𝓛 n (traceAdjoint_image ℓ hℓ hcond 𝓛 h𝓛 n)

end Langlands.BushnellKutzko
