import Langlands.BushnellKutzko.RefinementDiagonal
import Langlands.BushnellKutzko.PureSimpleStratum

/-! # The centralizer argument behind the refinement theorem

This file holds the algebraic core of the proof of BK93 (2.2.8): approximation of elements
commuting with a perturbed element, invertibility of nonzero commuting elements, fieldness of
the generated algebra, and two-sided approximation between the generated field and a field
acting on `V`.
-/

open ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko

universe uF uV uL

section Core

variable {F : Type uF} [Field F] [ValuativeRel F] {V : Type uV} [AddCommGroup V] [Module F V]
  (𝓛 : LatticeChain 𝒪[F] F V)

local notation "P" => 𝓛.endFiltration
local notation "Lat" => 𝓛.lattice

theorem commutator_mem_endFiltration {m n : ℤ} {x y : Module.End F V} (hx : x ∈ P m)
    (hy : y ∈ P n) : x * y - y * x ∈ P (m + n) := by
  refine sub_mem (𝓛.mul_mem_endFiltration hx hy) ?_
  rw [add_comm]
  exact 𝓛.mul_mem_endFiltration hy hx

/-- **Core step.** Let `s` be an additive endomorphism of `A` that preserves every `𝔓^m`, kills
the commutators with `β` and is a bimodule map for the elements commuting with `β`. Assume the
two exactness inputs `hU1` (for `β`: if `X ∈ 𝔓^t` and `[β, X] ∈ 𝔓^{t-r}`, there is a small error
`x ∈ 𝔓^{t+1}` with `X - x` commuting with `β`) and `hV1` (for `c`). If `b' ∈ 𝔓^{-r}` and
`s(b') ≡ c (mod 𝔓^{1-r})`, then every `X ∈ 𝔓^t` whose commutator with `β + b'` lies in
`𝔓^{t+1-r}` is congruent modulo `𝔓^{t+1}` to an element commuting with `β` and `c`. -/
theorem refinement_core {β c b' : Module.End F V} {r : ℤ}
    (s : Module.End F V →+ Module.End F V)
    (hs_mem : ∀ (m : ℤ) (z : Module.End F V), z ∈ P m → s z ∈ P m)
    (hs_adj : ∀ X, s (β * X - X * β) = 0)
    (hs_left : ∀ Y z, Commute Y β → s (Y * z) = Y * s z)
    (hs_right : ∀ Y z, Commute Y β → s (z * Y) = s z * Y)
    (hU1 : ∀ (t : ℤ) (X : Module.End F V), X ∈ P t → β * X - X * β ∈ P (t - r) →
      ∃ x ∈ P (t + 1), Commute (X - x) β)
    (hV1 : ∀ (t : ℤ) (γ : Module.End F V), Commute γ β → γ ∈ P t →
      c * γ - γ * c ∈ P (t + 1 - r) → ∃ γ₁, Commute γ₁ β ∧ Commute γ₁ c ∧ γ - γ₁ ∈ P (t + 1))
    (hb' : b' ∈ P (-r)) (hsb' : s b' - c ∈ P (1 - r))
    {t : ℤ} {X : Module.End F V} (hX : X ∈ P t)
    (hXc : (β + b') * X - X * (β + b') ∈ P (t + 1 - r)) :
    ∃ γ₁, Commute γ₁ β ∧ Commute γ₁ c ∧ X - γ₁ ∈ P (t + 1) := by
  have h1 : b' * X - X * b' ∈ P (t - r) := by
    have := commutator_mem_endFiltration 𝓛 hb' hX
    rwa [show -r + t = t - r by ring] at this
  have h2 : β * X - X * β ∈ P (t - r) := by
    have heq : β * X - X * β = ((β + b') * X - X * (β + b')) - (b' * X - X * b') := by
      noncomm_ring
    rw [heq]
    exact sub_mem (𝓛.endFiltration_antitone (by omega) hXc) h1
  obtain ⟨x, hx, hY⟩ := hU1 t X hX h2
  have hYt : X - x ∈ P t := sub_mem hX (𝓛.endFiltration_antitone (by omega) hx)
  have h3 := hs_mem _ _ hXc
  have hdecomp : (β + b') * X - X * (β + b') =
      (β * X - X * β) + (b' * (X - x) - (X - x) * b') + (b' * x - x * b') := by
    noncomm_ring
  have h4 : s (b' * x - x * b') ∈ P (t + 1 - r) := by
    have := hs_mem _ _ (commutator_mem_endFiltration 𝓛 hb' hx)
    rwa [show -r + (t + 1) = t + 1 - r by ring] at this
  have h5 : s (b' * (X - x) - (X - x) * b') = s b' * (X - x) - (X - x) * s b' := by
    rw [map_sub, hs_right _ _ hY, hs_left _ _ hY]
  have h6 : s b' * (X - x) - (X - x) * s b' ∈ P (t + 1 - r) := by
    rw [hdecomp, map_add, map_add, hs_adj, zero_add, h5] at h3
    simpa using sub_mem h3 h4
  have h7 : (s b' - c) * (X - x) - (X - x) * (s b' - c) ∈ P (t + 1 - r) := by
    have := commutator_mem_endFiltration 𝓛 hsb' hYt
    rwa [show 1 - r + t = t + 1 - r by ring] at this
  have h8 : c * (X - x) - (X - x) * c ∈ P (t + 1 - r) := by
    have heq : c * (X - x) - (X - x) * c = (s b' * (X - x) - (X - x) * s b') -
        ((s b' - c) * (X - x) - (X - x) * (s b' - c)) := by
      noncomm_ring
    rw [heq]
    exact sub_mem h6 h7
  obtain ⟨γ₁, hγβ, hγc, hγ⟩ := hV1 t (X - x) hY hYt h8
  refine ⟨γ₁, hγβ, hγc, ?_⟩
  have heq : X - γ₁ = (X - x - γ₁) + x := by abel
  rw [heq]
  exact add_mem hγ hx

/-- A unit lying with its inverse in the order normalizes the chain. -/
theorem mem_stabilizer_of_mem_order {g : (Module.End F V)ˣ} (hg : (g : Module.End F V) ∈ 𝓛.order)
    (hg' : ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) ∈ 𝓛.order) : g ∈ 𝓛.stabilizer := by
  intro i
  refine ⟨i, le_antisymm ?_ ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    exact (𝓛.mem_order.mp hg) i v hv
  · intro v hv
    refine ⟨((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) v, (𝓛.mem_order.mp hg') i v hv, ?_⟩
    change (g : Module.End F V) (((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) v) = v
    rw [← Module.End.mul_apply, Units.mul_inv, Module.End.one_apply]

theorem mem_stabilizer_of_mem_unitFiltration {k : ℕ} {g : (Module.End F V)ˣ}
    (hg : g ∈ 𝓛.unitFiltration k) : g ∈ 𝓛.stabilizer :=
  mem_stabilizer_of_mem_order 𝓛 hg.1 hg.2.1

section Shift

variable {L : Type uL} [Field L] [Algebra F L] [Module L V] [IsScalarTower F L V]

/-- If `a` shifts the chain by `d`, then `a ∈ 𝔓^k` exactly when `k ≤ d`. -/
theorem subfieldEmbedding_mem_iff_le {a : L} {d : ℤ}
    (hd : ∀ (i : ℤ) (v : V), a • v ∈ Lat (i + d) ↔ v ∈ Lat i) (k : ℤ) :
    subfieldEmbedding F L V a ∈ P k ↔ k ≤ d := by
  constructor
  · intro h
    by_contra hk
    push Not at hk
    apply (𝓛.lattice_succ_lt 0).not_ge
    intro v hv
    have h1 : a • v ∈ Lat (k - d + d) := by
      have := h 0 v hv
      rwa [subfieldEmbedding_apply, zero_add, ← sub_add_cancel k d] at this
    exact 𝓛.antitone (by omega) ((hd _ v).mp h1)
  · intro hk i v hv
    rw [subfieldEmbedding_apply]
    exact 𝓛.antitone (by omega) ((hd i v).mpr hv)

/-- The inverse of an element shifting by `d` shifts by `-d`. -/
theorem inv_smul_lattice_shift {a : L} (ha : a ≠ 0) {d : ℤ}
    (hd : ∀ (i : ℤ) (v : V), a • v ∈ Lat (i + d) ↔ v ∈ Lat i) (i : ℤ) (v : V) :
    a⁻¹ • v ∈ Lat (i + -d) ↔ v ∈ Lat i := by
  have h := hd (i + -d) (a⁻¹ • v)
  rw [smul_inv_smul₀ ha, show i + -d + d = i by ring] at h
  exact h.symm

end Shift

section LocalField

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F] {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)

include hϖ in
/-- A nonzero endomorphism has an exact depth in the filtration. -/
theorem exists_depth {x : Module.End F V} (hx : x ≠ 0) : ∃ s : ℤ, x ∈ P s ∧ x ∉ P (s + 1) := by
  obtain ⟨t, ht⟩ := 𝓛.exists_uniformizer_pow_mem_endFiltration hϖ x 0
  have hlow : x ∈ P (-((t : ℤ) * 𝓛.period)) :=
    (𝓛.uniformizer_pow_end_mem_iff hϖ t _ x).mp (by rwa [neg_add_cancel])
  have hbdd : BddAbove {s : ℤ | x ∈ P s} := by
    by_contra hnb
    rw [not_bddAbove_iff] at hnb
    apply hx
    ext v
    rw [LinearMap.zero_apply]
    obtain ⟨i, hi⟩ := 𝓛.exists_lattice_depth hϖ v
    apply 𝓛.lattice_eq_zero_of_forall
    intro j
    obtain ⟨s, hs, hjs⟩ := hnb (j - i)
    exact 𝓛.antitone (by omega) (hs i v hi)
  have hne : ({s : ℤ | x ∈ P s} : Set ℤ).Nonempty := ⟨_, hlow⟩
  refine ⟨sSup {s : ℤ | x ∈ P s}, Int.csSup_mem hne hbdd, fun h => ?_⟩
  have := le_csSup hbdd h
  omega

end LocalField

end Core

/-! ### Fields generated inside `End_F(V)` -/

section FieldCriterion

variable {F : Type uF} [Field F]

/-- A commutative subalgebra of a finite-dimensional algebra whose nonzero elements are units of
the ambient algebra is a field. -/
theorem isField_of_forall_ne_zero_isUnit {R : Type*} [Ring R] [Algebra F R] [FiniteDimensional F R]
    [Nontrivial R] (K : Subalgebra F R) (hcomm : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x)
    (hunit : ∀ x ∈ K, x ≠ 0 → IsUnit x) : IsField K where
  exists_pair_ne := ⟨0, 1, fun h => zero_ne_one (congrArg Subtype.val h)⟩
  mul_comm x y := Subtype.ext (hcomm x x.2 y y.2)
  mul_inv_cancel {x} hx := by
    have hx' : (x : R) ≠ 0 := fun h => hx (Subtype.ext h)
    have hu := hunit x x.2 hx'
    haveI : FiniteDimensional F K :=
      Module.Finite.of_injective K.val.toLinearMap Subtype.val_injective
    let f : K →ₗ[F] K := LinearMap.mulLeft F x
    have hinj : Function.Injective f := by
      intro y z hyz
      apply Subtype.ext
      have h := congrArg Subtype.val hyz
      exact hu.mul_left_cancel h
    obtain ⟨y, hy⟩ := LinearMap.injective_iff_surjective.mp hinj 1
    exact ⟨y, hy⟩

end FieldCriterion

section Generated

variable {F : Type uF} [Field F] [ValuativeRel F] {V : Type uV} [AddCommGroup V] [Module F V]
  (𝓛 : LatticeChain 𝒪[F] F V)

local notation "P" => 𝓛.endFiltration

/-- Every nonzero element of `K` is a unit normalizing the chain. -/
def NormalizingUnits (K : Subalgebra F (Module.End F V)) : Prop :=
  ∀ X ∈ K, X ≠ 0 → ∃ g : (Module.End F V)ˣ, (g : Module.End F V) = X ∧ g ∈ 𝓛.stabilizer

theorem commute_mem_elementAlgebra {y X Y : Module.End F V} (hX : X ∈ elementAlgebra y)
    (hY : Y ∈ elementAlgebra y) : X * Y = Y * X :=
  (Algebra.commute_of_mem_adjoin_singleton_of_commute hY
    (Algebra.commute_of_mem_adjoin_self hX).symm).eq

/-- A generated algebra with normalizing units is a field normalizing the chain. -/
theorem isField_of_normalizingUnits {y : Module.End F V}
    (h : NormalizingUnits 𝓛 (elementAlgebra y)) :
    ∃ hf : IsField (elementAlgebra y),
      letI := hf.toField
      ∀ a : (elementAlgebra y)ˣ, subfieldUnits F (elementAlgebra y) V a ∈ 𝓛.stabilizer := by
  haveI := 𝓛.finiteDimensional
  haveI := 𝓛.nontrivial_space
  have hf : IsField (elementAlgebra y) :=
    isField_of_forall_ne_zero_isUnit _ (fun X hX Y hY => commute_mem_elementAlgebra hX hY)
      (fun X hX hX0 => by
        obtain ⟨g, hg, -⟩ := h X hX hX0
        exact hg ▸ g.isUnit)
  refine ⟨hf, ?_⟩
  letI := hf.toField
  intro a
  have ha : ((a : elementAlgebra y) : Module.End F V) ≠ 0 := fun h0 =>
    a.ne_zero (Subtype.ext h0)
  obtain ⟨g, hg, hgs⟩ := h _ (a : elementAlgebra y).2 ha
  have heq : subfieldUnits F (elementAlgebra y) V a = g := by
    apply Units.ext
    rw [coe_subfieldUnits, hg]
    ext v
    rfl
  rw [heq]
  exact hgs

/-- Conjugation carries `F[y]` into `F[u⁻¹ y u]`. -/
theorem conj_mem_elementAlgebra (u : (Module.End F V)ˣ) {z X : Module.End F V}
    (hX : X ∈ elementAlgebra z) :
    ((u⁻¹ : (Module.End F V)ˣ) : Module.End F V) * X * u ∈
      elementAlgebra (((u⁻¹ : (Module.End F V)ˣ) : Module.End F V) * z * (u : Module.End F V)) := by
  induction hX using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff.mp hx]
    exact Algebra.self_mem_adjoin_singleton F _
  | algebraMap a =>
    rw [← Algebra.commutes]
    simp only [mul_assoc, Units.inv_mul, mul_one]
    exact Subalgebra.algebraMap_mem _ a
  | add x x' _ _ hx hx' =>
    rw [mul_add, add_mul]
    exact add_mem hx hx'
  | mul x x' _ _ hx hx' =>
    have heq : ((u⁻¹ : (Module.End F V)ˣ) : Module.End F V) * (x * x') * u =
        (((u⁻¹ : (Module.End F V)ˣ) : Module.End F V) * x * u) *
          (((u⁻¹ : (Module.End F V)ˣ) : Module.End F V) * x' * u) := by
      simp only [mul_assoc, Units.mul_inv_cancel_left]
    rw [heq]
    exact mul_mem hx hx'

theorem conj_mem_elementAlgebra' (u : (Module.End F V)ˣ) {z X : Module.End F V}
    (hX : X ∈ elementAlgebra (((u⁻¹ : (Module.End F V)ˣ) : Module.End F V) * z *
      (u : Module.End F V))) :
    (u : Module.End F V) * X * ((u⁻¹ : (Module.End F V)ˣ) : Module.End F V) ∈
      elementAlgebra z := by
  have h := conj_mem_elementAlgebra u⁻¹ hX
  simp only [inv_inv, mul_assoc, Units.mul_inv_cancel_left] at h
  rwa [← mul_assoc, Units.mul_inv_cancel_right] at h

/-- Normalizing units are preserved by conjugation with a normalizing unit. -/
theorem normalizingUnits_conj {z : Module.End F V} (h : NormalizingUnits 𝓛 (elementAlgebra z))
    {u : (Module.End F V)ˣ} (hu : u ∈ 𝓛.stabilizer) :
    NormalizingUnits 𝓛
      (elementAlgebra (((u⁻¹ : (Module.End F V)ˣ) : Module.End F V) * z *
        (u : Module.End F V))) := by
  intro X hX hX0
  have hY := conj_mem_elementAlgebra' u hX
  have hY0 : (u : Module.End F V) * X * ((u⁻¹ : (Module.End F V)ˣ) : Module.End F V) ≠ 0 := by
    intro h0
    apply hX0
    have := congrArg (fun Z => ((u⁻¹ : (Module.End F V)ˣ) : Module.End F V) * Z * u) h0
    simpa [mul_assoc] using this
  obtain ⟨g, hg, hgs⟩ := h _ hY hY0
  refine ⟨u⁻¹ * g * u, ?_, 𝓛.stabilizer.mul_mem (𝓛.stabilizer.mul_mem
    (𝓛.stabilizer.inv_mem hu) hgs) hu⟩
  rw [Units.val_mul, Units.val_mul, hg]
  simp [mul_assoc]

/-- Directional approximation: every element of `K` lying in `𝔓^t` is congruent modulo `𝔓^{t+1}`
to an element of `K'`. The refinement proof uses this predicate in both directions. -/
def Approx (K K' : Set (Module.End F V)) : Prop :=
  ∀ X ∈ K, ∀ t : ℤ, X ∈ P t → ∃ Y ∈ K', X - Y ∈ P (t + 1)

theorem conj_sub_mem {g : (Module.End F V)ˣ} (hg1 : (g : Module.End F V) - 1 ∈ P 1)
    (hginv : ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) ∈ P 0) {t : ℤ}
    {Z : Module.End F V} (hZ : Z ∈ P t) :
    ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) * Z * g - Z ∈ P (t + 1) := by
  have h1 : ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) * g = 1 := Units.inv_mul g
  have heq : ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) * Z * g - Z =
      ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) *
        (Z * ((g : Module.End F V) - 1) - ((g : Module.End F V) - 1) * Z) := by
    calc ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) * Z * g - Z
        = ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) * Z * g -
            (((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) * g) * Z := by rw [h1, one_mul]
      _ = _ := by noncomm_ring
  rw [heq]
  have hc := commutator_mem_endFiltration 𝓛 hZ hg1
  have := 𝓛.mul_mem_endFiltration hginv hc
  rwa [zero_add] at this

theorem conj_mem {g : (Module.End F V)ˣ} (hg : (g : Module.End F V) ∈ P 0)
    (hginv : ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) ∈ P 0) {t : ℤ}
    {Z : Module.End F V} (hZ : Z ∈ P t) :
    ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) * Z * g ∈ P t := by
  have := 𝓛.mul_mem_endFiltration (𝓛.mul_mem_endFiltration hginv hZ) hg
  rwa [zero_add, add_zero] at this

/-- Approximation from the left survives conjugation of the first set by `g ∈ 1 + 𝔓`. -/
theorem approx_conj_left {K K' K'' : Set (Module.End F V)} (h : Approx 𝓛 K K')
    {g : (Module.End F V)ˣ} (hg1 : (g : Module.End F V) - 1 ∈ P 1)
    (hg : (g : Module.End F V) ∈ P 0)
    (hginv : ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) ∈ P 0)
    (hK : ∀ X ∈ K'', (g : Module.End F V) * X * ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) ∈ K) :
    Approx 𝓛 K'' K' := by
  intro X hX t hXt
  have hXt' : (g : Module.End F V) * X * ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) ∈ P t := by
    have := conj_mem 𝓛 (g := g⁻¹) (by simpa using hginv) (by simpa using hg) hXt
    simpa using this
  obtain ⟨Y, hY, hXY⟩ := h _ (hK X hX) t hXt'
  refine ⟨Y, hY, ?_⟩
  have hYt : Y ∈ P t := by
    have := sub_mem hXt' (𝓛.endFiltration_antitone (by omega) hXY)
    rwa [sub_sub_cancel] at this
  have h1 := conj_mem 𝓛 hg hginv hXY
  have h2 := conj_sub_mem 𝓛 hg1 hginv hYt
  have heq : X - Y = ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) *
      ((g : Module.End F V) * X * ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) - Y) * g +
      (((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) * Y * g - Y) := by
    have e1 : ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) *
        ((g : Module.End F V) * X * ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) - Y) * g =
        X - ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) * Y * g := by
      rw [mul_sub, sub_mul]
      congr 1
      simp [mul_assoc]
    rw [e1]
    abel
  rw [heq]
  exact add_mem h1 h2

/-- Approximation into a set survives conjugating the target by `g ∈ 1 + 𝔓`. -/
theorem approx_conj_right {K K' K'' : Set (Module.End F V)} (h : Approx 𝓛 K K')
    {g : (Module.End F V)ˣ} (hg1 : (g : Module.End F V) - 1 ∈ P 1)
    (hginv : ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) ∈ P 0)
    (hK : ∀ X ∈ K', ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) * X * g ∈ K'') :
    Approx 𝓛 K K'' := by
  intro X hX t hXt
  obtain ⟨Y, hY, hXY⟩ := h X hX t hXt
  refine ⟨_, hK Y hY, ?_⟩
  have hYt : Y ∈ P t := by
    have := sub_mem hXt (𝓛.endFiltration_antitone (by omega) hXY)
    rwa [sub_sub_cancel] at this
  have h2 := conj_sub_mem 𝓛 hg1 hginv hYt
  have heq : X - ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) * Y * g =
      (X - Y) - (((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) * Y * g - Y) := by abel
  rw [heq]
  exact sub_mem hXY h2

end Generated

end Langlands.BushnellKutzko
