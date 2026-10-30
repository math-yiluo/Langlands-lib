import Langlands.Representation.RankinSelberg.RankOneMatrixIwasawa
import Langlands.HarmonicAnalysis.PadicLatticeGeometryProof
import Langlands.HarmonicAnalysis.Conductor
import Langlands.Representation.Whittaker.GeneralLinear
import Langlands.Group.GL.Transvection

/-!
# The unipotent transform of a matrix Schwartz–Bruhat function

For a Schwartz–Bruhat function `Φ` on `(n+1) × (n+1)` matrices over a canonical
`p`-adic field and the standard character `θ`, the transform
`J(M) = ∫_N Φ(u M) θ(u) du` is defined for every matrix `M`. It is left
`(N, θ⁻¹)`-equivariant, inherits every right invariance of `Φ`, vanishes on
`diag(d) k` unless the diagonal `d` is bounded and its entries after the first are
bounded below, and is uniformly locally constant in the first diagonal entry.
-/

noncomputable section

open MeasureTheory Topology
open scoped NNReal ENNReal

namespace Langlands.RankinSelberg.RankOneIwasawa

open GeneralLinear HarmonicAnalysis Whittaker Conductor

universe uF

section Filtration

variable {X : Type*} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]

/-- A locally constant, compactly supported function on a topological additive group
with an exhaustive increasing filtration by open subgroups forming a neighborhood
basis of zero is supported in one member and invariant under another. -/
theorem exists_filtration_bounds (L : ℤ → AddSubgroup X) (hmono : Monotone L)
    (hopen : ∀ n, IsOpen (L n : Set X)) (hbasis : ∀ s ∈ 𝓝 (0 : X), ∃ n, (L n : Set X) ⊆ s)
    (hcover : ∀ x, ∃ n, x ∈ L n) (f : X → ℂ) (hf : IsLocallyConstant f)
    (hc : HasCompactSupport f) :
    (∃ R, ∀ x, f x ≠ 0 → x ∈ L R) ∧ (∃ c, ∀ x h, h ∈ L c → f (x + h) = f x) := by
  have hK : IsCompact (tsupport f) := hc.isCompact
  constructor
  · obtain ⟨R, hR⟩ := hK.elim_directed_cover (fun n => (L n : Set X)) hopen
      (fun x _ => Set.mem_iUnion.2 (hcover x))
      (directed_of_isDirected_le fun _ _ h => hmono h)
    exact ⟨R, fun x hx => hR (subset_tsupport f (Function.mem_support.2 hx))⟩
  · have hloc (x : X) : ∃ n : ℤ, ∀ d ∈ L n, f (x + d) = f x := by
      have hs : {d : X | f (x + d) = f x} ∈ 𝓝 (0 : X) :=
        ((hf.isOpen_fiber (f x)).preimage (continuous_const.add continuous_id)).mem_nhds
          (by simp)
      obtain ⟨n, hn⟩ := hbasis _ hs
      exact ⟨n, fun d hd => hn hd⟩
    choose n hn using hloc
    obtain ⟨t, -, htK⟩ := hK.elim_nhds_subcover
      (fun x => {z | z - x ∈ L (n x)})
      (fun x _ => ((hopen (n x)).preimage (continuous_id.sub continuous_const)).mem_nhds
        (by simp))
    obtain ⟨M, hM⟩ := Finset.exists_le (t.image fun x => -n x)
    refine ⟨-M, ?_⟩
    have hsupp : ∀ y ∈ tsupport f, ∀ h ∈ L (-M), f (y + h) = f y := by
      intro y hy h hh
      obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.mp (htK hy)
      have hyx : y - x ∈ L (n x) := hyx
      have hle : -M ≤ n x := by
        have := hM _ (Finset.mem_image_of_mem _ hx)
        omega
      have hh' := hmono hle hh
      have e1 := hn x (y - x) hyx
      have e2 := hn x (y + h - x) (by
        rw [show y + h - x = (y - x) + h by abel]
        exact (L (n x)).add_mem hyx hh')
      rw [show x + (y - x) = y by abel] at e1
      rw [show x + (y + h - x) = y + h by abel] at e2
      rw [e1, e2]
    intro y h hh
    by_cases hy : y ∈ tsupport f
    · exact hsupp y hy h hh
    by_cases hyh : y + h ∈ tsupport f
    · have := hsupp (y + h) hyh (-h) (neg_mem hh)
      rw [add_neg_cancel_right] at this
      exact this.symm
    · rw [image_eq_zero_of_notMem_tsupport hy, image_eq_zero_of_notMem_tsupport hyh]

end Filtration

section Lattice

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField

local notation "𝓛" => F.canonicalTopologicalData.additiveLattice

theorem lattice_mul {a b : ℤ} {x y : F.Carrier} (hx : x ∈ 𝓛 a) (hy : y ∈ 𝓛 b) :
    x * y ∈ 𝓛 (a + b) := by
  rw [PadicField.TopologicalData.mem_additiveLattice] at hx hy ⊢
  rw [map_mul, WithZero.exp_add]
  exact mul_le_mul' hx hy

theorem lattice_mono {a b : ℤ} (h : a ≤ b) {x : F.Carrier} (hx : x ∈ 𝓛 a) : x ∈ 𝓛 b :=
  F.canonicalTopologicalData.additiveLattice_mono h hx

theorem mem_lattice_zero_iff (x : F.Carrier) :
    x ∈ 𝓛 0 ↔ x ∈ (ValuativeRel.valuation F.Carrier).integer :=
  F.canonicalTopologicalData.mem_additiveLattice_zero x

theorem one_mem_lattice_zero : (1 : F.Carrier) ∈ 𝓛 0 :=
  (mem_lattice_zero_iff F 1).2 (one_mem _)

theorem exists_mem_lattice (x : F.Carrier) : ∃ n : ℤ, x ∈ 𝓛 n := by
  by_cases hx : x = 0
  · exact ⟨0, hx ▸ zero_mem _⟩
  · refine ⟨WithZero.log (F.canonicalTopologicalData.discreteValuation x), ?_⟩
    rw [PadicField.TopologicalData.mem_additiveLattice, WithZero.exp_log]
    exact (map_ne_zero _).2 hx

/-- An element outside a lattice has inverse in the opposite lattice. -/
theorem inv_mem_lattice_of_notMem {x : F.Carrier} {a : ℤ} (hx : x ∉ 𝓛 a) :
    x⁻¹ ∈ 𝓛 (-a) := by
  rw [PadicField.TopologicalData.mem_additiveLattice, not_le] at hx
  rw [PadicField.TopologicalData.mem_additiveLattice, map_inv₀, WithZero.exp_neg]
  exact (inv_le_inv₀ (zero_le.trans_lt hx) WithZero.exp_pos).2 hx.le

theorem isOpen_lattice (a : ℤ) : IsOpen (𝓛 a : Set F.Carrier) :=
  ((padicLatticeGeometry F F.canonicalTopologicalData).2 a).2

theorem isCompact_lattice (a : ℤ) : IsCompact (𝓛 a : Set F.Carrier) :=
  ((padicLatticeGeometry F F.canonicalTopologicalData).2 a).1

/-- Matrices with all entries in one lattice. -/
def matLattice (r : ℕ) (a : ℤ) : AddSubgroup (Matrix (Fin r) (Fin r) F.Carrier) where
  carrier := {Y | ∀ i j, Y i j ∈ 𝓛 a}
  zero_mem' := fun _ _ => zero_mem _
  add_mem' hY hZ := fun i j => add_mem (hY i j) (hZ i j)
  neg_mem' hY := fun i j => neg_mem (hY i j)

theorem mem_matLattice {r : ℕ} {a : ℤ} (Y : Matrix (Fin r) (Fin r) F.Carrier) :
    Y ∈ matLattice F r a ↔ ∀ i j, Y i j ∈ 𝓛 a := Iff.rfl

theorem matLattice_mono (r : ℕ) : Monotone (matLattice F r) :=
  fun _ _ h _ hY i j => lattice_mono F h (hY i j)

theorem matLattice_mul {r : ℕ} {a b : ℤ} {Y Z : Matrix (Fin r) (Fin r) F.Carrier}
    (hY : Y ∈ matLattice F r a) (hZ : Z ∈ matLattice F r b) :
    Y * Z ∈ matLattice F r (a + b) := by
  intro i j
  rw [Matrix.mul_apply]
  exact AddSubgroup.sum_mem _ fun l _ => lattice_mul F (hY i l) (hZ l j)

theorem matLattice_mul_integral {r : ℕ} {a : ℤ} {Y Z : Matrix (Fin r) (Fin r) F.Carrier}
    (hY : Y ∈ matLattice F r a) (hZ : Z ∈ matLattice F r 0) :
    Y * Z ∈ matLattice F r a := by
  simpa using matLattice_mul F hY hZ

theorem integral_mul_matLattice {r : ℕ} {a : ℤ} {Y Z : Matrix (Fin r) (Fin r) F.Carrier}
    (hY : Y ∈ matLattice F r 0) (hZ : Z ∈ matLattice F r a) :
    Y * Z ∈ matLattice F r a := by
  simpa using matLattice_mul F hY hZ

/-- Integral invertible matrices and their inverses have integral entries. -/
theorem integralSubgroup_mem_matLattice {n : ℕ} {k : Langlands.GeneralLinear (n + 1) F.Carrier}
    (hk : k ∈ integralSubgroup (ValuativeRel.valuation F.Carrier).integer n) :
    k.val ∈ matLattice F (n + 1) 0 ∧ (k⁻¹).val ∈ matLattice F (n + 1) 0 := by
  rw [mem_integralSubgroup] at hk
  exact ⟨fun i j => (mem_lattice_zero_iff F _).2 (hk.1 i j),
    fun i j => (mem_lattice_zero_iff F _).2 (hk.2 i j)⟩

theorem isOpen_matLattice (r : ℕ) (a : ℤ) :
    IsOpen (matLattice F r a : Set (Matrix (Fin r) (Fin r) F.Carrier)) := by
  have : (matLattice F r a : Set (Matrix (Fin r) (Fin r) F.Carrier)) =
      ⋂ i, ⋂ j, (fun Y : Matrix (Fin r) (Fin r) F.Carrier => Y i j) ⁻¹' (𝓛 a : Set F.Carrier) := by
    ext Y
    simp [mem_matLattice]
  rw [this]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    (isOpen_lattice F a).preimage ((continuous_apply j).comp (continuous_apply i))

theorem exists_lattice_subset {s : Set F.Carrier} (hs : s ∈ 𝓝 (0 : F.Carrier)) :
    ∃ n : ℤ, (𝓛 n : Set F.Carrier) ⊆ s :=
  F.canonicalTopologicalData.exists_additiveLattice_subset hs

theorem matLattice_basis (r : ℕ) {s : Set (Matrix (Fin r) (Fin r) F.Carrier)}
    (hs : s ∈ 𝓝 (0 : Matrix (Fin r) (Fin r) F.Carrier)) :
    ∃ n : ℤ, (matLattice F r n : Set (Matrix (Fin r) (Fin r) F.Carrier)) ⊆ s := by
  obtain ⟨U, hUs, hU, h0⟩ := mem_nhds_iff.1 hs
  obtain ⟨u, hu, huU⟩ := (isOpen_pi_iff'.1 hU) 0 h0
  have hrow : ∀ i, ∃ w : Fin r → Set F.Carrier, (∀ j, w j ∈ 𝓝 (0 : F.Carrier)) ∧
      Set.univ.pi w ⊆ u i := by
    intro i
    obtain ⟨w, hw, hwu⟩ := (isOpen_pi_iff'.1 (hu i).1) 0 (hu i).2
    exact ⟨w, fun j => (hw j).1.mem_nhds (hw j).2, hwu⟩
  choose w hw hwu using hrow
  have hent : ∀ i j, ∃ m : ℤ, (𝓛 m : Set F.Carrier) ⊆ w i j :=
    fun i j => exists_lattice_subset F (hw i j)
  choose m hm using hent
  obtain ⟨N, hN⟩ := Finset.exists_le
    (Finset.univ.image fun ij : Fin r × Fin r => -m ij.1 ij.2)
  refine ⟨-N, fun Y hY => hUs (huU fun i _ => hwu i fun j _ => hm i j ?_)⟩
  have := hN _ (Finset.mem_image_of_mem _ (Finset.mem_univ (i, j)))
  exact lattice_mono F (by simp only at this; omega) (hY i j)

theorem exists_mem_matLattice {r : ℕ} (Y : Matrix (Fin r) (Fin r) F.Carrier) :
    ∃ n : ℤ, Y ∈ matLattice F r n := by
  have hent : ∀ i j, ∃ m : ℤ, Y i j ∈ 𝓛 m := fun i j => exists_mem_lattice F (Y i j)
  choose m hm using hent
  obtain ⟨N, hN⟩ := Finset.exists_le
    (Finset.univ.image fun ij : Fin r × Fin r => m ij.1 ij.2)
  exact ⟨N, fun i j => lattice_mono F
    (hN _ (Finset.mem_image_of_mem _ (Finset.mem_univ (i, j)))) (hm i j)⟩

/-- A matrix Schwartz–Bruhat function is supported in one matrix lattice. -/
theorem schwartz_support_bound {r : ℕ} (Φ : SchwartzBruhat (Matrix (Fin r) (Fin r) F.Carrier)) :
    ∃ R : ℤ, ∀ X, Φ X ≠ 0 → X ∈ matLattice F r R :=
  (exists_filtration_bounds (matLattice F r) (matLattice_mono F r) (isOpen_matLattice F r)
    (fun _ hs => matLattice_basis F r hs) (exists_mem_matLattice F) Φ
    Φ.locallyConstant Φ.hasCompactSupport).1

/-- A matrix Schwartz–Bruhat function is invariant under one matrix lattice. -/
theorem schwartz_invariance {r : ℕ} (Φ : SchwartzBruhat (Matrix (Fin r) (Fin r) F.Carrier)) :
    ∃ c : ℤ, ∀ X Y, Y ∈ matLattice F r c → Φ (X + Y) = Φ X :=
  (exists_filtration_bounds (matLattice F r) (matLattice_mono F r) (isOpen_matLattice F r)
    (fun _ hs => matLattice_basis F r hs) (exists_mem_matLattice F) Φ
    Φ.locallyConstant Φ.hasCompactSupport).2

/-- A function on `F` invariant under one lattice and supported in another is
Schwartz–Bruhat. -/
def schwartzOfLattice (φ : F.Carrier → ℂ) (c R : ℤ)
    (hinv : ∀ x h, h ∈ 𝓛 c → φ (x + h) = φ x) (hsupp : ∀ x, φ x ≠ 0 → x ∈ 𝓛 R) :
    SchwartzBruhat F.Carrier :=
  ⟨φ, by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
    have hn : {y : F.Carrier | y - x ∈ 𝓛 c} ∈ 𝓝 x :=
      ((isOpen_lattice F c).preimage (continuous_id.sub continuous_const)).mem_nhds (by simp)
    filter_upwards [hn] with y hy
    simpa [add_sub_cancel] using hinv x (y - x) hy, by
    apply HasCompactSupport.intro (isCompact_lattice F R)
    intro x hx
    by_contra h
    exact hx (hsupp x h)⟩

@[simp] theorem schwartzOfLattice_apply (φ : F.Carrier → ℂ) (c R : ℤ) (hinv hsupp)
    (x : F.Carrier) : schwartzOfLattice F φ c R hinv hsupp x = φ x := rfl

end Lattice

section Transform

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance (m : ℕ) : MeasurableSpace (upperUnipotent (m + 1) F.Carrier) := borel _
local instance (m : ℕ) : BorelSpace (upperUnipotent (m + 1) F.Carrier) := ⟨rfl⟩

local notation "𝓛" => F.canonicalTopologicalData.additiveLattice

variable (ψ : UnitaryAdditiveCharacter F.Carrier) {n : ℕ}

/-- The unipotent transform `J(M) = ∫_N Φ(u M) θ(u) du` of a matrix test function,
for an arbitrary (possibly singular) matrix `M`. -/
def unipotentTransform (Φ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier))
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) : ℂ :=
  ∫ u, Φ ((u : Langlands.GeneralLinear (n + 1) F.Carrier).val * M) *
    (standardCharacter ψ n u : ℂ) ∂(unipotentHaar F.Carrier n)

/-- Left `(N, θ⁻¹)`-equivariance. -/
theorem unipotentTransform_unipotent_mul
    (Φ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier))
    (ν : upperUnipotent (n + 1) F.Carrier) (M : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) :
    unipotentTransform F ψ Φ ((ν : Langlands.GeneralLinear (n + 1) F.Carrier).val * M) =
      (((standardCharacter ψ n ν)⁻¹ : ℂˣ) : ℂ) * unipotentTransform F ψ Φ M := by
  unfold unipotentTransform
  have h := integral_mul_right_eq_self (μ := unipotentHaar F.Carrier n)
    (fun w : upperUnipotent (n + 1) F.Carrier =>
      Φ ((w : Langlands.GeneralLinear (n + 1) F.Carrier).val * M) *
        (standardCharacter ψ n (w * ν⁻¹) : ℂ)) ν
  simp only [mul_inv_cancel_right, Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc] at h
  rw [h, ← integral_const_mul]
  congr 1
  funext w
  rw [map_mul, map_inv, Units.val_mul]
  ring

/-- Right invariances of the test function pass to the transform. -/
theorem unipotentTransform_mul_right
    (Φ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier))
    (κ : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) (hκ : ∀ X, Φ (X * κ) = Φ X)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) :
    unipotentTransform F ψ Φ (M * κ) = unipotentTransform F ψ Φ M := by
  unfold unipotentTransform
  congr 1
  funext u
  rw [← Matrix.mul_assoc, hκ]

theorem exists_ne_zero_of_unipotentTransform_ne_zero
    {Φ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier)}
    {M : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier} (h : unipotentTransform F ψ Φ M ≠ 0) :
    ∃ u : upperUnipotent (n + 1) F.Carrier,
      Φ ((u : Langlands.GeneralLinear (n + 1) F.Carrier).val * M) ≠ 0 := by
  by_contra hc
  push Not at hc
  apply h
  unfold unipotentTransform
  simp [hc]

theorem castSucc_lt_succ' (i : Fin n) : i.castSucc < i.succ := Fin.castSucc_lt_succ

theorem one_add_single_apply {m : ℕ} (a b : Fin m) (t : F.Carrier) (x y : Fin m) :
    (1 + Matrix.single a b t : Matrix (Fin m) (Fin m) F.Carrier) x y =
      (if x = y then 1 else 0) + (if a = x ∧ b = y then t else 0) := by
  rw [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]

/-- The elementary unipotent matrix `1 + t E_{i, i+1}`. -/
def elemUnipotent (i : Fin n) (t : F.Carrier) : upperUnipotent (n + 1) F.Carrier :=
  ⟨transvectionUnit i.castSucc i.succ (castSucc_lt_succ' i).ne t, by
    refine ⟨fun x y hxy => ?_, fun x => ?_⟩
    · change (1 + Matrix.single i.castSucc i.succ t : Matrix _ _ F.Carrier) x y = 0
      rw [one_add_single_apply]
      have hxy' : y < x := hxy
      rw [ite_eq_right (ne_of_gt hxy'), ite_eq_right, add_zero]
      rintro ⟨rfl, rfl⟩
      exact absurd hxy' (not_lt.2 (castSucc_lt_succ' i).le)
    · change (1 + Matrix.single i.castSucc i.succ t : Matrix _ _ F.Carrier) x x = 1
      rw [one_add_single_apply, ite_eq_left rfl, ite_eq_right, add_zero]
      rintro ⟨rfl, h⟩
      exact (castSucc_lt_succ' i).ne h.symm⟩

theorem elemUnipotent_val (i : Fin n) (t : F.Carrier) :
    ((elemUnipotent F i t : upperUnipotent (n + 1) F.Carrier) :
      Langlands.GeneralLinear (n + 1) F.Carrier).val =
      1 + Matrix.single i.castSucc i.succ t := rfl

theorem standardCharacter_elemUnipotent (i : Fin n) (t : F.Carrier) :
    (standardCharacter ψ n (elemUnipotent F i t) : ℂ) = ψ.complex t := by
  rw [standardCharacter_apply]
  congr 1
  rw [Finset.sum_eq_single i]
  · change (1 + Matrix.single i.castSucc i.succ t : Matrix _ _ F.Carrier) i.castSucc i.succ = t
    rw [one_add_single_apply, ite_eq_right (castSucc_lt_succ' i).ne, ite_eq_left ⟨rfl, rfl⟩, zero_add]
  · intro m _ hm
    change (1 + Matrix.single i.castSucc i.succ t : Matrix _ _ F.Carrier) m.castSucc m.succ = 0
    rw [one_add_single_apply, ite_eq_right (castSucc_lt_succ' m).ne, ite_eq_right, zero_add]
    rintro ⟨h, -⟩
    exact hm (Fin.castSucc_injective _ h.symm)
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- If right translation by `1 + t E_{i,i+1}` with `ψ(t) ≠ 1` does not change the
integrand, the transform vanishes. -/
theorem unipotentTransform_eq_zero_of_shift
    (Φ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier))
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) (i : Fin n) (t : F.Carrier)
    (ht : ψ.complex t ≠ 1)
    (h : ∀ u : upperUnipotent (n + 1) F.Carrier,
      Φ (((u * elemUnipotent F i t : upperUnipotent (n + 1) F.Carrier) :
        Langlands.GeneralLinear (n + 1) F.Carrier).val * M) =
      Φ ((u : Langlands.GeneralLinear (n + 1) F.Carrier).val * M)) :
    unipotentTransform F ψ Φ M = 0 := by
  have hr := integral_mul_right_eq_self (μ := unipotentHaar F.Carrier n)
    (fun w : upperUnipotent (n + 1) F.Carrier =>
      Φ ((w : Langlands.GeneralLinear (n + 1) F.Carrier).val * M) *
        (standardCharacter ψ n w : ℂ)) (elemUnipotent F i t)
  simp only [h, map_mul, Units.val_mul, standardCharacter_elemUnipotent] at hr
  rw [show (∫ u, Φ ((u : Langlands.GeneralLinear (n + 1) F.Carrier).val * M) *
      ((standardCharacter ψ n u : ℂ) * ψ.complex t) ∂unipotentHaar F.Carrier n) =
      (∫ u, Φ ((u : Langlands.GeneralLinear (n + 1) F.Carrier).val * M) *
      (standardCharacter ψ n u : ℂ) ∂unipotentHaar F.Carrier n) * ψ.complex t by
    rw [← integral_mul_const]
    congr 1
    funext u
    ring] at hr
  have : unipotentTransform F ψ Φ M * (ψ.complex t - 1) = 0 := by
    unfold unipotentTransform
    rw [mul_sub, hr, mul_one, sub_self]
  rcases mul_eq_zero.1 this with h0 | h0
  · exact h0
  · exact absurd (sub_eq_zero.1 h0) ht

/-- A nontrivial character is nontrivial on some lattice. -/
theorem exists_lattice_nontrivial : ∃ b : ℤ, ∃ t ∈ 𝓛 b, ψ.complex t ≠ 1 := by
  obtain ⟨B, hB⟩ := F.canonicalTopologicalData.additiveTrivialAt_bddAbove ψ
  have hn : ¬ F.canonicalTopologicalData.AdditiveTrivialAt ψ (B + 1) := fun h => by
    have := hB _ h
    omega
  unfold PadicField.TopologicalData.AdditiveTrivialAt at hn
  push Not at hn
  obtain ⟨x, hx, hψ⟩ := hn
  refine ⟨B + 1, x, hx, fun h => hψ ?_⟩
  rw [UnitaryAdditiveCharacter.complex_apply] at h
  exact Subtype.ext h

/-- Entries of the first column of an upper unipotent matrix. -/
theorem unipotent_col_zero (u : upperUnipotent (n + 1) F.Carrier) (a : Fin (n + 1)) :
    (u : Langlands.GeneralLinear (n + 1) F.Carrier).val a 0 = if a = 0 then 1 else 0 := by
  split_ifs with ha
  · subst ha
    exact UpperUnipotent.entry_diag u 0
  · exact UpperUnipotent.entry_eq_zero u (Fin.pos_of_ne_zero ha)

/-- An upper unipotent matrix fixes the corner matrix unit on the left. -/
theorem unipotent_mul_single_zero (u : upperUnipotent (n + 1) F.Carrier) (η : F.Carrier) :
    (u : Langlands.GeneralLinear (n + 1) F.Carrier).val * Matrix.single 0 0 η =
      Matrix.single 0 0 η := by
  ext a b
  by_cases hb : b = 0
  · subst hb
    rw [Matrix.mul_single_apply_same, unipotent_col_zero]
    by_cases ha : a = 0
    · subst ha
      simp
    · rw [Matrix.single_apply_of_ne]
      · simp [ha]
      · rintro ⟨h, -⟩
        exact ha h.symm
  · rw [Matrix.mul_single_apply_of_ne (hbj := hb), Matrix.single_apply_of_ne]
    rintro ⟨-, h⟩
    exact hb h.symm

section Bounds

variable {Φ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier)}

/-- If `Φ(A k) ≠ 0` with `k` integral, then `A` lies in the support lattice. -/
theorem mem_matLattice_of_support {R : ℤ} (hR : ∀ X, Φ X ≠ 0 → X ∈ matLattice F (n + 1) R)
    {k : Langlands.GeneralLinear (n + 1) F.Carrier}
    (hk : k ∈ integralSubgroup (ValuativeRel.valuation F.Carrier).integer n)
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier} (h : Φ (A * k.val) ≠ 0) :
    A ∈ matLattice F (n + 1) R := by
  have h1 := hR _ h
  have : A = (A * k.val) * (k⁻¹).val := by
    rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  rw [this]
  exact matLattice_mul_integral F h1 (integralSubgroup_mem_matLattice F hk).2

/-- Column `j` of every unipotent `u` with `Φ(u M) ≠ 0` lies in the lattice of level `B`. -/
def ColBound (Φ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier))
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) (j : Fin (n + 1)) (B : ℤ) : Prop :=
  ∀ u : upperUnipotent (n + 1) F.Carrier,
    Φ ((u : Langlands.GeneralLinear (n + 1) F.Carrier).val * M) ≠ 0 →
      ∀ a, (u : Langlands.GeneralLinear (n + 1) F.Carrier).val a j ∈ 𝓛 B

theorem colBound_zero (M : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) :
    ColBound F Φ M 0 0 := by
  intro u _ a
  rw [unipotent_col_zero]
  split_ifs
  · exact one_mem_lattice_zero F
  · exact zero_mem _

theorem colBound_of_inv {R : ℤ} (hR : ∀ X, Φ X ≠ 0 → X ∈ matLattice F (n + 1) R)
    (d : Fin (n + 1) → F.Carrierˣ) {k : Langlands.GeneralLinear (n + 1) F.Carrier}
    (hk : k ∈ integralSubgroup (ValuativeRel.valuation F.Carrier).integer n)
    (j : Fin (n + 1)) (e : ℤ) (he : ((d j : F.Carrier))⁻¹ ∈ 𝓛 e) :
    ColBound F Φ (Matrix.diagonal (fun i => (d i : F.Carrier)) * k.val) j (R + e) := by
  intro u hu a
  have hA := mem_matLattice_of_support F hR hk
    (A := (u : Langlands.GeneralLinear (n + 1) F.Carrier).val *
      Matrix.diagonal (fun i => (d i : F.Carrier))) (by rwa [Matrix.mul_assoc])
  have h1 := hA a j
  rw [Matrix.mul_diagonal] at h1
  have h2 : (u : Langlands.GeneralLinear (n + 1) F.Carrier).val a j =
      ((u : Langlands.GeneralLinear (n + 1) F.Carrier).val a j * (d j : F.Carrier)) *
        ((d j : F.Carrier))⁻¹ := by
    rw [mul_assoc, mul_inv_cancel₀ (d j).ne_zero, mul_one]
  rw [h2]
  exact lattice_mul F h1 he

/-- The inductive step of the lower bound: a bounded column forces the next
diagonal entry away from zero when the transform does not vanish. -/
theorem inv_mem_of_colBound {c b : ℤ} (hc : ∀ X Y, Y ∈ matLattice F (n + 1) c → Φ (X + Y) = Φ X)
    {t : F.Carrier} (htb : t ∈ 𝓛 b) (ht : ψ.complex t ≠ 1)
    (d : Fin (n + 1) → F.Carrierˣ) {k : Langlands.GeneralLinear (n + 1) F.Carrier}
    (hk : k ∈ integralSubgroup (ValuativeRel.valuation F.Carrier).integer n)
    (i : Fin n) (B : ℤ)
    (hcol : ColBound F Φ (Matrix.diagonal (fun j => (d j : F.Carrier)) * k.val) i.castSucc B)
    (hJ : unipotentTransform F ψ Φ (Matrix.diagonal (fun j => (d j : F.Carrier)) * k.val) ≠ 0) :
    ((d i.succ : F.Carrier))⁻¹ ∈ 𝓛 (B + b - c) := by
  set M := Matrix.diagonal (fun j => (d j : F.Carrier)) * k.val with hM
  by_contra hnot
  apply hJ
  have hd : (d i.succ : F.Carrier) ∈ 𝓛 (c - b - B) := by
    by_contra h'
    apply hnot
    have := inv_mem_lattice_of_notMem F h'
    rwa [show -(c - b - B) = B + b - c by ring] at this
  -- the perturbation produced by `1 + t E_{i,i+1}`
  have hY : ∀ w : upperUnipotent (n + 1) F.Carrier,
      (∀ a, (w : Langlands.GeneralLinear (n + 1) F.Carrier).val a i.castSucc ∈ 𝓛 B) →
      ((w : Langlands.GeneralLinear (n + 1) F.Carrier).val *
        Matrix.single i.castSucc i.succ t) * M ∈ matLattice F (n + 1) c := by
    intro w hw
    rw [hM, ← Matrix.mul_assoc]
    refine matLattice_mul_integral F (fun a j => ?_) (integralSubgroup_mem_matLattice F hk).1
    rw [Matrix.mul_diagonal]
    by_cases hj : j = i.succ
    · subst hj
      rw [Matrix.mul_single_apply_same]
      have := lattice_mul F (lattice_mul F (hw a) htb) hd
      rwa [show B + b + (c - b - B) = c by ring] at this
    · rw [Matrix.mul_single_apply_of_ne (hbj := hj), zero_mul]
      exact zero_mem _
  have hcolEq : ∀ (w : upperUnipotent (n + 1) F.Carrier) (a : Fin (n + 1)),
      ((w * elemUnipotent F i t : upperUnipotent (n + 1) F.Carrier) :
        Langlands.GeneralLinear (n + 1) F.Carrier).val a i.castSucc =
      (w : Langlands.GeneralLinear (n + 1) F.Carrier).val a i.castSucc := by
    intro w a
    rw [Subgroup.coe_mul, Units.val_mul, elemUnipotent_val, Matrix.mul_add, Matrix.mul_one,
      Matrix.add_apply, Matrix.mul_single_apply_of_ne (hbj := (castSucc_lt_succ' i).ne),
      add_zero]
  apply unipotentTransform_eq_zero_of_shift F ψ Φ M i t ht
  intro u
  have hsplit : ((u * elemUnipotent F i t : upperUnipotent (n + 1) F.Carrier) :
      Langlands.GeneralLinear (n + 1) F.Carrier).val * M =
      (u : Langlands.GeneralLinear (n + 1) F.Carrier).val * M +
        ((u : Langlands.GeneralLinear (n + 1) F.Carrier).val *
          Matrix.single i.castSucc i.succ t) * M := by
    rw [Subgroup.coe_mul, Units.val_mul, elemUnipotent_val, Matrix.mul_add, Matrix.mul_one,
      Matrix.add_mul]
  by_cases h1 : Φ ((u : Langlands.GeneralLinear (n + 1) F.Carrier).val * M) ≠ 0
  · rw [hsplit]
    exact hc _ _ (hY u (hcol u h1))
  · by_cases h2 : Φ (((u * elemUnipotent F i t : upperUnipotent (n + 1) F.Carrier) :
        Langlands.GeneralLinear (n + 1) F.Carrier).val * M) ≠ 0
    · rw [hsplit]
      exact hc _ _ (hY u fun a => (hcolEq u a) ▸ hcol _ h2 a)
    · push Not at h1 h2
      rw [h1, h2]

/-- **Support of the transform on `diag(d) k`.** There are levels `R` and `E` such that
`J(diag(d) k) ≠ 0` for integral `k` forces every `dᵢ` into the lattice of level `R` and
every inverse `dᵢ⁻¹` with `i ≥ 1` into the lattice of level `E`. -/
theorem unipotentTransform_diag_bounds
    (Φ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier)) :
    ∃ R E : ℤ, ∀ (d : Fin (n + 1) → F.Carrierˣ) (k : Langlands.GeneralLinear (n + 1) F.Carrier),
      k ∈ integralSubgroup (ValuativeRel.valuation F.Carrier).integer n →
      unipotentTransform F ψ Φ (Matrix.diagonal (fun j => (d j : F.Carrier)) * k.val) ≠ 0 →
        (∀ j, (d j : F.Carrier) ∈ 𝓛 R) ∧ ∀ i : Fin n, ((d i.succ : F.Carrier))⁻¹ ∈ 𝓛 E := by
  obtain ⟨R, hR⟩ := schwartz_support_bound F Φ
  obtain ⟨c, hc⟩ := schwartz_invariance F Φ
  obtain ⟨b, t, htb, ht⟩ := exists_lattice_nontrivial F ψ
  set S : ℤ := |b - c| + |R| with hS
  have hS0 : 0 ≤ S := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hbc : b - c ≤ S := (le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _))
  have hRbc : R + b - c ≤ S := by
    have h1 := le_abs_self R
    have h2 := le_abs_self (b - c)
    linarith
  refine ⟨R, n * S, ?_⟩
  intro d k hk hJ
  constructor
  · intro j
    obtain ⟨u, hu⟩ := exists_ne_zero_of_unipotentTransform_ne_zero F ψ hJ
    have hA := mem_matLattice_of_support F hR hk
      (A := (u : Langlands.GeneralLinear (n + 1) F.Carrier).val *
        Matrix.diagonal (fun i => (d i : F.Carrier))) (by rwa [Matrix.mul_assoc])
    have := hA j j
    rwa [Matrix.mul_diagonal, UpperUnipotent.entry_diag, one_mul] at this
  · have key : ∀ m (hm : m < n), ((d (⟨m, hm⟩ : Fin n).succ : F.Carrier))⁻¹ ∈
        𝓛 (((m : ℤ) + 1) * S) := by
      intro m
      induction m with
      | zero =>
        intro hm
        have h0 := inv_mem_of_colBound F ψ hc htb ht d hk ⟨0, hm⟩ 0
          (colBound_zero F _) hJ
        exact lattice_mono F (by simpa using hbc) h0
      | succ m ih =>
        intro hm
        have ih' := ih (by omega)
        have hcol := colBound_of_inv F hR d hk _ _ ih'
        have hcol' : ColBound F Φ (Matrix.diagonal (fun j => (d j : F.Carrier)) * k.val)
            (⟨m + 1, hm⟩ : Fin n).castSucc (R + ((m : ℤ) + 1) * S) := hcol
        have h1 := inv_mem_of_colBound F ψ hc htb ht d hk ⟨m + 1, hm⟩ _ hcol' hJ
        refine lattice_mono F ?_ h1
        push_cast
        linarith
    intro i
    refine lattice_mono F ?_ (key i.val i.isLt)
    have hi : ((i.val : ℤ) + 1) ≤ n := by exact_mod_cast i.isLt
    nlinarith

/-- **The corner transform is Schwartz.** For fixed `a` and integral `k`, the function
`x ↦ J(diag(x, a) k)` on `F` (including `x = 0`) is Schwartz–Bruhat. -/
theorem exists_cornerSchwartz
    (Φ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier)) (a : Fin n → F.Carrier)
    {k : Langlands.GeneralLinear (n + 1) F.Carrier}
    (hk : k ∈ integralSubgroup (ValuativeRel.valuation F.Carrier).integer n) :
    ∃ φ : SchwartzBruhat F.Carrier, ∀ x,
      φ x = unipotentTransform F ψ Φ (Matrix.diagonal (Fin.cons x a) * k.val) := by
  obtain ⟨R, hR⟩ := schwartz_support_bound F Φ
  obtain ⟨c, hc⟩ := schwartz_invariance F Φ
  have hdiag : ∀ x h : F.Carrier, Matrix.diagonal (Fin.cons (x + h) a) =
      Matrix.diagonal (Fin.cons x a) + Matrix.single 0 0 h := by
    intro x h
    ext i j
    by_cases hij : i = j
    · subst hij
      induction i using Fin.cases with
      | zero => simp
      | succ i =>
        simp only [Matrix.add_apply, Matrix.diagonal_apply_eq, Fin.cons_succ]
        rw [Matrix.single_apply_of_ne, add_zero]
        rintro ⟨h1, -⟩
        exact Fin.succ_ne_zero i h1.symm
    · rw [Matrix.add_apply, Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ hij,
        Matrix.single_apply_of_ne, add_zero]
      rintro ⟨rfl, rfl⟩
      exact hij rfl
  refine ⟨schwartzOfLattice F (fun x => unipotentTransform F ψ Φ
    (Matrix.diagonal (Fin.cons x a) * k.val)) c R ?_ ?_, fun x => rfl⟩
  · intro x h hh
    show unipotentTransform F ψ Φ (Matrix.diagonal (Fin.cons (x + h) a) * k.val) =
      unipotentTransform F ψ Φ (Matrix.diagonal (Fin.cons x a) * k.val)
    rw [hdiag, Matrix.add_mul]
    unfold unipotentTransform
    congr 1
    funext u
    rw [Matrix.mul_add, ← Matrix.mul_assoc _ (Matrix.single 0 0 h), unipotent_mul_single_zero,
      hc]
    intro i j
    rw [Matrix.mul_apply]
    refine AddSubgroup.sum_mem _ fun l _ => ?_
    by_cases hil : i = 0 ∧ l = 0
    · obtain ⟨rfl, rfl⟩ := hil
      rw [Matrix.single_apply_same]
      have := lattice_mul F hh
        ((integralSubgroup_mem_matLattice F hk).1 0 j)
      simpa using this
    · rw [Matrix.single_apply_of_ne, zero_mul]
      · exact zero_mem _
      · rintro ⟨h1, h2⟩
        exact hil ⟨h1.symm, h2.symm⟩
  · intro x hx
    obtain ⟨u, hu⟩ := exists_ne_zero_of_unipotentTransform_ne_zero F ψ hx
    have hA := mem_matLattice_of_support F hR hk
      (A := (u : Langlands.GeneralLinear (n + 1) F.Carrier).val * Matrix.diagonal (Fin.cons x a))
      (by rwa [Matrix.mul_assoc])
    have := hA 0 0
    rwa [Matrix.mul_diagonal, UpperUnipotent.entry_diag, one_mul, Fin.cons_zero] at this

end Bounds

end Transform

section Congruence

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField

local notation "𝓛" => F.canonicalTopologicalData.additiveLattice

theorem mul_sub_one_mem {r : ℕ} {a : ℤ} (ha : a ≤ 0) {A B : Matrix (Fin r) (Fin r) F.Carrier}
    (hA : A - 1 ∈ matLattice F r a) (hB : B - 1 ∈ matLattice F r a) :
    A * B - 1 ∈ matLattice F r a := by
  have h : A * B - 1 = (A - 1) * (B - 1) + (A - 1) + (B - 1) := by noncomm_ring
  rw [h]
  refine add_mem (add_mem ?_ hA) hB
  exact matLattice_mono F r (by omega) (matLattice_mul F hA hB)

/-- The congruence subgroup of level `m`: `k - 1` and `k⁻¹ - 1` have entries in `πᵐ O`. -/
def congruenceGroup (n m : ℕ) : Subgroup (Langlands.GeneralLinear (n + 1) F.Carrier) where
  carrier := {k | k.val - 1 ∈ matLattice F (n + 1) (-(m : ℤ)) ∧
    (k⁻¹).val - 1 ∈ matLattice F (n + 1) (-(m : ℤ))}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul]
      exact mul_sub_one_mem F (by omega) ha.1 hb.1
    · rw [mul_inv_rev, Units.val_mul]
      exact mul_sub_one_mem F (by omega) hb.2 ha.2
  inv_mem' {a} ha := ⟨ha.2, by simpa using ha.1⟩

theorem mem_congruenceGroup {n m : ℕ} (k : Langlands.GeneralLinear (n + 1) F.Carrier) :
    k ∈ congruenceGroup F n m ↔ k.val - 1 ∈ matLattice F (n + 1) (-(m : ℤ)) ∧
      (k⁻¹).val - 1 ∈ matLattice F (n + 1) (-(m : ℤ)) := Iff.rfl

theorem one_add_mem_lattice_zero {r : ℕ} {a : ℤ} (ha : a ≤ 0)
    {A : Matrix (Fin r) (Fin r) F.Carrier} (hA : A - 1 ∈ matLattice F r a) :
    A ∈ matLattice F r 0 := by
  intro i j
  have : A i j = (A - 1) i j + (1 : Matrix (Fin r) (Fin r) F.Carrier) i j := by simp
  rw [this]
  refine add_mem (lattice_mono F ha (hA i j)) ?_
  rw [Matrix.one_apply]
  split_ifs
  · exact one_mem_lattice_zero F
  · exact zero_mem _

theorem congruenceGroup_le_integral (n m : ℕ) :
    congruenceGroup F n m ≤ integralSubgroup (ValuativeRel.valuation F.Carrier).integer n := by
  intro k hk
  rw [mem_integralSubgroup]
  have h1 := one_add_mem_lattice_zero F (by omega) hk.1
  have h2 := one_add_mem_lattice_zero F (by omega) hk.2
  exact ⟨fun i j => (mem_lattice_zero_iff F _).1 (h1 i j),
    fun i j => (mem_lattice_zero_iff F _).1 (h2 i j)⟩

/-- The congruence subgroups are normalized by the integral subgroup. -/
theorem conj_mem_congruenceGroup {n m : ℕ} {k κ : Langlands.GeneralLinear (n + 1) F.Carrier}
    (hk : k ∈ integralSubgroup (ValuativeRel.valuation F.Carrier).integer n)
    (hκ : κ ∈ congruenceGroup F n m) : k⁻¹ * κ * k ∈ congruenceGroup F n m := by
  obtain ⟨hk1, hk2⟩ := integralSubgroup_mem_matLattice F hk
  have hkk : (k⁻¹).val * k.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  refine ⟨?_, ?_⟩
  · have : (k⁻¹ * κ * k).val - 1 = (k⁻¹).val * (κ.val - 1) * k.val := by
      rw [Units.val_mul, Units.val_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hkk]
    rw [this]
    exact matLattice_mul_integral F (integral_mul_matLattice F hk2 hκ.1) hk1
  · have : ((k⁻¹ * κ * k)⁻¹).val - 1 = (k⁻¹).val * ((κ⁻¹).val - 1) * k.val := by
      rw [mul_inv_rev, mul_inv_rev, inv_inv, ← mul_assoc, Units.val_mul, Units.val_mul,
        Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hkk]
    rw [this]
    exact matLattice_mul_integral F (integral_mul_matLattice F hk2 hκ.2) hk1

theorem isOpen_congruenceGroup (n m : ℕ) :
    IsOpen (congruenceGroup F n m : Set (Langlands.GeneralLinear (n + 1) F.Carrier)) := by
  have hS : IsOpen {A : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier |
      A - 1 ∈ matLattice F (n + 1) (-(m : ℤ))} :=
    (isOpen_matLattice F (n + 1) _).preimage (continuous_id.sub continuous_const)
  exact (hS.preimage Units.continuous_val).inter (hS.preimage Units.continuous_coe_inv)

/-- Every open subgroup contains a congruence subgroup. -/
theorem exists_congruenceGroup_le {n : ℕ} (H : Subgroup (Langlands.GeneralLinear (n + 1) F.Carrier))
    (hH : IsOpen (H : Set (Langlands.GeneralLinear (n + 1) F.Carrier))) :
    ∃ m : ℕ, congruenceGroup F n m ≤ H := by
  have hmem : (H : Set (Langlands.GeneralLinear (n + 1) F.Carrier)) ∈ 𝓝 1 :=
    hH.mem_nhds H.one_mem
  rw [Units.isInducing_embedProduct.nhds_eq_comap, Filter.mem_comap] at hmem
  obtain ⟨t, ht, htH⟩ := hmem
  rw [map_one, Prod.one_eq_mk, nhds_prod_eq, Filter.mem_prod_iff] at ht
  obtain ⟨t1, ht1, t2, ht2, ht12⟩ := ht
  have ht2' : MulOpposite.op ⁻¹' t2 ∈ 𝓝 (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) :=
    MulOpposite.continuous_op.continuousAt.preimage_mem_nhds ht2
  have hshift : ∀ {s : Set (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier)}, s ∈ 𝓝 1 →
      (fun Y => 1 + Y) ⁻¹' s ∈ 𝓝 (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) := by
    intro s hs
    apply (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds
    simpa using hs
  obtain ⟨N1, hN1⟩ := matLattice_basis F (n + 1) (hshift ht1)
  obtain ⟨N2, hN2⟩ := matLattice_basis F (n + 1) (hshift ht2')
  refine ⟨(max (-N1) (-N2)).toNat, fun k hk => htH (ht12 ⟨?_, ?_⟩)⟩
  · have h := hN1 (matLattice_mono F (n + 1) (by omega) hk.1)
    simpa using h
  · have h := hN2 (matLattice_mono F (n + 1) (by omega) hk.2)
    simpa using h

/-- Right invariance of a matrix Schwartz–Bruhat function under deep congruence subgroups. -/
theorem exists_schwartz_congruence {n : ℕ}
    (Φ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier)) :
    ∃ m₀ : ℕ, ∀ m, m₀ ≤ m → ∀ κ ∈ congruenceGroup F n m, ∀ X, Φ (X * κ.val) = Φ X := by
  obtain ⟨R, hR⟩ := schwartz_support_bound F Φ
  obtain ⟨c, hc⟩ := schwartz_invariance F Φ
  refine ⟨(R - c).toNat, fun m hm κ hκ X => ?_⟩
  have hlev : R + -(m : ℤ) ≤ c := by omega
  by_cases h1 : Φ X ≠ 0
  · have hX := hR X h1
    have : X * κ.val = X + X * (κ.val - 1) := by
      rw [Matrix.mul_sub, Matrix.mul_one, add_sub_cancel]
    rw [this]
    exact hc _ _ (matLattice_mono F (n + 1) hlev (matLattice_mul F hX hκ.1))
  · by_cases h2 : Φ (X * κ.val) ≠ 0
    · have hX := hR _ h2
      have : X = X * κ.val + X * κ.val * ((κ⁻¹).val - 1) := by
        rw [Matrix.mul_sub, Matrix.mul_one, add_sub_cancel, Matrix.mul_assoc, ← Units.val_mul,
          mul_inv_cancel, Units.val_one, Matrix.mul_one]
      conv_rhs => rw [this]
      exact (hc _ _ (matLattice_mono F (n + 1) hlev (matLattice_mul F hX hκ.2))).symm
    · push Not at h1 h2
      rw [h1, h2]

end Congruence

end Langlands.RankinSelberg.RankOneIwasawa
