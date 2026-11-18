import Langlands.LinearAlgebra.FreudenthalCasimirCoreStatement
import Langlands.LinearAlgebra.TraceFormCasimir

/-! # The Casimir element of a weight-graded Lie algebra of endomorphisms

For a Lie algebra `g` of endomorphisms of a weight-graded space satisfying the hypotheses of
`FreudenthalCasimirCoreStatement`, this module shows that the trace form is nondegenerate on
`g`, constructs dual families of `g` (torus elements and root vectors), and shows that the
resulting Casimir element commutes with `g` and preserves every weight space. -/

noncomputable section

open Module Function Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

namespace Langlands.LinearAlgebra.FreudenthalCasimir

open WeightGraded

section Dual

variable {k U : Type*} [Field k] [AddCommGroup U] [Module k U]

/-- Expansion in the first family of a pair of dual families, from nondegeneracy. -/
theorem eq_sum_trace_mul_smul {κ : Type*} [Fintype κ] [DecidableEq κ]
    (g : Submodule k (Module.End k U)) (b d : κ → Module.End k U)
    (hdual : ∀ a c, LinearMap.trace k U (b a * d c) = if a = c then 1 else 0)
    (hspan : g ≤ Submodule.span k (Set.range d)) (hb : ∀ a, b a ∈ g)
    (hrad : ∀ x ∈ g, (∀ z ∈ g, LinearMap.trace k U (x * z) = 0) → x = 0)
    {v : Module.End k U} (hv : v ∈ g) :
    v = ∑ a, LinearMap.trace k U (v * d a) • b a := by
  set w := v - ∑ a, LinearMap.trace k U (v * d a) • b a with hw
  have hwg : w ∈ g := g.sub_mem hv (g.sum_mem fun a _ => g.smul_mem _ (hb a))
  have hd : ∀ c, LinearMap.trace k U (w * d c) = 0 := by
    intro c
    rw [hw, sub_mul, map_sub, Finset.sum_mul, map_sum]
    simp [hdual]
  have hz : ∀ z ∈ Submodule.span k (Set.range d), LinearMap.trace k U (w * z) = 0 := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨c, rfl⟩ := hz
      exact hd c
    | zero => simp
    | add z z' _ _ h h' => rw [mul_add, map_add, h, h', add_zero]
    | smul c z _ h => rw [mul_smul_comm, map_smul, h, smul_zero]
  have h0 := hrad w hwg fun z hz' => hz z (hspan hz')
  rwa [hw, sub_eq_zero] at h0

/-- Expansion in the second family of a pair of dual families, from nondegeneracy. -/
theorem eq_sum_trace_mul_smul' {κ : Type*} [Fintype κ] [DecidableEq κ]
    (g : Submodule k (Module.End k U)) (b d : κ → Module.End k U)
    (hdual : ∀ a c, LinearMap.trace k U (b a * d c) = if a = c then 1 else 0)
    (hspan : g ≤ Submodule.span k (Set.range b)) (hd : ∀ a, d a ∈ g)
    (hrad : ∀ x ∈ g, (∀ z ∈ g, LinearMap.trace k U (x * z) = 0) → x = 0)
    {v : Module.End k U} (hv : v ∈ g) :
    v = ∑ a, LinearMap.trace k U (b a * v) • d a := by
  set w := v - ∑ a, LinearMap.trace k U (b a * v) • d a with hw
  have hwg : w ∈ g := g.sub_mem hv (g.sum_mem fun a _ => g.smul_mem _ (hd a))
  have hb : ∀ c, LinearMap.trace k U (b c * w) = 0 := by
    intro c
    rw [hw, mul_sub, map_sub, Finset.mul_sum, map_sum]
    simp [hdual]
  have hz : ∀ z ∈ Submodule.span k (Set.range b), LinearMap.trace k U (w * z) = 0 := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨c, rfl⟩ := hz
      rw [LinearMap.trace_mul_comm]
      exact hb c
    | zero => simp
    | add z z' _ _ h h' => rw [mul_add, map_add, h, h', add_zero]
    | smul c z _ h => rw [mul_smul_comm, map_smul, h, smul_zero]
  have h0 := hrad w hwg fun z hz' => hz z (hspan hz')
  rwa [hw, sub_eq_zero] at h0

end Dual

theorem mul_mem_shift' {k U X : Type*} [Field k] [AddCommGroup U] [Module k U] [AddCommGroup X]
    {W : X → Submodule k U} {χ χ' ψ : X} {f f' : Module.End k U} (hf : f ∈ shift W χ)
    (hf' : f' ∈ shift W χ') (h : χ + χ' = ψ) : f * f' ∈ shift W ψ :=
  h ▸ mul_mem_shift hf hf'

section Graded

variable {k : Type*} [Field k] {U : Type*} [AddCommGroup U] [Module k U]
  {X : Type*} [AddCommGroup X]
  {Y : Type*} [AddCommGroup Y] {ι : Type*} {J : Type*}

/-- The hypotheses of `FreudenthalCasimirCoreStatement` on the graded Lie algebra `g`. -/
structure Hyp (P : X →ₗ[ℤ] Y →ₗ[ℤ] ℤ) (W : X → Submodule k U)
    (g : LieSubalgebra k (Module.End k U)) (root : J → X) : Prop where
  indep : iSupIndep W
  iSup_eq_top : ⨆ μ, W μ = ⊤
  le_iSup : g.toSubmodule ≤ ⨆ χ, g.toSubmodule ⊓ shift W χ
  exists_torus : ∀ y : Y, ∃ x ∈ g, IsScalarOn W (fun μ => ((P μ y : ℤ) : k)) x
  zero_le_span : g.toSubmodule ⊓ shift W 0 ≤
    Submodule.span k {x | ∃ y : Y, IsScalarOn W (fun μ => ((P μ y : ℤ) : k)) x}
  eq_bot : ∀ χ : X, χ ≠ 0 → χ ∉ Set.range root → g.toSubmodule ⊓ shift W χ = ⊥
  finrank_root : ∀ j : J, finrank k ↥(g.toSubmodule ⊓ shift W (root j)) = 1
  faithful : ∀ y : Y, y ≠ 0 → ∃ μ : X, W μ ≠ ⊥ ∧ P μ y ≠ 0
  root_ne_zero : ∀ j : J, root j ≠ 0
  root_injective : Function.Injective root
  exists_neg : ∀ j : J, ∃ j' : J, root j' = -root j
  nilpotent_ideal :
    ∀ I : LieIdeal k g, (∀ x ∈ I, IsNilpotent ((x : g) : Module.End k U)) → I = ⊥

/-- The weight multiplicities. -/
def mult (W : X → Submodule k U) : X → ℕ := fun ν => finrank k ↥(W ν)

variable [Fintype ι] [DecidableEq ι]

/-- The coordinates `⟨μ, y_j⟩` in `k`. -/
def ck (k : Type*) [Field k] (P : X →ₗ[ℤ] Y →ₗ[ℤ] ℤ) (yb : Basis ι ℤ Y) (μ : X) : ι → k :=
  fun j => ((P μ (yb j) : ℤ) : k)

variable [CharZero k]

/-- The Gram matrix in `k`. -/
def Mk (P : X →ₗ[ℤ] Y →ₗ[ℤ] ℤ) (yb : Basis ι ℤ Y) (W : X → Submodule k U) : Matrix ι ι k :=
  (Rat.castHom k).mapMatrix (GramDual.gram P yb (mult W))

/-- The inverse Gram matrix in `k`. -/
def Mik (P : X →ₗ[ℤ] Y →ₗ[ℤ] ℤ) (yb : Basis ι ℤ Y) (W : X → Submodule k U) : Matrix ι ι k :=
  (Rat.castHom k).mapMatrix (GramDual.gram P yb (mult W))⁻¹

variable {P : X →ₗ[ℤ] Y →ₗ[ℤ] ℤ} (yb : Basis ι ℤ Y) {W : X → Submodule k U}
  {g : LieSubalgebra k (Module.End k U)} {root : J → X}

omit [Fintype ι] [DecidableEq ι] [CharZero k] in
theorem coord_cast (μ : X) (j : ι) :
    ((GramDual.coord P yb μ j : ℚ) : k) = ck k P yb μ j := by
  simp [GramDual.coord_apply, ck]

namespace Hyp

variable [FiniteDimensional k U] (h : Hyp P W g root)
include h

omit [CharZero k] in
theorem finite_mult : (support (mult W)).Finite := by
  refine (finite_ne_bot h.indep).subset fun ν hν => ?_
  intro hbot
  apply hν
  simp [mult, hbot]

omit [CharZero k] in
theorem faithful_mult : ∀ y : Y, y ≠ 0 → ∃ ν, mult W ν ≠ 0 ∧ P ν y ≠ 0 := by
  intro y hy
  obtain ⟨μ, hμ, hP⟩ := h.faithful y hy
  exact ⟨μ, fun h0 => hμ (Submodule.finrank_eq_zero.mp h0), hP⟩

theorem Mk_mul_Mik : Mk P yb W * Mik P yb W = 1 := by
  rw [Mk, Mik, ← map_mul, mul_nonsing_inv _ (GramDual.isUnit_det_gram P yb h.finite_mult
    h.faithful_mult), map_one]

theorem Mik_mul_Mk : Mik P yb W * Mk P yb W = 1 := by
  rw [Mk, Mik, ← map_mul, nonsing_inv_mul _ (GramDual.isUnit_det_gram P yb h.finite_mult
    h.faithful_mult), map_one]

theorem Mk_apply (j l : ι) :
    Mk P yb W j l = ∑ ν ∈ h.finite_mult.toFinset,
      (mult W ν : k) * (ck k P yb ν j * ck k P yb ν l) := by
  rw [Mk, RingHom.mapMatrix_apply, Matrix.map_apply, GramDual.gram_eq_sum P yb h.finite_mult,
    Matrix.sum_apply, Rat.coe_castHom, Rat.cast_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [Matrix.smul_apply, vecMulVec_apply, smul_eq_mul, Rat.cast_mul, Rat.cast_mul,
    Rat.cast_natCast, coord_cast, coord_cast]

theorem Mk_symm (j l : ι) : Mk P yb W j l = Mk P yb W l j := by
  rw [h.Mk_apply, h.Mk_apply]
  exact Finset.sum_congr rfl fun ν _ => by ring

theorem Mik_symm (j l : ι) : Mik P yb W j l = Mik P yb W l j := by
  have hsymm : ((GramDual.gram P yb (mult W))⁻¹)ᵀ = (GramDual.gram P yb (mult W))⁻¹ := by
    rw [transpose_nonsing_inv, GramDual.gram_transpose P yb h.finite_mult]
  simp only [Mik, RingHom.mapMatrix_apply, Matrix.map_apply]
  conv_lhs => rw [← hsymm]
  rfl

omit [FiniteDimensional k U] h in
theorem form_cast (μ ν : X) :
    ((GramDual.form P yb (mult W) μ ν : ℚ) : k) =
      ck k P yb μ ⬝ᵥ (Mik P yb W *ᵥ ck k P yb ν) := by
  simp only [GramDual.form_apply, dotProduct, mulVec, Rat.cast_sum, Rat.cast_mul, coord_cast,
    Mik, RingHom.mapMatrix_apply, Matrix.map_apply, Rat.coe_castHom]

/-! ### Torus elements -/

/-- An element of `g` acting by the cocharacter `y`. -/
def tor (y : Y) : Module.End k U := (h.exists_torus y).choose

omit [CharZero k] [FiniteDimensional k U] in
theorem tor_mem (y : Y) : h.tor y ∈ g := (h.exists_torus y).choose_spec.1

omit [CharZero k] [FiniteDimensional k U] in
theorem tor_isScalarOn (y : Y) : IsScalarOn W (fun μ => ((P μ y : ℤ) : k)) (h.tor y) :=
  (h.exists_torus y).choose_spec.2

omit h [CharZero k] [FiniteDimensional k U] in
theorem eq_of_isScalarOn (h : Hyp P W g root) {φ : X → k} {x x' : Module.End k U}
    (hx : IsScalarOn W φ x) (hx' : IsScalarOn W φ x') : x = x' :=
  ext_of_iSup_eq_top h.iSup_eq_top fun μ u hu => by rw [hx μ u hu, hx' μ u hu]

/-- The torus element of the basis cocharacter `y_j`. -/
def t (j : ι) : Module.End k U := h.tor (yb j)

/-- The torus element `∑ a_j t_j`. -/
def τ (a : ι → k) : Module.End k U := ∑ j, a j • h.t yb j

/-- The dual torus elements `t^l = ∑_j (M⁻¹)_{lj} t_j`. -/
def td (l : ι) : Module.End k U := h.τ yb fun j => Mik P yb W l j

omit [Fintype ι] [DecidableEq ι] [CharZero k] [FiniteDimensional k U] in
theorem t_mem (j : ι) : h.t yb j ∈ g := h.tor_mem (yb j)

omit [DecidableEq ι] [CharZero k] [FiniteDimensional k U] in
theorem τ_mem (a : ι → k) : h.τ yb a ∈ g :=
  g.toSubmodule.sum_mem fun j _ => g.toSubmodule.smul_mem _ (h.t_mem yb j)

omit [FiniteDimensional k U] in
theorem td_mem (l : ι) : h.td yb l ∈ g := h.τ_mem yb _

omit [Fintype ι] [DecidableEq ι] [CharZero k] [FiniteDimensional k U] in
theorem isScalarOn_t (j : ι) : IsScalarOn W (fun μ => ck k P yb μ j) (h.t yb j) :=
  h.tor_isScalarOn (yb j)

omit [DecidableEq ι] [CharZero k] [FiniteDimensional k U] in
theorem isScalarOn_τ (a : ι → k) :
    IsScalarOn W (fun μ => a ⬝ᵥ ck k P yb μ) (h.τ yb a) := by
  have hs := IsScalarOn.sum (W := W) Finset.univ (φ := fun j => a j • fun μ => ck k P yb μ j)
    (t := fun j => a j • h.t yb j) fun j _ => (h.isScalarOn_t yb j).smul (a j)
  intro μ u hu
  rw [τ, hs μ u hu]
  congr 1
  simp [dotProduct, Finset.sum_apply]

omit [DecidableEq ι] [CharZero k] [FiniteDimensional k U] in
theorem τ_mem_shift (a : ι → k) : h.τ yb a ∈ shift W 0 :=
  (h.isScalarOn_τ yb a).mem_shift_zero W

omit [Fintype ι] [DecidableEq ι] [CharZero k] [FiniteDimensional k U] in
theorem t_mem_shift (j : ι) : h.t yb j ∈ shift W 0 :=
  (h.isScalarOn_t yb j).mem_shift_zero W

omit [FiniteDimensional k U] in
theorem td_mem_shift (l : ι) : h.td yb l ∈ shift W 0 := h.τ_mem_shift yb _

omit [CharZero k] [FiniteDimensional k U] in
theorem τ_single (j : ι) : h.τ yb (Pi.single j 1) = h.t yb j := by
  simp [τ, Pi.single_apply]

omit [FiniteDimensional k U] in
theorem sum_smul_td (c : ι → k) : ∑ l, c l • h.td yb l = h.τ yb (c ᵥ* Mik P yb W) := by
  simp only [td, τ, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_smul]
  rfl

omit [DecidableEq ι] [CharZero k] [FiniteDimensional k U] in
/-- Every element of `g` of degree zero is a torus element. -/
theorem exists_eq_τ {x : Module.End k U} (hx : x ∈ g.toSubmodule ⊓ shift W 0) :
    ∃ a, x = h.τ yb a := by
  have hgen : ∀ x ∈ Submodule.span k
      {x | ∃ y : Y, IsScalarOn W (fun μ => ((P μ y : ℤ) : k)) x},
      ∃ a : ι → k, IsScalarOn W (fun μ => a ⬝ᵥ ck k P yb μ) x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy⟩ := hx
      refine ⟨fun j => ((yb.repr y j : ℤ) : k), fun μ u hu => ?_⟩
      rw [hy μ u hu]
      congr 1
      have hP : P μ y = ∑ i, yb.repr y i * P μ (yb i) := by
        conv_lhs => rw [← yb.sum_repr y]
        rw [map_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [map_zsmul, smul_eq_mul]
      simp only [dotProduct, ck, hP, Int.cast_sum, Int.cast_mul]
    | zero => exact ⟨0, fun μ u _ => by simp⟩
    | add x x' _ _ hx hx' =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨a', ha'⟩ := hx'
      refine ⟨a + a', fun μ u hu => ?_⟩
      rw [LinearMap.add_apply, ha μ u hu, ha' μ u hu]
      dsimp only
      rw [add_dotProduct, add_smul]
    | smul c x _ hx =>
      obtain ⟨a, ha⟩ := hx
      refine ⟨c • a, fun μ u hu => ?_⟩
      rw [LinearMap.smul_apply, ha μ u hu]
      dsimp only
      rw [smul_dotProduct, smul_eq_mul, smul_smul]
  obtain ⟨a, ha⟩ := hgen x (h.zero_le_span hx)
  exact ⟨a, h.eq_of_isScalarOn ha (h.isScalarOn_τ yb a)⟩

/-! ### Traces of torus elements -/

theorem trace_mul_of_isScalarOn {φ ψ : X → k} {x z : Module.End k U} (hx : IsScalarOn W φ x)
    (hz : IsScalarOn W ψ z) :
    LinearMap.trace k U (x * z) =
      ∑ ν ∈ h.finite_mult.toFinset, (mult W ν : k) * (φ ν * ψ ν) := by
  rw [trace_eq_finsum_of_isScalarOn h.indep h.iSup_eq_top (hx.mul hz)]
  exact finsum_eq_sum_of_support_subset _
    (GramDual.support_subset_of_eq_zero h.finite_mult fun ν hν => by simp [mult] at hν ⊢; simp [hν])

theorem trace_τ_mul_τ (a b : ι → k) :
    LinearMap.trace k U (h.τ yb a * h.τ yb b) = a ⬝ᵥ (Mk P yb W *ᵥ b) := by
  rw [h.trace_mul_of_isScalarOn (h.isScalarOn_τ yb a) (h.isScalarOn_τ yb b)]
  simp only [dotProduct, mulVec, h.Mk_apply, Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  refine Finset.sum_congr rfl fun ν _ => ?_
  ring

theorem trace_t_mul_τ (j : ι) (b : ι → k) :
    LinearMap.trace k U (h.t yb j * h.τ yb b) = (Mk P yb W *ᵥ b) j := by
  rw [← h.τ_single yb j, h.trace_τ_mul_τ, single_dotProduct, one_mul]

theorem trace_τ_mul_td (a : ι → k) (l : ι) :
    LinearMap.trace k U (h.τ yb a * h.td yb l) = a l := by
  rw [td, h.trace_τ_mul_τ]
  have hv : (Mk P yb W *ᵥ fun j => Mik P yb W l j) = Pi.single l 1 := by
    ext i
    have h1 := congrFun (congrFun (h.Mk_mul_Mik yb) i) l
    rw [Matrix.mul_apply] at h1
    rw [mulVec, dotProduct]
    simp_rw [h.Mik_symm yb l]
    rw [h1, Matrix.one_apply, Pi.single_apply]
  rw [hv, dotProduct_single, mul_one]

theorem trace_t_mul_td (j l : ι) :
    LinearMap.trace k U (h.t yb j * h.td yb l) = if j = l then 1 else 0 := by
  rw [← h.τ_single yb j, h.trace_τ_mul_td, Pi.single_apply]
  exact if_congr eq_comm rfl rfl

/-- A torus element is determined by its traces against the `t_l`. -/
theorem τ_eq_of_Mk_mulVec {a : ι → k} {b : ι → k} (hab : Mk P yb W *ᵥ a = b) :
    a = Mik P yb W *ᵥ b := by
  rw [← hab, mulVec_mulVec, h.Mik_mul_Mk, one_mulVec]

/-! ### Nondegeneracy of the trace form -/

variable [IsAddTorsionFree X]

omit [CharZero k] [IsAddTorsionFree X] in
theorem trace_mul_eq_zero_of_mem_shift {χ ψ : X} (hχψ : χ + ψ ≠ 0) {a z : Module.End k U}
    (ha : a ∈ shift W χ) (hz : z ∈ shift W ψ) : LinearMap.trace k U (a * z) = 0 :=
  trace_eq_zero_of_mem_shift h.indep h.iSup_eq_top hχψ (mul_mem_shift ha hz)

omit [CharZero k] [IsAddTorsionFree X] in
theorem trace_mul_eq_zero_of_homog {χ : X} {a : Module.End k U} (ha : a ∈ shift W χ)
    (h0 : ∀ z ∈ g.toSubmodule ⊓ shift W (-χ), LinearMap.trace k U (a * z) = 0)
    {z : Module.End k U} (hz : z ∈ g) : LinearMap.trace k U (a * z) = 0 := by
  have hz' : z ∈ ⨆ ψ, g.toSubmodule ⊓ shift W ψ := h.le_iSup hz
  clear hz
  induction hz' using Submodule.iSup_induction' with
  | mem ψ z hz =>
    by_cases hψ : ψ = -χ
    · subst hψ
      exact h0 z hz
    · exact h.trace_mul_eq_zero_of_mem_shift
        (fun h' => hψ (eq_neg_of_add_eq_zero_right h')) ha (Submodule.mem_inf.mp hz).2
  | zero => simp
  | add z z' _ _ h1 h2 => rw [mul_add, map_add, h1, h2, add_zero]

include yb in
/-- The trace form of `U` is nondegenerate on `g`. -/
theorem eq_zero_of_trace_mul_eq_zero {x : Module.End k U} (hx : x ∈ g)
    (hx' : ∀ z ∈ g, LinearMap.trace k U (x * z) = 0) : x = 0 := by
  classical
  have hnil : ∀ x ∈ g, (∀ z ∈ g, LinearMap.trace k U (x * z) = 0) → IsNilpotent x := by
    intro x hx hx'
    obtain ⟨f, hf, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ x).mp (h.le_iSup hx)
    have hfg : ∀ χ, f χ ∈ g := fun χ => (Submodule.mem_inf.mp (hf χ)).1
    have hfs : ∀ χ, f χ ∈ shift W χ := fun χ => (Submodule.mem_inf.mp (hf χ)).2
    have hrad : ∀ χ, ∀ z ∈ g, LinearMap.trace k U (f χ * z) = 0 := by
      intro χ z₀ hz₀
      refine h.trace_mul_eq_zero_of_homog (hfs χ) (fun z hz => ?_) hz₀
      have h1 := hx' z (Submodule.mem_inf.mp hz).1
      rw [← hsum, Finsupp.sum, Finset.sum_mul, map_sum, Finset.sum_eq_single χ] at h1
      · exact h1
      · intro χ' _ hne
        exact h.trace_mul_eq_zero_of_mem_shift
          (by rw [← sub_eq_add_neg]; exact sub_ne_zero.mpr hne) (hfs χ')
          (Submodule.mem_inf.mp hz).2
      · intro hχ
        rw [Finsupp.notMem_support_iff.mp hχ, zero_mul, map_zero]
    have hf0 : f 0 = 0 := by
      obtain ⟨a, ha⟩ := h.exists_eq_τ yb (hf 0)
      have hMa : Mk P yb W *ᵥ a = 0 := by
        ext l
        rw [← h.trace_t_mul_τ, ← ha, LinearMap.trace_mul_comm, Pi.zero_apply]
        exact hrad 0 _ (h.t_mem yb l)
      rw [ha, h.τ_eq_of_Mk_mulVec yb hMa, mulVec_zero]
      simp [τ]
    have hfnil : ∀ χ, IsNilpotent (f χ) := by
      intro χ
      by_cases hχ : χ = 0
      · subst hχ
        rw [hf0]
        exact IsNilpotent.zero
      · exact isNilpotent_of_mem_shift h.indep h.iSup_eq_top hχ (hfs χ)
    have hcomm : ∀ χ χ', Commute (f χ) (f χ') := fun χ χ' =>
      TraceFormCasimir.commute_of_trace_mul_eq_zero g h.nilpotent_ideal (hfg χ) (hfg χ')
        (hrad χ) (hrad χ')
    rw [← hsum, Finsupp.sum]
    exact Commute.isNilpotent_sum (fun χ _ => hfnil χ) fun χ χ' _ _ => hcomm χ χ'
  let R : LieIdeal k g := LieAlgebra.InvariantForm.orthogonal (LieModule.traceForm k g U)
    (LieModule.traceForm_lieInvariant k g U) ⊤
  have hR : ∀ z : g, z ∈ R → ∀ w ∈ g, LinearMap.trace k U ((z : Module.End k U) * w) = 0 := by
    intro z hz w hw
    have h' := (LieAlgebra.InvariantForm.mem_orthogonal _ _ _ _).mp hz ⟨w, hw⟩
      (LieSubmodule.mem_top _)
    rwa [LieModule.traceForm_comm, TraceFormCasimir.traceForm_eq] at h'
  have hR0 : R = ⊥ := h.nilpotent_ideal R fun z hz => hnil z z.2 (hR z hz)
  have hxR : (⟨x, hx⟩ : g) ∈ R := by
    rw [LieAlgebra.InvariantForm.mem_orthogonal]
    intro w _
    rw [LieModule.traceForm_comm, TraceFormCasimir.traceForm_eq]
    exact hx' w w.2
  rw [hR0, LieSubmodule.mem_bot] at hxR
  exact congrArg Subtype.val hxR

/-! ### Root vectors -/

include yb in
theorem exists_root_vectors (i : J) :
    ∃ e f : Module.End k U, e ∈ g.toSubmodule ⊓ shift W (root i) ∧
      f ∈ g.toSubmodule ⊓ shift W (-root i) ∧ LinearMap.trace k U (e * f) = 1 ∧
      (∀ v ∈ g.toSubmodule ⊓ shift W (root i), ∃ c : k, v = c • e) ∧
      (∀ v ∈ g.toSubmodule ⊓ shift W (-root i), ∃ c : k, v = c • f) := by
  obtain ⟨⟨e, he⟩, he0, hespan⟩ := finrank_eq_one_iff'.mp (h.finrank_root i)
  have he0' : e ≠ 0 := fun h' => he0 (Subtype.ext h')
  have hex : ∃ f ∈ g.toSubmodule ⊓ shift W (-root i), LinearMap.trace k U (e * f) ≠ 0 := by
    by_contra hcon
    refine he0' (h.eq_zero_of_trace_mul_eq_zero yb (Submodule.mem_inf.mp he).1 fun z hz =>
      h.trace_mul_eq_zero_of_homog (Submodule.mem_inf.mp he).2 (fun f hf => ?_) hz)
    by_contra hne
    exact hcon ⟨f, hf, hne⟩
  obtain ⟨f0, hf0, hef0⟩ := hex
  have hfmem : (LinearMap.trace k U (e * f0))⁻¹ • f0 ∈ g.toSubmodule ⊓ shift W (-root i) :=
    Submodule.smul_mem _ _ hf0
  have hT : LinearMap.trace k U (e * ((LinearMap.trace k U (e * f0))⁻¹ • f0)) = 1 := by
    rw [mul_smul_comm, map_smul, smul_eq_mul, inv_mul_cancel₀ hef0]
  refine ⟨e, _, he, hfmem, hT, ?_, ?_⟩
  · intro v hv
    obtain ⟨c, hc⟩ := hespan ⟨v, hv⟩
    exact ⟨c, (congrArg Subtype.val hc).symm⟩
  · intro v hv
    obtain ⟨i', hi'⟩ := h.exists_neg i
    have hf1 : finrank k ↥(g.toSubmodule ⊓ shift W (-root i)) = 1 := by
      rw [← hi']
      exact h.finrank_root i'
    have hfne : (⟨_, hfmem⟩ : ↥(g.toSubmodule ⊓ shift W (-root i))) ≠ 0 := by
      intro h0
      have h0' := congrArg Subtype.val h0
      simp only [ZeroMemClass.coe_zero] at h0'
      rw [h0', mul_zero, map_zero] at hT
      exact zero_ne_one hT
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hfne).mp hf1 ⟨v, hv⟩
    exact ⟨c, (congrArg Subtype.val hc).symm⟩

/-- A root vector spanning the root part of degree `root i`. -/
def e (i : J) : Module.End k U := (h.exists_root_vectors yb i).choose

/-- The root vector of degree `-root i` dual to `e i`. -/
def f (i : J) : Module.End k U := (h.exists_root_vectors yb i).choose_spec.choose

theorem e_mem (i : J) : h.e yb i ∈ g.toSubmodule ⊓ shift W (root i) :=
  (h.exists_root_vectors yb i).choose_spec.choose_spec.1

theorem f_mem (i : J) : h.f yb i ∈ g.toSubmodule ⊓ shift W (-root i) :=
  (h.exists_root_vectors yb i).choose_spec.choose_spec.2.1

theorem trace_e_mul_f (i : J) : LinearMap.trace k U (h.e yb i * h.f yb i) = 1 :=
  (h.exists_root_vectors yb i).choose_spec.choose_spec.2.2.1

theorem eq_smul_e (i : J) {v : Module.End k U} (hv : v ∈ g.toSubmodule ⊓ shift W (root i)) :
    ∃ c : k, v = c • h.e yb i :=
  (h.exists_root_vectors yb i).choose_spec.choose_spec.2.2.2.1 v hv

theorem eq_smul_f (i : J) {v : Module.End k U} (hv : v ∈ g.toSubmodule ⊓ shift W (-root i)) :
    ∃ c : k, v = c • h.f yb i :=
  (h.exists_root_vectors yb i).choose_spec.choose_spec.2.2.2.2 v hv

/-! ### The dual families and the Casimir element -/

/-- The first family: torus elements `t_j` and root vectors `e_i`. -/
def bfam : ι ⊕ J → Module.End k U := Sum.elim (h.t yb) (h.e yb)

/-- The second family: dual torus elements `t^l` and root vectors `f_i`. -/
def dfam : ι ⊕ J → Module.End k U := Sum.elim (h.td yb) (h.f yb)

theorem bfam_mem (a : ι ⊕ J) : h.bfam yb a ∈ g := by
  rcases a with j | i
  · exact h.t_mem yb j
  · exact (Submodule.mem_inf.mp (h.e_mem yb i)).1

theorem dfam_mem (a : ι ⊕ J) : h.dfam yb a ∈ g := by
  rcases a with j | i
  · exact h.td_mem yb j
  · exact (Submodule.mem_inf.mp (h.f_mem yb i)).1

theorem trace_bfam_mul_dfam [DecidableEq J] (a c : ι ⊕ J) :
    LinearMap.trace k U (h.bfam yb a * h.dfam yb c) = if a = c then 1 else 0 := by
  rcases a with j | i <;> rcases c with l | i'
  · simp only [bfam, dfam, Sum.elim_inl, Sum.inl.injEq]
    exact h.trace_t_mul_td yb j l
  · simp only [bfam, dfam, Sum.elim_inl, Sum.elim_inr, reduceCtorEq, ite_false]
    have hne : (0 : X) + -root i' ≠ 0 := by
      rw [zero_add]
      exact neg_ne_zero.mpr (h.root_ne_zero i')
    exact h.trace_mul_eq_zero_of_mem_shift hne (h.t_mem_shift yb j)
      (Submodule.mem_inf.mp (h.f_mem yb i')).2
  · simp only [bfam, dfam, Sum.elim_inl, Sum.elim_inr, reduceCtorEq, ite_false]
    have hne : root i + 0 ≠ 0 := by
      rw [add_zero]
      exact h.root_ne_zero i
    exact h.trace_mul_eq_zero_of_mem_shift hne (Submodule.mem_inf.mp (h.e_mem yb i)).2
      (h.td_mem_shift yb l)
  · simp only [bfam, dfam, Sum.elim_inr, Sum.inr.injEq]
    split_ifs with hii
    · subst hii
      exact h.trace_e_mul_f yb i
    · refine h.trace_mul_eq_zero_of_mem_shift ?_ (Submodule.mem_inf.mp (h.e_mem yb i)).2
        (Submodule.mem_inf.mp (h.f_mem yb i')).2
      rw [← sub_eq_add_neg, sub_ne_zero]
      exact fun h' => hii (h.root_injective h')

theorem le_span_bfam : g.toSubmodule ≤ Submodule.span k (Set.range (h.bfam yb)) := by
  intro x hx
  have hx' : x ∈ ⨆ χ, g.toSubmodule ⊓ shift W χ := h.le_iSup hx
  clear hx
  induction hx' using Submodule.iSup_induction' with
  | mem χ x hx =>
    by_cases hχ : χ = 0
    · subst hχ
      obtain ⟨a, rfl⟩ := h.exists_eq_τ yb hx
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
        (Submodule.subset_span ⟨Sum.inl j, rfl⟩)
    · by_cases hr : χ ∈ Set.range root
      · obtain ⟨i, rfl⟩ := hr
        obtain ⟨c, rfl⟩ := h.eq_smul_e yb i hx
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr i, rfl⟩)
      · rw [h.eq_bot χ hχ hr, Submodule.mem_bot] at hx
        rw [hx]
        exact Submodule.zero_mem _
  | zero => exact Submodule.zero_mem _
  | add x x' _ _ h1 h2 => exact Submodule.add_mem _ h1 h2

theorem le_span_dfam : g.toSubmodule ≤ Submodule.span k (Set.range (h.dfam yb)) := by
  intro x hx
  have hx' : x ∈ ⨆ χ, g.toSubmodule ⊓ shift W χ := h.le_iSup hx
  clear hx
  induction hx' using Submodule.iSup_induction' with
  | mem χ x hx =>
    by_cases hχ : χ = 0
    · subst hχ
      obtain ⟨a, rfl⟩ := h.exists_eq_τ yb hx
      have heq : h.τ yb a = ∑ l, (Mk P yb W *ᵥ a) l • h.td yb l := by
        rw [h.sum_smul_td, ← mulVec_transpose]
        congr 1
        have hT : (Mik P yb W)ᵀ = Mik P yb W := by
          ext j l
          exact h.Mik_symm yb l j
        rw [hT, mulVec_mulVec, h.Mik_mul_Mk, one_mulVec]
      rw [heq]
      exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _
        (Submodule.subset_span ⟨Sum.inl l, rfl⟩)
    · by_cases hr : χ ∈ Set.range root
      · obtain ⟨i, rfl⟩ := hr
        obtain ⟨i', hi'⟩ := h.exists_neg i
        have hx2 : x ∈ g.toSubmodule ⊓ shift W (-root i') := by
          rw [hi', neg_neg]
          exact hx
        obtain ⟨c, rfl⟩ := h.eq_smul_f yb i' hx2
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr i', rfl⟩)
      · rw [h.eq_bot χ hχ hr, Submodule.mem_bot] at hx
        rw [hx]
        exact Submodule.zero_mem _
  | zero => exact Submodule.zero_mem _
  | add x x' _ _ h1 h2 => exact Submodule.add_mem _ h1 h2

/-- The Casimir element `Ω = ∑_j t_j t^j + ∑_i e_i f_i`. -/
def casimir [Fintype J] : Module.End k U := ∑ a, h.bfam yb a * h.dfam yb a

theorem casimir_eq [Fintype J] :
    h.casimir yb = ∑ j, h.t yb j * h.td yb j + ∑ i, h.e yb i * h.f yb i := by
  rw [casimir, Fintype.sum_sum_type]
  rfl

theorem commute_casimir [Fintype J] {x : Module.End k U} (hx : x ∈ g) :
    Commute x (h.casimir yb) := by
  classical
  have hrad : ∀ x ∈ g.toSubmodule, (∀ z ∈ g.toSubmodule, LinearMap.trace k U (x * z) = 0) →
      x = 0 := fun x hx hx' => h.eq_zero_of_trace_mul_eq_zero yb hx hx'
  have hbr : ∀ y ∈ g, x * y - y * x ∈ g.toSubmodule := fun y hy => g.lie_mem hx hy
  exact TraceFormCasimir.commute_sum_mul (LinearMap.trace k U)
    (fun x y => LinearMap.trace_mul_comm k x y) g.toSubmodule (h.bfam yb) (h.dfam yb)
    (fun v hv => eq_sum_trace_mul_smul g.toSubmodule _ _ (h.trace_bfam_mul_dfam yb)
      (h.le_span_dfam yb) (h.bfam_mem yb) hrad hv)
    (fun v hv => eq_sum_trace_mul_smul' g.toSubmodule _ _ (h.trace_bfam_mul_dfam yb)
      (h.le_span_bfam yb) (h.dfam_mem yb) hrad hv)
    (fun a => hbr _ (h.bfam_mem yb a)) (fun a => hbr _ (h.dfam_mem yb a))

theorem casimir_mem_shift [Fintype J] : h.casimir yb ∈ shift W 0 := by
  refine Submodule.sum_mem _ fun a _ => ?_
  rcases a with j | i
  · exact mul_mem_shift' (h.t_mem_shift yb j) (h.td_mem_shift yb j) (add_zero 0)
  · exact mul_mem_shift' (Submodule.mem_inf.mp (h.e_mem yb i)).2
      (Submodule.mem_inf.mp (h.f_mem yb i)).2 (add_neg_cancel _)

theorem casimir_mem_of_stable [Fintype J] {V : Submodule k U}
    (hV : ∀ x ∈ g, ∀ v ∈ V, x v ∈ V) {v : U} (hv : v ∈ V) : h.casimir yb v ∈ V := by
  rw [casimir, LinearMap.sum_apply]
  exact V.sum_mem fun a _ =>
    hV _ (h.bfam_mem yb a) _ (hV _ (h.dfam_mem yb a) _ hv)

end Hyp

end Graded

end Langlands.LinearAlgebra.FreudenthalCasimir
