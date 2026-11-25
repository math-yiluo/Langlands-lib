import Langlands.Theta.Heisenberg.SchrodingerUnitary
import Langlands.Theta.Heisenberg.SchrodingerIrreducible

/-!
# Invariant sesquilinear forms on the Schrödinger model

GKT §1.3.1 (Theorem 1.31: the Heisenberg representation is unitarizable) and Appendix A
(Lemma A.16: on an irreducible unitarizable representation the invariant Hermitian form is unique up
to a positive scalar), for the Schrödinger model, proved directly. Let `β : X × Y → F` be a perfect
pairing of finite-dimensional spaces over a nonarchimedean local field, `ψ` a continuous
non-trivial character and `μ` a Haar measure on `X`.

* `exists_eq_mul_schwartzBruhatInner`: every sesquilinear form on `S(X)` invariant under the
  Schrödinger operators is `c ⟨,⟩_μ` for a complex number `c`.
* `exists_pos_schwartzBruhatInner_map`: a non-zero linear map `T` of `S(X)` with
  `T ∘ σ(h) = σ(a h) ∘ T` for a map `a` of the Heisenberg group multiplies the `L²` inner product
  by a constant `C > 0`; so `C^{-1/2} T` is unitary. This is how the Haar measures of GKT
  Proposition 1.21 and Proposition 2.13 ("the unique measure that makes the operator unitary") are
  fixed in the Library.

The proof replaces Schur's lemma for unitary representations by the structure of the model: for a
compact open subgroup `L` of `X` with orthogonal `M = L^⊥` in `Y`, the operators `σ(0, y)`,
`y ∈ M`, act on the indicator of `z + L` by the scalar `ψ(β(z, y))`, so an invariant form vanishes
on two different cosets (`L^⊥⊥ = L`), and the translations make its value on one coset independent
of the coset. A function invariant under `L` is a finite combination of such indicators.
-/

noncomputable section

open MeasureTheory Filter Topology

namespace Langlands.HeisenbergGroup

open Langlands.HarmonicAnalysis
open SchrodingerIrreducible.Internal Langlands.HarmonicAnalysis.BicharacterFourier.Internal
open Langlands.Theta (schwartzBruhatInner schwartzBruhatInner_apply schwartzBruhatInner_self)

universe u v w

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Invertible (2 : F)]
  {X : Type v} [AddCommGroup X] [Module F X] [FiniteDimensional F X] [TopologicalSpace X]
  [IsModuleTopology F X] [IsTopologicalAddGroup X]
  {Y : Type w} [AddCommGroup Y] [Module F Y] [FiniteDimensional F Y] [TopologicalSpace Y]
  [IsModuleTopology F Y]
  {β : X →ₗ[F] Y →ₗ[F] F} {ψ : AddChar F ℂ}
  (hψ : Continuous ψ) (hβ : ∀ y, Continuous fun x => β x y)

/-- **A sesquilinear form invariant under the Schrödinger model**: `B(σ(h) φ, σ(h) φ') = B(φ, φ')`
for all `h` in the Heisenberg group. -/
def IsSchrodingerInvariant (B : SchwartzBruhat X →ₗ⋆[ℂ] SchwartzBruhat X →ₗ[ℂ] ℂ) : Prop :=
  ∀ (h : HeisenbergGroup (polarizedForm β)) (φ φ' : SchwartzBruhat X),
    B (schrodingerSB hψ hβ h φ) (schrodingerSB hψ hβ h φ') = B φ φ'

namespace InvariantForm.Internal

/-- The translate `x ↦ 1_L(x - z)` of the indicator of a compact open subgroup, as
`σ(-z, 0) 1_L`. -/
def cosetIndicator (L : AddSubgroup X) (hc : IsCompact (L : Set X)) (ho : IsOpen (L : Set X))
    (z : X) : SchwartzBruhat X :=
  schrodingerSB hψ hβ (ofVec (-z, 0)) ⟨_, indicator_one_mem_schwartzBruhatSubmodule L hc ho⟩

omit [FiniteDimensional F X] [IsModuleTopology F X] [FiniteDimensional F Y] [TopologicalSpace Y]
  [IsModuleTopology F Y] in
theorem cosetIndicator_apply (L : AddSubgroup X) (hc : IsCompact (L : Set X))
    (ho : IsOpen (L : Set X)) (z x : X) :
    (cosetIndicator hψ hβ L hc ho z : X → ℂ) x =
      (L : Set X).indicator (fun _ => (1 : ℂ)) (x - z) := by
  simp only [cosetIndicator, schrodingerSB_apply, schrodinger_ofVec, schrodingerFun_apply,
    map_zero, mul_zero, add_zero, AddChar.map_zero_eq_one, one_mul, sub_eq_add_neg]

omit [FiniteDimensional F X] [IsModuleTopology F X] [FiniteDimensional F Y]
  [IsModuleTopology F Y] in
/-- `σ(0, y)` acts on `1_{z+L}` by `ψ(β(z, y))` when `y` is orthogonal to `L`. -/
theorem schrodingerSB_cosetIndicator (P : LatticePair β ψ) (z : X) {y : Y} (hy : y ∈ P.right) :
    schrodingerSB hψ hβ (ofVec (0, y))
        (cosetIndicator hψ hβ P.left P.isCompact_left P.isOpen_left z) =
      ψ (β z y) • cosetIndicator hψ hβ P.left P.isCompact_left P.isOpen_left z := by
  ext x
  simp only [schrodingerSB_apply, schrodinger_ofVec, schrodingerFun_apply, map_zero,
    LinearMap.zero_apply, mul_zero, add_zero, SetLike.val_smul, Pi.smul_apply, smul_eq_mul]
  change ψ (β x y) * (cosetIndicator hψ hβ _ _ _ z : X → ℂ) x =
    ψ (β z y) * (cosetIndicator hψ hβ _ _ _ z : X → ℂ) x
  rw [cosetIndicator_apply]
  by_cases hx : x - z ∈ (P.left : Set X)
  · rw [Set.indicator_of_mem hx]
    have : x = z + (x - z) := by abel
    rw [this, map_add, LinearMap.add_apply, AddChar.map_add_eq_mul, P.apply_eq_one hx hy, mul_one]
  · rw [Set.indicator_of_notMem hx, mul_zero, mul_zero]

omit [FiniteDimensional F X] [IsModuleTopology F X] [FiniteDimensional F Y]
  [IsModuleTopology F Y] in
/-- An invariant form vanishes on the indicators of two different cosets. -/
theorem invariant_cosetIndicator_of_sub_notMem
    {B : SchwartzBruhat X →ₗ⋆[ℂ] SchwartzBruhat X →ₗ[ℂ] ℂ}
    (hB : IsSchrodingerInvariant hψ hβ B) (P : LatticePair β ψ) {z z' : X}
    (hzz : z' - z ∉ P.left) :
    B (cosetIndicator hψ hβ P.left P.isCompact_left P.isOpen_left z)
      (cosetIndicator hψ hβ P.left P.isCompact_left P.isOpen_left z') = 0 := by
  have hL := P.left_eq
  obtain ⟨y, hy, hne⟩ : ∃ y ∈ P.right, ψ (β (z' - z) y) ≠ 1 := by
    by_contra h
    push Not at h
    apply hzz
    rw [hL]
    exact fun y hy => h y hy
  set u := cosetIndicator hψ hβ P.left P.isCompact_left P.isOpen_left z
  set u' := cosetIndicator hψ hβ P.left P.isCompact_left P.isOpen_left z'
  have h1 := hB (ofVec (0, y)) u u'
  rw [schrodingerSB_cosetIndicator hψ hβ P z hy, schrodingerSB_cosetIndicator hψ hβ P z' hy] at h1
  simp only [map_smulₛₗ, LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul] at h1
  have hconj : (starRingEnd ℂ) (ψ (β z y)) = ψ (-(β z y)) := by
    rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (norm_addChar_eq_one hψ _)]
  have h2 : ψ (β (z' - z) y) * B u u' = B u u' := by
    conv_rhs => rw [← h1]
    rw [hconj, ← mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    simp only [map_sub, LinearMap.sub_apply]
    ring
  have h3 : (ψ (β (z' - z) y) - 1) * B u u' = 0 := by rw [sub_mul, h2, one_mul, sub_self]
  exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hne)

omit [FiniteDimensional F X] [IsModuleTopology F X] [FiniteDimensional F Y] [TopologicalSpace Y]
  [IsModuleTopology F Y] in
/-- An invariant form takes the same value on the indicator of every coset. -/
theorem invariant_cosetIndicator_self {B : SchwartzBruhat X →ₗ⋆[ℂ] SchwartzBruhat X →ₗ[ℂ] ℂ}
    (hB : IsSchrodingerInvariant hψ hβ B) (L : AddSubgroup X) (hc : IsCompact (L : Set X))
    (ho : IsOpen (L : Set X)) (z : X) :
    B (cosetIndicator hψ hβ L hc ho z) (cosetIndicator hψ hβ L hc ho z) =
      B (cosetIndicator hψ hβ L hc ho 0) (cosetIndicator hψ hβ L hc ho 0) := by
  simp only [cosetIndicator]
  rw [hB _ _ _, hB _ _ _]

omit [FiniteDimensional F X] [IsModuleTopology F X] [FiniteDimensional F Y] [TopologicalSpace Y]
  [IsModuleTopology F Y] in
/-- A Schwartz–Bruhat function invariant under `L` and vanishing off a compact set `C` is the sum of
its values on representatives of `C / L` times the indicators of the cosets. -/
theorem eq_sum_cosetIndicator (L : AddSubgroup X) (hc : IsCompact (L : Set X))
    (ho : IsOpen (L : Set X)) {C : Set X} (hC : IsCompact C) (φ : SchwartzBruhat X)
    (hφL : ∀ u ∈ L, ∀ x, (φ : X → ℂ) (x + u) = φ x) (hφC : ∀ x ∉ C, (φ : X → ℂ) x = 0) :
    φ = ∑ c ∈ (finite_image_quotient L ho hC).toFinset,
      (φ : X → ℂ) (Quotient.out c) • cosetIndicator hψ hβ L hc ho (Quotient.out c) := by
  apply Subtype.ext
  rw [Submodule.coe_sum]
  conv_lhs => rw [eq_sum_translates L ho hφL hC hφC]
  refine Finset.sum_congr rfl fun c _ => ?_
  funext x
  rw [Submodule.coe_smul, Pi.smul_apply, Pi.smul_apply, cosetIndicator_apply]

omit [FiniteDimensional F X] [IsModuleTopology F X] [FiniteDimensional F Y]
  [IsModuleTopology F Y] in
/-- **The value of an invariant form on `L`-invariant functions**: the sum over the cosets of `L`
of the products of the values, times the value on `1_L`. -/
theorem invariant_eq_sum {B : SchwartzBruhat X →ₗ⋆[ℂ] SchwartzBruhat X →ₗ[ℂ] ℂ}
    (hB : IsSchrodingerInvariant hψ hβ B) (P : LatticePair β ψ) {C : Set X} (hC : IsCompact C)
    (φ φ' : SchwartzBruhat X) (hφL : ∀ u ∈ P.left, ∀ x, (φ : X → ℂ) (x + u) = φ x)
    (hφC : ∀ x ∉ C, (φ : X → ℂ) x = 0) (hφ'L : ∀ u ∈ P.left, ∀ x, (φ' : X → ℂ) (x + u) = φ' x)
    (hφ'C : ∀ x ∉ C, (φ' : X → ℂ) x = 0) :
    B φ φ' = (∑ c ∈ (finite_image_quotient P.left P.isOpen_left hC).toFinset,
        (starRingEnd ℂ) ((φ : X → ℂ) (Quotient.out c)) * (φ' : X → ℂ) (Quotient.out c)) *
      B (cosetIndicator hψ hβ P.left P.isCompact_left P.isOpen_left 0)
        (cosetIndicator hψ hβ P.left P.isCompact_left P.isOpen_left 0) := by
  conv_lhs => rw [eq_sum_cosetIndicator hψ hβ P.left P.isCompact_left P.isOpen_left hC φ hφL hφC,
    eq_sum_cosetIndicator hψ hβ P.left P.isCompact_left P.isOpen_left hC φ' hφ'L hφ'C]
  simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
    RingHom.id_apply]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun c hc => ?_
  rw [Finset.sum_eq_single c]
  · rw [invariant_cosetIndicator_self hψ hβ hB]; ring
  · intro c' _ hc'
    have hne : Quotient.out c - Quotient.out c' ∉ P.left := by
      intro h
      apply hc'
      rw [← QuotientAddGroup.out_eq' c, ← QuotientAddGroup.out_eq' c']
      exact QuotientAddGroup.eq.2 (by rw [neg_add_eq_sub]; exact h)
    rw [invariant_cosetIndicator_of_sub_notMem hψ hβ hB P hne]
    simp
  · intro h; exact absurd hc h

end InvariantForm.Internal

open InvariantForm.Internal

section Positivity

variable {V : Type*} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V)

/-- `⟨f, f⟩ = ∫ ‖f‖²` as a real integral. -/
theorem schwartzBruhatInner_self_eq_integral [IsFiniteMeasureOnCompacts μ] (f : SchwartzBruhat V) :
    schwartzBruhatInner μ f f = ((∫ x, ‖(f : V → ℂ) x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  rw [schwartzBruhatInner_apply, ← integral_complex_ofReal]
  congr 1
  funext x
  rw [Complex.conj_mul']
  push_cast
  ring

/-- **The `L²` form is positive definite** on Schwartz–Bruhat functions, for a measure positive on
open sets. -/
theorem integral_norm_sq_pos [μ.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μ]
    (f : SchwartzBruhat V) {x : V} (hx : (f : V → ℂ) x ≠ 0) :
    0 < ∫ x, ‖(f : V → ℂ) x‖ ^ 2 ∂μ := by
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := x)
    ((continuous_norm.comp f.2.1.continuous).pow 2) ?_ (fun _ => by positivity)
    (by simpa using hx)
  exact f.2.2.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp)

end Positivity

section Main

variable [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [μ.IsAddHaarMeasure]

omit [FiniteDimensional F X] [IsModuleTopology F X] [FiniteDimensional F Y] [TopologicalSpace Y]
  [IsModuleTopology F Y] in
/-- The `L²` inner product is invariant under the Schrödinger model. -/
theorem isSchrodingerInvariant_schwartzBruhatInner :
    IsSchrodingerInvariant hψ hβ (schwartzBruhatInner μ) :=
  fun h φ φ' => schrodingerSB_inner hψ hβ (norm_addChar_eq_one hψ) μ h φ φ'

/-- **Uniqueness of the invariant form** (GKT Lemma A.16 for the Schrödinger model): a sesquilinear
form on `S(X)` invariant under the Schrödinger operators is a multiple of the `L²` inner product of
a Haar measure. -/
theorem exists_eq_mul_schwartzBruhatInner [β.IsPerfPair] (hψ1 : ψ ≠ 1)
    {B : SchwartzBruhat X →ₗ⋆[ℂ] SchwartzBruhat X →ₗ[ℂ] ℂ} (hB : IsSchrodingerInvariant hψ hβ B) :
    ∃ c : ℂ, ∀ φ φ', B φ φ' = c * schwartzBruhatInner μ φ φ' := by
  have hI := isSchrodingerInvariant_schwartzBruhatInner hψ hβ μ
  obtain ⟨P₀⟩ := LatticePair.nonempty (β := β) hψ hψ1
  set e₀ := cosetIndicator hψ hβ P₀.left P₀.isCompact_left P₀.isOpen_left 0 with he₀_def
  have he₀ : ∀ x, (e₀ : X → ℂ) x = (P₀.left : Set X).indicator (fun _ => (1 : ℂ)) x := fun x => by
    rw [he₀_def, cosetIndicator_apply, sub_zero]
  refine ⟨B e₀ e₀ / schwartzBruhatInner μ e₀ e₀, fun φ φ' => ?_⟩
  obtain ⟨U₁, hU₁, hφU⟩ := exists_nhds_add_eq_of_mem_schwartzBruhatSubmodule φ.2
  obtain ⟨U₂, hU₂, hφ'U⟩ := exists_nhds_add_eq_of_mem_schwartzBruhatSubmodule φ'.2
  have hL₀ : (P₀.left : Set X) ∈ 𝓝 0 := P₀.isOpen_left.mem_nhds P₀.left.zero_mem
  obtain ⟨t, ht⟩ := P₀.exists_smul_left_subset (Filter.inter_mem (Filter.inter_mem hU₁ hU₂) hL₀)
  set P := P₀.smul t
  set C : Set X := tsupport (φ : X → ℂ) ∪ tsupport (φ' : X → ℂ) ∪ (P₀.left : Set X)
  have hC : IsCompact C := (φ.2.2.isCompact.union φ'.2.2.isCompact).union P₀.isCompact_left
  have hφL : ∀ u ∈ P.left, ∀ x, (φ : X → ℂ) (x + u) = φ x := fun u hu x =>
    hφU P.left (fun v hv => (ht hv).1.1) u hu x
  have hφ'L : ∀ u ∈ P.left, ∀ x, (φ' : X → ℂ) (x + u) = φ' x := fun u hu x =>
    hφ'U P.left (fun v hv => (ht hv).1.2) u hu x
  have he₀L : ∀ u ∈ P.left, ∀ x, (e₀ : X → ℂ) (x + u) = e₀ x := fun u hu x => by
    rw [he₀, he₀]
    exact indicator_invariant P₀.left 1 u (ht hu).2 x
  have hφC : ∀ x ∉ C, (φ : X → ℂ) x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (Or.inl (Or.inl h))
  have hφ'C : ∀ x ∉ C, (φ' : X → ℂ) x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (Or.inl (Or.inr h))
  have he₀C : ∀ x ∉ C, (e₀ : X → ℂ) x = 0 := fun x hx => by
    rw [he₀]
    exact Set.indicator_of_notMem (fun h => hx (Or.inr h)) _
  have h1 := invariant_eq_sum hψ hβ hB P hC φ φ' hφL hφC hφ'L hφ'C
  have h2 := invariant_eq_sum hψ hβ hI P hC φ φ' hφL hφC hφ'L hφ'C
  have h3 := invariant_eq_sum hψ hβ hB P hC e₀ e₀ he₀L he₀C he₀L he₀C
  have h4 := invariant_eq_sum hψ hβ hI P hC e₀ e₀ he₀L he₀C he₀L he₀C
  have hpos : schwartzBruhatInner μ e₀ e₀ ≠ 0 := by
    rw [schwartzBruhatInner_self_eq_integral, Complex.ofReal_ne_zero]
    refine (integral_norm_sq_pos μ e₀ (x := 0) ?_).ne'
    rw [he₀, Set.indicator_of_mem (show (0 : X) ∈ (P₀.left : Set X) from P₀.left.zero_mem)]
    exact one_ne_zero
  rw [h4] at hpos
  have hs₀ := left_ne_zero_of_mul hpos
  have hi := right_ne_zero_of_mul hpos
  rw [h1, h2, h3, h4]
  field_simp

/-- **The normalization of an intertwining operator by unitarity.** A non-zero linear map `T` of
`S(X)` with `T ∘ σ(h) = σ(a h) ∘ T` for all `h` (for a map `a` of the Heisenberg group into itself)
multiplies the `L²` inner product by a constant `C > 0`: `C^{-1/2} T` is unitary, and it is the only
positive multiple of `T` that is. -/
theorem exists_pos_schwartzBruhatInner_map [β.IsPerfPair] (hψ1 : ψ ≠ 1)
    (a : HeisenbergGroup (polarizedForm β) → HeisenbergGroup (polarizedForm β))
    (T : SchwartzBruhat X →ₗ[ℂ] SchwartzBruhat X)
    (hT : ∀ h, T ∘ₗ schrodingerSB hψ hβ h = schrodingerSB hψ hβ (a h) ∘ₗ T) (hT0 : T ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ φ φ', schwartzBruhatInner μ (T φ) (T φ') =
      (C : ℂ) * schwartzBruhatInner μ φ φ' := by
  have hI := isSchrodingerInvariant_schwartzBruhatInner hψ hβ μ
  set B : SchwartzBruhat X →ₗ⋆[ℂ] SchwartzBruhat X →ₗ[ℂ] ℂ :=
    ((schwartzBruhatInner μ).comp T).compl₂ T
  have hB : IsSchrodingerInvariant hψ hβ B := fun h φ φ' => by
    change schwartzBruhatInner μ (T (schrodingerSB hψ hβ h φ)) (T (schrodingerSB hψ hβ h φ')) =
      schwartzBruhatInner μ (T φ) (T φ')
    rw [← LinearMap.comp_apply (f := T), hT, ← LinearMap.comp_apply (f := T), hT]
    exact hI (a h) (T φ) (T φ')
  obtain ⟨c, hc⟩ := exists_eq_mul_schwartzBruhatInner hψ hβ μ hψ1 hB
  obtain ⟨φ₀, hφ₀⟩ : ∃ φ₀, T φ₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hT0 (LinearMap.ext h)
  obtain ⟨x₁, hx₁⟩ : ∃ x, (T φ₀ : X → ℂ) x ≠ 0 := by
    by_contra h
    push Not at h
    exact hφ₀ (Subtype.ext (funext h))
  obtain ⟨x₀, hx₀⟩ : ∃ x, (φ₀ : X → ℂ) x ≠ 0 := by
    by_contra h
    push Not at h
    have : φ₀ = 0 := Subtype.ext (funext h)
    exact hφ₀ (by rw [this, map_zero])
  have hr₁ := integral_norm_sq_pos μ (T φ₀) hx₁
  have hr₂ := integral_norm_sq_pos μ φ₀ hx₀
  have h0 := hc φ₀ φ₀
  change schwartzBruhatInner μ (T φ₀) (T φ₀) = c * schwartzBruhatInner μ φ₀ φ₀ at h0
  rw [schwartzBruhatInner_self_eq_integral, schwartzBruhatInner_self_eq_integral] at h0
  set r₁ := ∫ x, ‖(T φ₀ : X → ℂ) x‖ ^ 2 ∂μ
  set r₂ := ∫ x, ‖(φ₀ : X → ℂ) x‖ ^ 2 ∂μ
  have hc' : c = ((r₁ / r₂ : ℝ) : ℂ) := by
    rw [Complex.ofReal_div, h0, mul_div_assoc, div_self (Complex.ofReal_ne_zero.2 hr₂.ne'),
      mul_one]
  refine ⟨r₁ / r₂, div_pos hr₁ hr₂, fun φ φ' => ?_⟩
  rw [← hc']
  exact hc φ φ'

end Main

end Langlands.HeisenbergGroup
