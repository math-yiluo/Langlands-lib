import Langlands.Representation.Archimedean.RealLeviGeometry
import Langlands.Representation.Archimedean.RealInducedStandardBound
import Langlands.Representation.Archimedean.RealBlockChartBound

/-!
# Torus integrals, block orthogonal invariance and growth bounds along `N̄_Q`

Measure-theoretic tools for the limit argument along the standard parabolic subgroup `Q` of
`GL_N(ℝ)` with blocks of sizes `sz` (modules `RealLeviChartIntegralStatement`,
`RealLeviParabolicIntegrationStatement`, `RealLeviGeometry`):

* the iterated mode-`0` Fourier coefficient `coeffs (zeroModes L) F g` of a list of slots `L` is the
  integral of `θ ↦ F(τ(θ) g)` over `θ ∈ (0, 2π]^r` for the torus element
  `τ(θ) = r_{p_{r-1}}(θ_{r-1}) ⋯ r_{p_0}(θ_0)` (`coeffs_eq_integral`);
* the integral over `K_M = ∏_i O(sz_i)` of `f(diag(κ))` is invariant under left multiplication of
  `diag(κ)` by block orthogonal elements (`integral_blockOrth_mul`);
* the substitution `X ↦ Ad(g) X` preserves integrals over `N̄_Q` (`integral_adCoord`);
* the growth bound of principal-series functions in terms of Gram determinants, for every `N`
  (`norm_le_gram_fin`).
-/

noncomputable section

open MeasureTheory Matrix

open scoped Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace RealLeviTorus

open RealInducedBlockBound RealInducedTorusCore RealLeviChart GramFormula

/-! ## Torus parameters -/

section Torus

variable {N : ℕ}

/-- The torus element `r_{p_{r-1}}(θ_{r-1}) ⋯ r_{p_0}(θ_0)` of the slots `L`. -/
def torusElem : (L : List (Slot N)) → (Fin L.length → ℝ) → Langlands.GeneralLinear N ℝ
  | [], _ => 1
  | s :: rest, θ => torusElem rest (fun i => θ i.succ) * blockRotation N s.p (θ 0)

theorem continuous_torusElem : ∀ L : List (Slot N), Continuous (torusElem L)
  | [] => continuous_const
  | s :: rest =>
      ((continuous_torusElem rest).comp (continuous_pi fun i => continuous_apply i.succ)).mul
        ((continuous_blockRotation N s.p).comp (continuous_apply 0))

theorem torusElem_mem_unitaryCompact :
    ∀ (L : List (Slot N)) (θ : Fin L.length → ℝ), torusElem L θ ∈ unitaryCompact ℝ N
  | [], _ => one_mem _
  | s :: rest, _ =>
      mul_mem (torusElem_mem_unitaryCompact rest _) (blockRotation_mem_unitaryCompact N s.p _)

/-- The measure on the torus parameters: Lebesgue measure on `(0, 2π]^r`. -/
def torusMeasure (r : ℕ) : Measure (Fin r → ℝ) :=
  Measure.pi fun _ => volume.restrict (Set.Ioc 0 (2 * Real.pi))

instance isFiniteMeasure_torusMeasure (r : ℕ) : IsFiniteMeasure (torusMeasure r) := by
  unfold torusMeasure
  infer_instance

/-- A continuous function is bounded on `O(N) g`. -/
theorem exists_bound_mul {F : Langlands.GeneralLinear N ℝ → ℂ} (hF : Continuous F)
    (g : Langlands.GeneralLinear N ℝ) :
    ∃ M : ℝ, ∀ k ∈ unitaryCompact ℝ N, ‖F (k * g)‖ ≤ M := by
  have hc : Continuous fun k : unitaryCompact ℝ N => F ((k : Langlands.GeneralLinear N ℝ) * g) :=
    hF.comp (continuous_subtype_val.mul continuous_const)
  obtain ⟨M, hM⟩ := (isCompact_range hc).isBounded.exists_norm_le
  exact ⟨M, fun k hk => hM _ ⟨⟨k, hk⟩, rfl⟩⟩

theorem integrable_torus {F : Langlands.GeneralLinear N ℝ → ℂ} (hF : Continuous F)
    (L : List (Slot N)) (g : Langlands.GeneralLinear N ℝ) :
    Integrable (fun θ => F (torusElem L θ * g)) (torusMeasure L.length) := by
  obtain ⟨M, hM⟩ := exists_bound_mul hF g
  refine Integrable.of_bound ?_ M
    (Filter.Eventually.of_forall fun θ => hM _ (torusElem_mem_unitaryCompact L θ))
  exact (hF.comp ((continuous_torusElem L).mul continuous_const)).aestronglyMeasurable

/-- **The torus coefficient as an integral.** -/
theorem coeffs_eq_integral {F : Langlands.GeneralLinear N ℝ → ℂ} (hF : Continuous F) :
    ∀ (L : List (Slot N)) (g : Langlands.GeneralLinear N ℝ),
      coeffs (zeroModes L) F g = ∫ θ, F (torusElem L θ * g) ∂torusMeasure L.length
  | [], g => by
    have : IsEmpty (Fin ([] : List (Slot N)).length) := by
      simp only [List.length_nil]; infer_instance
    have : torusMeasure ([] : List (Slot N)).length = Measure.dirac (fun i => isEmptyElim i) :=
      Measure.pi_of_empty _
    rw [this, integral_dirac]
    simp [coeffs, zeroModes, torusElem]
  | s :: rest, g => by
    have hstep : coeffs (zeroModes (s :: rest)) F g =
        ∫ a in (0 : ℝ)..2 * Real.pi, coeffs (zeroModes rest) F (blockRotation N s.p a * g) := by
      simp only [zeroModes, List.map_cons, coeffs, blockFourierCoefficient, setMode,
        Int.cast_zero, zero_mul, neg_zero, Complex.exp_zero, mul_one]
    rw [hstep, intervalIntegral.integral_of_le (by positivity)]
    simp_rw [coeffs_eq_integral hF rest]
    set μ0 : Measure ℝ := volume.restrict (Set.Ioc 0 (2 * Real.pi))
    set G : ℝ × (Fin rest.length → ℝ) → ℂ :=
      fun p => F (torusElem rest p.2 * (blockRotation N s.p p.1 * g)) with hG
    have hGc : Continuous G :=
      hF.comp (((continuous_torusElem rest).comp continuous_snd).mul
        (((continuous_blockRotation N s.p).comp continuous_fst).mul continuous_const))
    have hGi : Integrable G (μ0.prod (torusMeasure rest.length)) := by
      obtain ⟨M, hM⟩ := exists_bound_mul hF g
      refine Integrable.of_bound hGc.aestronglyMeasurable M
        (Filter.Eventually.of_forall fun p => ?_)
      rw [hG]
      simp only
      rw [← mul_assoc]
      exact hM _ (mul_mem (torusElem_mem_unitaryCompact rest _)
        (blockRotation_mem_unitaryCompact N s.p _))
    have h1 : ∫ a, ∫ θ, G (a, θ) ∂torusMeasure rest.length ∂μ0 =
        ∫ p, G p ∂(μ0.prod (torusMeasure rest.length)) := (integral_prod G hGi).symm
    have hmp := measurePreserving_piFinSuccAbove
      (fun _ : Fin (rest.length + 1) => volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi))) 0
    have h2 := hmp.integral_comp' G
    rw [show (fun a => ∫ θ, F (torusElem rest θ * (blockRotation N s.p a * g))
        ∂torusMeasure rest.length) = fun a => ∫ θ, G (a, θ) ∂torusMeasure rest.length from rfl, h1]
    change ∫ p, G p ∂((volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi))).prod
        (Measure.pi fun _ : Fin rest.length => volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi)))) =
      ∫ θ, F (torusElem (s :: rest) θ * g)
        ∂Measure.pi fun _ : Fin (rest.length + 1) => volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi))
    rw [← h2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    simp only [hG, MeasurableEquiv.piFinSuccAbove_apply, torusElem, mul_assoc]
    rfl

end Torus

/-! ## Torus elements of slots inside the blocks -/

section TorusOrth

variable {c : ℕ} {sz : Fin c → ℕ}

theorem torusElem_mem_blockOrth :
    ∀ (L : List (Slot (∑ i, sz i))),
      (∀ s ∈ L, cls sz ⟨s.p, by have := s.hp; omega⟩ = cls sz ⟨s.p + 1, s.hp⟩) →
      ∀ θ : Fin L.length → ℝ, torusElem L θ ∈ blockOrth sz
  | [], _, _ => one_mem _
  | s :: rest, h, _ =>
      mul_mem (torusElem_mem_blockOrth rest (fun t ht => h t (List.mem_cons_of_mem s ht)) _)
        (blockRotation_mem_blockOrth s.hp (h s List.mem_cons_self) _)

end TorusOrth

/-! ## Block orthogonal elements are block diagonal -/

section BlockDiag

variable {c : ℕ} {sz : Fin c → ℕ}

/-- The diagonal block `i` of a matrix. -/
def diagBlock (g : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) (i : Fin c) :
    Matrix (Fin (sz i)) (Fin (sz i)) ℝ :=
  Matrix.of fun a b => g (pos sz i a) (pos sz i b)

theorem blockDiagHom_diagBlock {g : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ}
    (hg : BlockZero sz g) : blockDiagHom sz (diagBlock g) = g := by
  ext p q
  obtain ⟨a, ha⟩ := pos_cls sz p
  obtain ⟨b, hb⟩ := pos_cls sz q
  rw [← ha, ← hb]
  by_cases hij : cls sz p = cls sz q
  · have : HEq a b ∨ True := Or.inr trivial
    revert a b
    rw [hij]
    intro a _ b _ _
    rw [blockDiagHom_pos_pos_self]
    rfl
  · rw [blockDiagHom_pos_pos_of_ne sz _ hij, hg]
    rwa [cls_pos, cls_pos]

theorem blockDiagHom_injective : Function.Injective (blockDiagHom sz) := by
  intro A B h
  funext i
  ext a b
  have := congrFun (congrFun h (pos sz i a)) (pos sz i b)
  rwa [blockDiagHom_pos_pos_self, blockDiagHom_pos_pos_self] at this

theorem diagBlock_mul_transpose {g : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ}
    (hg : BlockZero sz g) (hgg : g * gᵀ = 1) (i : Fin c) :
    diagBlock g i * (diagBlock g i)ᵀ = 1 := by
  have h : blockDiagHom sz (diagBlock g * fun i => (diagBlock g i)ᵀ) = blockDiagHom sz 1 := by
    rw [map_mul, ← blockDiagHom_transpose, blockDiagHom_diagBlock hg, hgg, map_one]
  exact congrFun (blockDiagHom_injective h) i

/-- The diagonal block `i` of a block orthogonal element, as an element of `O(sz_i)`. -/
def orthBlock {g : Langlands.GeneralLinear (∑ i, sz i) ℝ} (hg : g ∈ blockOrth sz) (i : Fin c) :
    unitaryCompact ℝ (sz i) :=
  ⟨⟨diagBlock (g : Matrix _ _ ℝ) i, (diagBlock (g : Matrix _ _ ℝ) i)ᵀ,
      diagBlock_mul_transpose hg.2 hg.1 i,
      mul_eq_one_comm.mp (diagBlock_mul_transpose hg.2 hg.1 i)⟩, by
    rw [mem_unitaryCompact_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial]
    exact mul_eq_one_comm.mp (diagBlock_mul_transpose hg.2 hg.1 i)⟩

theorem blockDiagGL_orthBlock {g : Langlands.GeneralLinear (∑ i, sz i) ℝ}
    (hg : g ∈ blockOrth sz) :
    blockDiagGL sz (fun i => ((orthBlock hg i : unitaryCompact ℝ (sz i)) :
      Langlands.GeneralLinear (sz i) ℝ)) = g := by
  ext : 1
  rw [blockDiagGL_val]
  exact blockDiagHom_diagBlock hg.2

end BlockDiag

/-! ## Invariance of the integral over `K_M` -/

section Invariance

open RealPrincipalSeriesDuality

attribute [local instance] measurableSpaceK

local instance borelSpaceK_lt (n : ℕ) : BorelSpace (unitaryCompact ℝ n) := ⟨rfl⟩

variable {c : ℕ} {sz : Fin c → ℕ}

theorem blockDiagGL_mul (ρ κ : ∀ i, unitaryCompact ℝ (sz i)) :
    blockDiagGL sz (fun i => ((ρ * κ) i : Langlands.GeneralLinear (sz i) ℝ)) =
      blockDiagGL sz (fun i => (ρ i : Langlands.GeneralLinear (sz i) ℝ)) *
        blockDiagGL sz (fun i => (κ i : Langlands.GeneralLinear (sz i) ℝ)) := by
  rw [← map_mul]
  rfl

/-- **Left invariance.** For block orthogonal `g`, `∫_{K_M} f(g diag(κ)) dκ = ∫_{K_M} f(diag(κ)) dκ`. -/
theorem integral_blockOrth_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Langlands.GeneralLinear (∑ i, sz i) ℝ → E) {g : Langlands.GeneralLinear (∑ i, sz i) ℝ}
    (hg : g ∈ blockOrth sz) :
    ∫ κ : (∀ i, unitaryCompact ℝ (sz i)),
        f (g * blockDiagGL sz fun i => (κ i : Langlands.GeneralLinear (sz i) ℝ))
      ∂Measure.pi (fun i => haarK (sz i)) =
      ∫ κ : (∀ i, unitaryCompact ℝ (sz i)),
        f (blockDiagGL sz fun i => (κ i : Langlands.GeneralLinear (sz i) ℝ))
      ∂Measure.pi (fun i => haarK (sz i)) := by
  set ρ : ∀ i, unitaryCompact ℝ (sz i) := orthBlock hg
  have h := integral_mul_left_eq_self (μ := Measure.pi fun i => haarK (sz i))
    (fun κ : (∀ i, unitaryCompact ℝ (sz i)) =>
      f (blockDiagGL sz fun i => (κ i : Langlands.GeneralLinear (sz i) ℝ))) ρ
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun κ => ?_)
  simp only
  rw [blockDiagGL_mul, blockDiagGL_orthBlock hg]

end Invariance

/-! ## Substitution by `Ad(g)` -/

section Subst

variable {c : ℕ} {sz : Fin c → ℕ}

theorem adCoord_adCoord_inv {g : Langlands.GeneralLinear (∑ i, sz i) ℝ} (hg : g ∈ blockOrth sz)
    (X : Coord sz → ℝ) :
    adCoord ((g⁻¹ : Langlands.GeneralLinear (∑ i, sz i) ℝ) : Matrix _ _ ℝ)
      (adCoord (g : Matrix _ _ ℝ) X) = X := by
  have hgi : g⁻¹ ∈ blockOrth sz := inv_mem hg
  apply lower_injective sz
  rw [lower_adCoord hgi.1 hgi.2, lower_adCoord hg.1 hg.2]
  have hinv : ((g⁻¹ : Langlands.GeneralLinear (∑ i, sz i) ℝ) :
      Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) =
      (g : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ)ᵀ :=
    Units.inv_eq_of_mul_eq_one_right hg.1
  rw [hinv, Matrix.transpose_transpose]
  have hT : (g : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ)ᵀ * (g : Matrix _ _ ℝ) = 1 :=
    transpose_mul_self_of_mem hg
  simp only [← Matrix.mul_assoc]
  rw [hT, Matrix.one_mul, Matrix.mul_assoc, hT, Matrix.mul_one]

theorem continuous_adCoord (k : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) :
    Continuous (adCoord k (sz := sz)) := by
  have hl : Continuous (lower sz) := by
    refine continuous_pi fun p => continuous_pi fun q => ?_
    simp only [lower, Matrix.of_apply]
    split_ifs
    all_goals first | exact continuous_apply _ | exact continuous_const
  refine continuous_pi fun pq => ?_
  simp only [adCoord]
  exact (((continuous_const.matrix_mul hl).matrix_mul continuous_const).matrix_elem _ _)

/-- `Ad(g)` as a homeomorphism of the coordinates of `N̄_Q`. -/
def adHomeomorph {g : Langlands.GeneralLinear (∑ i, sz i) ℝ} (hg : g ∈ blockOrth sz) :
    (Coord sz → ℝ) ≃ₜ (Coord sz → ℝ) where
  toFun := adCoord (g : Matrix _ _ ℝ)
  invFun := adCoord ((g⁻¹ : Langlands.GeneralLinear (∑ i, sz i) ℝ) : Matrix _ _ ℝ)
  left_inv X := adCoord_adCoord_inv hg X
  right_inv X := by
    have := adCoord_adCoord_inv (inv_mem hg) X
    rwa [inv_inv] at this
  continuous_toFun := continuous_adCoord _
  continuous_invFun := continuous_adCoord _

/-- **Substitution.** `∫ f(Ad(g) X) dX = ∫ f(X) dX` for block orthogonal `g`. -/
theorem integral_adCoord {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : Langlands.GeneralLinear (∑ i, sz i) ℝ} (hg : g ∈ blockOrth sz)
    (f : (Coord sz → ℝ) → E) :
    ∫ X, f (adCoord (g : Matrix _ _ ℝ) X) = ∫ X, f X :=
  (measurePreserving_adCoord hg).integral_comp (adHomeomorph hg).measurableEmbedding f

theorem lintegral_adCoord {g : Langlands.GeneralLinear (∑ i, sz i) ℝ} (hg : g ∈ blockOrth sz)
    (f : (Coord sz → ℝ) → ENNReal) :
    ∫⁻ X, f (adCoord (g : Matrix _ _ ℝ) X) = ∫⁻ X, f X :=
  (measurePreserving_adCoord hg).lintegral_comp_emb (adHomeomorph hg).measurableEmbedding f

end Subst

/-! ## Growth bounds in terms of Gram determinants -/

section Growth

open Langlands.GeneralLinear

variable {N : ℕ}

theorem gram_zero_eq (M : Matrix (Fin N) (Fin N) ℝ) : gram 0 M = M.det ^ 2 := by
  have : paddedGram 0 M = M * Mᵀ := by
    ext p q
    simp [paddedGram]
  rw [GramFormula.gram, this, Matrix.det_mul, Matrix.det_transpose, sq]

/-- **Growth bound for every `N`.** If `F(diag(a) u g) = c(a) F(g)` with
`‖c(a)‖ = ∏ |a_l|^{σ_l}` and `‖F‖ ≤ C` on `O(N)`, then for every `y` with `G_0(y) = 1` and
`κ ∈ O(N)`, `‖F(y κ)‖ ≤ C ∏_l G_l(y)^{ε_l}` whenever `ε_l = (σ_l − σ_{l−1})/2` for `l ≥ 1`. -/
theorem norm_le_gram_fin {F : Langlands.GeneralLinear N ℝ → ℂ} {c : (Fin N → ℝˣ) → ℂ}
    {σ : ℕ → ℝ}
    (hF : ∀ (a : Fin N → ℝˣ) (u : upperUnipotent N ℝ) (g : Langlands.GeneralLinear N ℝ),
      F ((Iwasawa.diagonalUnits a : Langlands.GeneralLinear N ℝ) *
        (u : Langlands.GeneralLinear N ℝ) * g) = c a * F g)
    (hc : ∀ a, ‖c a‖ = ∏ l : Fin N, |(a l : ℝ)| ^ σ l)
    {C : ℝ} (hC : ∀ k ∈ unitaryCompact ℝ N, ‖F k‖ ≤ C)
    (y : Langlands.GeneralLinear N ℝ) (hy : gram 0 (y : Matrix (Fin N) (Fin N) ℝ) = 1)
    {κ : Langlands.GeneralLinear N ℝ} (hκ : κ ∈ unitaryCompact ℝ N) (ε : Fin N → ℝ)
    (hε : ∀ l : Fin N, 0 < (l : ℕ) → ε l = (σ l - σ ((l : ℕ) - 1)) / 2) :
    ‖F (y * κ)‖ ≤ C * ∏ l : Fin N, gram (l : ℕ) (y : Matrix (Fin N) (Fin N) ℝ) ^ ε l := by
  cases N with
  | zero =>
    have : y * κ = κ := Subsingleton.elim _ _
    rw [this, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
    exact hC κ hκ
  | succ m =>
    have h := RealBlockChart.norm_le_gram hF hc hC y hy hκ
    refine h.trans (le_of_eq ?_)
    rw [Fin.prod_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ, hy, Real.one_rpow, one_mul]
    congr 1
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [hε l.succ (by simp)]
    simp

end Growth

end RealLeviTorus

end Langlands.Archimedean
