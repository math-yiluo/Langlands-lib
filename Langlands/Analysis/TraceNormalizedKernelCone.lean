import Langlands.Analysis.PositiveKernelHilbert
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.Module.LocallyConvex

/-! # A compact convex set of trace-normalized operator-valued positive kernels

Fix a complex `*`-algebra `𝒜` with a norm, a Hilbert space `W` with a Hilbert basis `e`, an index
type `κ` with real weights `c`, and a set `Rel` of relations. A function
`F : κ × κ × 𝒜 × W × W → ℂ`, read as `F (k, k', a, w, w') = ⟪w, B_k ρ(a) B_{k'}^* w'⟫`, is a *cone
element* if it is linear in `a`, sesquilinear in `(w, w')`, Hermitian, positive as a kernel on
`𝒜 × κ × W` (`(x, k, w), (y, k', w') ↦ F (k, k', x^* y, w, w')`), satisfies the domination
`ρ(a)^* ρ(a) ≤ ‖a‖²` in kernel form, and satisfies the relations `Rel`.

`coneSet` adds the weighted trace bound `traceSet c e`: for every finite set `s` of pairs `(k, b)` of
an index and a basis index, `∑_{(k,b) ∈ s} c_k Re F (k, k, 1, e_b, e_b) ≤ 1`; and the pointwise
bound `|F (k, k', a, w, w')| ≤ ‖a‖ ‖w‖ ‖w'‖ / √(c_k c_{k'})`; it is a compact convex subset of the
product space. The main result: if `coneSet` contains a nonzero point, it has a nonzero extreme
point (Krein–Milman). The module `Langlands.Analysis.TraceNormalizedKernelExtreme` gives each cone
element a Hilbert space with a `*`-representation `ρ` of `𝒜` and shows, for strictly positive
weights `c`, that at a nonzero extreme point every orthogonal projection commuting with `ρ(𝒜)` is
`0` or `1`.
-/

noncomputable section

open scoped ComplexConjugate InnerProductSpace ENNReal
open Filter Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Langlands.Analysis.KernelCone

variable {𝒜 : Type*} [NormedRing 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] [StarModule ℂ 𝒜]
variable {κ : Type*}
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/-- The coordinates `(k, k', a, w, w')`. -/
abbrev Coord (𝒜 κ W : Type*) : Type _ := κ × κ × 𝒜 × W × W

/-- The point of `Coord` giving the kernel value at `(i, j)`. -/
def pt (i j : 𝒜 × κ × W) : Coord 𝒜 κ W := (i.2.1, j.2.1, star i.1 * j.1, i.2.2, j.2.2)

/-- The kernel on `𝒜 × κ × W` defined by `F`. -/
def kernelOf (F : Coord 𝒜 κ W → ℂ) (i j : 𝒜 × κ × W) : ℂ := F (pt i j)

/-- Left multiplication of the first index component. -/
def lmul (a : 𝒜) (i : 𝒜 × κ × W) : 𝒜 × κ × W := (a * i.1, i.2)

/-- The defining conditions of a cone element. -/
structure IsConeElement (Rel : Set (κ × 𝒜 × κ × (W →L[ℂ] W))) (F : Coord 𝒜 κ W → ℂ) :
    Prop where
  add_mid : ∀ k k' x y w w', F (k, k', x + y, w, w') = F (k, k', x, w, w') + F (k, k', y, w, w')
  smul_mid : ∀ k k' (r : ℂ) x w w', F (k, k', r • x, w, w') = r * F (k, k', x, w, w')
  add_left : ∀ k k' x w₁ w₂ w',
    F (k, k', x, w₁ + w₂, w') = F (k, k', x, w₁, w') + F (k, k', x, w₂, w')
  smul_left : ∀ k k' x (r : ℂ) w w', F (k, k', x, r • w, w') = conj r * F (k, k', x, w, w')
  add_right : ∀ k k' x w w₁ w₂,
    F (k, k', x, w, w₁ + w₂) = F (k, k', x, w, w₁) + F (k, k', x, w, w₂)
  smul_right : ∀ k k' x w (r : ℂ) w', F (k, k', x, w, r • w') = r * F (k, k', x, w, w')
  herm : ∀ k k' x w w', conj (F (k', k, star x, w', w)) = F (k, k', x, w, w')
  pos : ∀ f : (𝒜 × κ × W) →₀ ℂ, 0 ≤ (kernelForm (kernelOf F) f f).re
  mul_le : ∀ (a : 𝒜) (f : (𝒜 × κ × W) →₀ ℂ),
    (kernelForm (fun i j => kernelOf F (lmul a i) (lmul a j)) f f).re ≤
      ‖a‖ ^ 2 * (kernelForm (kernelOf F) f f).re
  rel : ∀ r ∈ Rel, ∀ k' x w w', F (r.1, k', r.2.1 * x, w, w') = F (r.2.2.1, k', x, r.2.2.2 w, w')

/-- For all `k, k', a` there is a constant `M` with `‖F (k, k', a, w, w')‖ ≤ M ‖w‖ ‖w'‖`. This is
only a bound; sesquilinearity is part of `IsConeElement`. -/
def IsBoundedForm (F : Coord 𝒜 κ W → ℂ) : Prop :=
  ∀ k k' x, ∃ M : ℝ, ∀ w w', ‖F (k, k', x, w, w')‖ ≤ M * (‖w‖ * ‖w'‖)

variable {Rel : Set (κ × 𝒜 × κ × (W →L[ℂ] W))}

/-! ### Algebraic closure properties -/

theorem kernelOf_add (F₁ F₂ : Coord 𝒜 κ W → ℂ) :
    kernelOf (F₁ + F₂) = kernelOf F₁ + kernelOf F₂ := rfl

theorem kernelOf_smul (t : ℂ) (F : Coord 𝒜 κ W → ℂ) : kernelOf (t • F) = t • kernelOf F := rfl

theorem IsConeElement.zero : IsConeElement Rel (0 : Coord 𝒜 κ W → ℂ) where
  add_mid := by simp
  smul_mid := by simp
  add_left := by simp
  smul_left := by simp
  add_right := by simp
  smul_right := by simp
  herm := by simp
  pos f := by simp [kernelForm, kernelOf]
  mul_le a f := by simp [kernelForm, kernelOf]
  rel := by simp

theorem IsConeElement.add {F₁ F₂ : Coord 𝒜 κ W → ℂ} (h₁ : IsConeElement Rel F₁)
    (h₂ : IsConeElement Rel F₂) : IsConeElement Rel (F₁ + F₂) where
  add_mid k k' x y w w' := by simp only [Pi.add_apply, h₁.add_mid, h₂.add_mid]; ring
  smul_mid k k' r x w w' := by simp only [Pi.add_apply, h₁.smul_mid, h₂.smul_mid]; ring
  add_left k k' x w₁ w₂ w' := by simp only [Pi.add_apply, h₁.add_left, h₂.add_left]; ring
  smul_left k k' x r w w' := by simp only [Pi.add_apply, h₁.smul_left, h₂.smul_left]; ring
  add_right k k' x w w₁ w₂ := by simp only [Pi.add_apply, h₁.add_right, h₂.add_right]; ring
  smul_right k k' x w r w' := by simp only [Pi.add_apply, h₁.smul_right, h₂.smul_right]; ring
  herm k k' x w w' := by simp only [Pi.add_apply, map_add, h₁.herm, h₂.herm]
  pos f := by
    rw [kernelOf_add, kernelForm_add_kernel, Complex.add_re]
    exact add_nonneg (h₁.pos f) (h₂.pos f)
  mul_le a f := by
    have e : (fun i j => kernelOf (F₁ + F₂) (lmul a i) (lmul a j)) =
        (fun i j => kernelOf F₁ (lmul a i) (lmul a j)) +
          fun i j => kernelOf F₂ (lmul a i) (lmul a j) := rfl
    rw [e, kernelForm_add_kernel, kernelOf_add, kernelForm_add_kernel, Complex.add_re,
      Complex.add_re, mul_add]
    exact add_le_add (h₁.mul_le a f) (h₂.mul_le a f)
  rel r hr k' x w w' := by simp only [Pi.add_apply, h₁.rel r hr, h₂.rel r hr]

theorem IsConeElement.smul {F : Coord 𝒜 κ W → ℂ} (hF : IsConeElement Rel F) {t : ℝ}
    (ht : 0 ≤ t) : IsConeElement Rel (t • F) where
  add_mid k k' x y w w' := by simp only [Pi.smul_apply, hF.add_mid, smul_add]
  smul_mid k k' r x w w' := by
    simp only [Pi.smul_apply, hF.smul_mid, Complex.real_smul]; ring
  add_left k k' x w₁ w₂ w' := by simp only [Pi.smul_apply, hF.add_left, smul_add]
  smul_left k k' x r w w' := by
    simp only [Pi.smul_apply, hF.smul_left, Complex.real_smul]; ring
  add_right k k' x w w₁ w₂ := by simp only [Pi.smul_apply, hF.add_right, smul_add]
  smul_right k k' x w r w' := by
    simp only [Pi.smul_apply, hF.smul_right, Complex.real_smul]; ring
  herm k k' x w w' := by
    simp only [Pi.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal, hF.herm]
  pos f := by
    have e : kernelOf (t • F) = (t : ℂ) • kernelOf F := by
      funext i j; simp [kernelOf, Complex.real_smul]
    rw [e, kernelForm_smul_kernel, Complex.re_ofReal_mul]
    exact mul_nonneg ht (hF.pos f)
  mul_le a f := by
    have e : kernelOf (t • F) = (t : ℂ) • kernelOf F := by
      funext i j; simp [kernelOf, Complex.real_smul]
    have e' : (fun i j => kernelOf (t • F) (lmul a i) (lmul a j)) =
        (t : ℂ) • fun i j => kernelOf F (lmul a i) (lmul a j) := by
      funext i j; simp [kernelOf, Complex.real_smul]
    rw [e', e, kernelForm_smul_kernel, kernelForm_smul_kernel, Complex.re_ofReal_mul,
      Complex.re_ofReal_mul]
    nlinarith [hF.mul_le a f, ht]
  rel r hr k' x w w' := by simp only [Pi.smul_apply, hF.rel r hr]

/-! ### The compact convex set -/

variable {β : Type*}

/-- The pointwise bound. -/
def boundSet (c : κ → ℝ) : Set (Coord 𝒜 κ W → ℂ) :=
  {F | ∀ k k' x w w', ‖F (k, k', x, w, w')‖ ≤ ‖x‖ * ‖w‖ * ‖w'‖ / Real.sqrt (c k * c k')}

/-- The weighted trace bound: `∑_{(k,b) ∈ s} c_k Re F (k, k, 1, e_b, e_b) ≤ 1` for every finite set
`s` of pairs `(k, b)`. -/
def traceSet (c : κ → ℝ) (e : HilbertBasis β ℂ W) : Set (Coord 𝒜 κ W → ℂ) :=
  {F | ∀ s : Finset (κ × β), ∑ p ∈ s, c p.1 * (F (p.1, p.1, 1, e p.2, e p.2)).re ≤ 1}

/-- The compact convex set of trace-normalized cone elements. -/
def coneSet (Rel : Set (κ × 𝒜 × κ × (W →L[ℂ] W))) (c : κ → ℝ) (e : HilbertBasis β ℂ W) :
    Set (Coord 𝒜 κ W → ℂ) :=
  {F | IsConeElement Rel F} ∩ traceSet c e ∩ boundSet c

theorem continuous_kernelForm {ι : Type*} (m : ι → ι → Coord 𝒜 κ W) (f g : ι →₀ ℂ) :
    Continuous fun F : Coord 𝒜 κ W → ℂ => kernelForm (fun i j => F (m i j)) f g := by
  unfold kernelForm
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact continuous_const.mul (continuous_apply _)

theorem isClosed_isConeElement :
    IsClosed {F : Coord 𝒜 κ W → ℂ | IsConeElement Rel F} := by
  have e : {F : Coord 𝒜 κ W → ℂ | IsConeElement Rel F} =
      {F | ∀ k k' x y w w', F (k, k', x + y, w, w') = F (k, k', x, w, w') + F (k, k', y, w, w')} ∩
      {F | ∀ k k' (r : ℂ) x w w', F (k, k', r • x, w, w') = r * F (k, k', x, w, w')} ∩
      {F | ∀ k k' x w₁ w₂ w',
        F (k, k', x, w₁ + w₂, w') = F (k, k', x, w₁, w') + F (k, k', x, w₂, w')} ∩
      {F | ∀ k k' x (r : ℂ) w w', F (k, k', x, r • w, w') = conj r * F (k, k', x, w, w')} ∩
      {F | ∀ k k' x w w₁ w₂,
        F (k, k', x, w, w₁ + w₂) = F (k, k', x, w, w₁) + F (k, k', x, w, w₂)} ∩
      {F | ∀ k k' x w (r : ℂ) w', F (k, k', x, w, r • w') = r * F (k, k', x, w, w')} ∩
      {F | ∀ k k' x w w', conj (F (k', k, star x, w', w)) = F (k, k', x, w, w')} ∩
      {F | ∀ f : (𝒜 × κ × W) →₀ ℂ, 0 ≤ (kernelForm (kernelOf F) f f).re} ∩
      {F | ∀ (a : 𝒜) (f : (𝒜 × κ × W) →₀ ℂ),
        (kernelForm (fun i j => kernelOf F (lmul a i) (lmul a j)) f f).re ≤
          ‖a‖ ^ 2 * (kernelForm (kernelOf F) f f).re} ∩
      {F | ∀ r ∈ Rel, ∀ k' x w w',
        F (r.1, k', r.2.1 * x, w, w') = F (r.2.2.1, k', x, r.2.2.2 w, w')} := by
    ext F
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · intro h
      exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨h.add_mid, h.smul_mid⟩, h.add_left⟩, h.smul_left⟩, h.add_right⟩,
        h.smul_right⟩, h.herm⟩, h.pos⟩, h.mul_le⟩, h.rel⟩
    · rintro ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩
      exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  rw [e]
  have ca : ∀ p : Coord 𝒜 κ W, Continuous fun F : Coord 𝒜 κ W → ℂ => F p :=
    fun p => continuous_apply p
  refine IsClosed.inter (IsClosed.inter (IsClosed.inter (IsClosed.inter (IsClosed.inter
    (IsClosed.inter (IsClosed.inter (IsClosed.inter (IsClosed.inter ?_ ?_) ?_) ?_) ?_) ?_) ?_)
    ?_) ?_) ?_
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun k => isClosed_iInter fun k' => isClosed_iInter fun x =>
      isClosed_iInter fun y => isClosed_iInter fun w => isClosed_iInter fun w' =>
        isClosed_eq (ca _) ((ca _).add (ca _))
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun k => isClosed_iInter fun k' => isClosed_iInter fun r =>
      isClosed_iInter fun x => isClosed_iInter fun w => isClosed_iInter fun w' =>
        isClosed_eq (ca _) (continuous_const.mul (ca _))
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun k => isClosed_iInter fun k' => isClosed_iInter fun x =>
      isClosed_iInter fun w₁ => isClosed_iInter fun w₂ => isClosed_iInter fun w' =>
        isClosed_eq (ca _) ((ca _).add (ca _))
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun k => isClosed_iInter fun k' => isClosed_iInter fun x =>
      isClosed_iInter fun r => isClosed_iInter fun w => isClosed_iInter fun w' =>
        isClosed_eq (ca _) (continuous_const.mul (ca _))
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun k => isClosed_iInter fun k' => isClosed_iInter fun x =>
      isClosed_iInter fun w => isClosed_iInter fun w₁ => isClosed_iInter fun w₂ =>
        isClosed_eq (ca _) ((ca _).add (ca _))
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun k => isClosed_iInter fun k' => isClosed_iInter fun x =>
      isClosed_iInter fun w => isClosed_iInter fun r => isClosed_iInter fun w' =>
        isClosed_eq (ca _) (continuous_const.mul (ca _))
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun k => isClosed_iInter fun k' => isClosed_iInter fun x =>
      isClosed_iInter fun w => isClosed_iInter fun w' =>
        isClosed_eq (Complex.continuous_conj.comp (ca _)) (ca _)
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun f => isClosed_le continuous_const
      (Complex.continuous_re.comp (continuous_kernelForm (fun i j => pt i j) f f))
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun a => isClosed_iInter fun f => isClosed_le
      (Complex.continuous_re.comp
        (continuous_kernelForm (fun i j => pt (lmul a i) (lmul a j)) f f))
      (continuous_const.mul
        (Complex.continuous_re.comp (continuous_kernelForm (fun i j => pt i j) f f)))
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun r => isClosed_iInter fun _ => isClosed_iInter fun k' =>
      isClosed_iInter fun x => isClosed_iInter fun w => isClosed_iInter fun w' =>
        isClosed_eq (ca _) (ca _)

theorem isClosed_traceSet (c : κ → ℝ) (e : HilbertBasis β ℂ W) :
    IsClosed (traceSet (𝒜 := 𝒜) c e) := by
  unfold traceSet
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun s => isClosed_le
    (continuous_finsetSum _ fun p _ =>
      continuous_const.mul (Complex.continuous_re.comp (continuous_apply _)))
    continuous_const

theorem isClosed_boundSet (c : κ → ℝ) : IsClosed (boundSet (𝒜 := 𝒜) (W := W) c) := by
  unfold boundSet
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun k => isClosed_iInter fun k' => isClosed_iInter fun x =>
    isClosed_iInter fun w => isClosed_iInter fun w' =>
      isClosed_le (continuous_norm.comp (continuous_apply _)) continuous_const

theorem isCompact_coneSet (c : κ → ℝ) (e : HilbertBasis β ℂ W) :
    IsCompact (coneSet Rel c e) := by
  have hsub : coneSet Rel c e ⊆ Set.pi Set.univ fun p : Coord 𝒜 κ W =>
      Metric.closedBall (0 : ℂ) (‖p.2.2.1‖ * ‖p.2.2.2.1‖ * ‖p.2.2.2.2‖ /
        Real.sqrt (c p.1 * c p.2.1)) := by
    rintro F ⟨-, hB⟩ p -
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hB _ _ _ _ _
  refine (isCompact_univ_pi fun p => isCompact_closedBall _ _).of_isClosed_subset ?_ hsub
  exact (isClosed_isConeElement.inter (isClosed_traceSet c e)).inter (isClosed_boundSet c)

theorem convex_coneSet (c : κ → ℝ) (e : HilbertBasis β ℂ W) :
    Convex ℝ (coneSet Rel c e) := by
  rintro F ⟨⟨hF, hFt⟩, hFb⟩ G ⟨⟨hG, hGt⟩, hGb⟩ a b ha hb hab
  refine ⟨⟨(hF.smul ha).add (hG.smul hb), fun s => ?_⟩, fun k k' x w w' => ?_⟩
  · have h1 := hFt s
    have h2 := hGt s
    calc ∑ p ∈ s, c p.1 * ((a • F + b • G) (p.1, p.1, 1, e p.2, e p.2)).re
        = a * ∑ p ∈ s, c p.1 * (F (p.1, p.1, 1, e p.2, e p.2)).re +
            b * ∑ p ∈ s, c p.1 * (G (p.1, p.1, 1, e p.2, e p.2)).re := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun p _ => ?_
          simp only [Pi.add_apply, Pi.smul_apply, Complex.add_re, Complex.real_smul,
            Complex.re_ofReal_mul]
          ring
      _ ≤ a * 1 + b * 1 := add_le_add (mul_le_mul_of_nonneg_left h1 ha)
          (mul_le_mul_of_nonneg_left h2 hb)
      _ = 1 := by rw [mul_one, mul_one, hab]
  · simp only [Pi.add_apply, Pi.smul_apply]
    calc ‖a • F (k, k', x, w, w') + b • G (k, k', x, w, w')‖
        ≤ a * ‖F (k, k', x, w, w')‖ + b * ‖G (k, k', x, w, w')‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
      _ ≤ a * (‖x‖ * ‖w‖ * ‖w'‖ / Real.sqrt (c k * c k')) +
            b * (‖x‖ * ‖w‖ * ‖w'‖ / Real.sqrt (c k * c k')) :=
          add_le_add (mul_le_mul_of_nonneg_left (hFb _ _ _ _ _) ha)
            (mul_le_mul_of_nonneg_left (hGb _ _ _ _ _) hb)
      _ = _ := by rw [← add_mul, hab, one_mul]

/-- Krein–Milman: a compact convex set with a nonzero point has a nonzero extreme point. -/
theorem exists_extremePoint_ne_zero (c : κ → ℝ) (e : HilbertBasis β ℂ W)
    {F₀ : Coord 𝒜 κ W → ℂ} (hF₀ : F₀ ∈ coneSet Rel c e) (hne : F₀ ≠ 0) :
    ∃ F ∈ (coneSet Rel c e).extremePoints ℝ, F ≠ 0 := by
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  have hsub : (coneSet Rel c e).extremePoints ℝ ⊆ {0} := fun F hF => h F hF
  have hcl := closure_convexHull_extremePoints (isCompact_coneSet (Rel := Rel) c e)
    (convex_coneSet c e)
  have : coneSet Rel c e ⊆ {0} := by
    rw [← hcl]
    refine closure_minimal ((convexHull_mono hsub).trans ?_) isClosed_singleton
    rw [convexHull_singleton]
  exact hne (this hF₀)

end Langlands.Analysis.KernelCone
