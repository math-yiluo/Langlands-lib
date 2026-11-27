import Langlands.Geometry.Manifold.SmoothGroupDifferential

/-! # Iterated invariant derivatives along lists of directions

For a Lie group `G` and a list `[X₁, …, Xₖ]` of identity tangent vectors,
`listDirectionalDerivative [X₁, …, Xₖ] f` applies the invariant derivative
`groupDirectionalValue X₁` first and `groupDirectionalValue Xₖ` last. This file proves that these
operators preserve smoothness, are additive on smooth functions, commute with left translation and
kill constants, the product rule for one derivative, and that a product of a function whose
iterated derivatives are bounded by a weight with a function whose iterated derivatives are
bounded again has iterated derivatives bounded by the weight. -/

noncomputable section

open scoped Manifold ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Geometry.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace E G]

local notation "𝓘E" => 𝓘(ℝ, E)

/-- The iterated invariant derivative along a list of directions; the head of the list is
applied first. -/
def listDirectionalDerivative (w : List (GroupLieAlgebra 𝓘E G)) (f : G → ℂ) : G → ℂ :=
  w.foldl (fun h X => groupDirectionalValue 𝓘E X h) f

@[simp]
theorem listDirectionalDerivative_nil (f : G → ℂ) :
    listDirectionalDerivative ([] : List (GroupLieAlgebra 𝓘E G)) f = f := rfl

@[simp]
theorem listDirectionalDerivative_cons (X : GroupLieAlgebra 𝓘E G)
    (w : List (GroupLieAlgebra 𝓘E G)) (f : G → ℂ) :
    listDirectionalDerivative (X :: w) f =
      listDirectionalDerivative w (groupDirectionalValue 𝓘E X f) := rfl

theorem listDirectionalDerivative_append_singleton (w : List (GroupLieAlgebra 𝓘E G))
    (X : GroupLieAlgebra 𝓘E G) (f : G → ℂ) :
    listDirectionalDerivative (w ++ [X]) f =
      groupDirectionalValue 𝓘E X (listDirectionalDerivative w f) := by
  simp only [listDirectionalDerivative, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- Left translation commutes with iterated invariant derivatives. -/
theorem listDirectionalDerivative_leftTranslation (w : List (GroupLieAlgebra 𝓘E G)) (a : G) :
    ∀ f : G → ℂ, listDirectionalDerivative w (fun x => f (a * x)) =
      fun x => listDirectionalDerivative w f (a * x) := by
  induction w with
  | nil => intro f; rfl
  | cons X w ih =>
    intro f
    rw [listDirectionalDerivative_cons, listDirectionalDerivative_cons]
    have h : groupDirectionalValue 𝓘E X (fun x => f (a * x)) =
        fun x => groupDirectionalValue 𝓘E X f (a * x) :=
      funext fun x => groupDirectionalValue_leftTranslation 𝓘E X a f x
    rw [h, ih]

/-- The invariant derivative of a constant vanishes. -/
theorem groupDirectionalValue_const (X : GroupLieAlgebra 𝓘E G) (c : ℂ) :
    groupDirectionalValue 𝓘E X (fun _ : G => c) = 0 := by
  funext g
  change mvfderiv 𝓘E (fun _ : G => c) 1 X = 0
  exact congrArg (fun D : TangentSpace 𝓘E (1 : G) →L[ℝ] ℂ => D X) (mvfderiv_const (I := 𝓘E) c)

variable [LieGroup 𝓘(ℝ, E) ∞ G]

theorem contMDiff_listDirectionalDerivative (w : List (GroupLieAlgebra 𝓘E G)) :
    ∀ {f : G → ℂ}, ContMDiff 𝓘E 𝓘(ℝ, ℂ) ∞ f →
      ContMDiff 𝓘E 𝓘(ℝ, ℂ) ∞ (listDirectionalDerivative w f) := by
  induction w with
  | nil => intro f hf; exact hf
  | cons X w ih =>
    intro f hf
    exact ih (contMDiff_groupDirectionalValue 𝓘E X hf)

/-- Iterated invariant derivatives are additive on smooth functions. -/
theorem listDirectionalDerivative_add (w : List (GroupLieAlgebra 𝓘E G)) :
    ∀ {f h : G → ℂ}, ContMDiff 𝓘E 𝓘(ℝ, ℂ) ∞ f → ContMDiff 𝓘E 𝓘(ℝ, ℂ) ∞ h →
      listDirectionalDerivative w (f + h) =
        listDirectionalDerivative w f + listDirectionalDerivative w h := by
  induction w with
  | nil => intro f h _ _; rfl
  | cons X w ih =>
    intro f h hf hh
    rw [listDirectionalDerivative_cons, listDirectionalDerivative_cons,
      listDirectionalDerivative_cons]
    have hadd : groupDirectionalValue 𝓘E X (f + h) =
        groupDirectionalValue 𝓘E X f + groupDirectionalValue 𝓘E X h :=
      funext fun g => groupDirectionalValue_add 𝓘E X hf hh g
    rw [hadd]
    exact ih (contMDiff_groupDirectionalValue 𝓘E X hf) (contMDiff_groupDirectionalValue 𝓘E X hh)

/-- Adding a constant does not change iterated invariant derivatives along a nonempty list. -/
theorem listDirectionalDerivative_add_const {w : List (GroupLieAlgebra 𝓘E G)} (hw : w ≠ [])
    {f : G → ℂ} (hf : ContMDiff 𝓘E 𝓘(ℝ, ℂ) ∞ f) (c : ℂ) :
    listDirectionalDerivative w (fun x => f x + c) = listDirectionalDerivative w f := by
  obtain ⟨X, v, rfl⟩ := List.exists_cons_of_ne_nil hw
  rw [listDirectionalDerivative_cons, listDirectionalDerivative_cons]
  have h : groupDirectionalValue 𝓘E X (fun x => f x + c) = groupDirectionalValue 𝓘E X f := by
    funext g
    have hsum := groupDirectionalValue_add 𝓘E X hf
      (contMDiff_const : ContMDiff 𝓘E 𝓘(ℝ, ℂ) ∞ (fun _ : G => c)) g
    rw [groupDirectionalValue_const, Pi.zero_apply, add_zero] at hsum
    exact hsum
  rw [h]

omit [Group G] [LieGroup 𝓘(ℝ, E) ∞ G] in
/-- Products of smooth complex functions are smooth. -/
theorem contMDiff_mul_complex {f h : G → ℂ} (hf : ContMDiff 𝓘E 𝓘(ℝ, ℂ) ∞ f)
    (hh : ContMDiff 𝓘E 𝓘(ℝ, ℂ) ∞ h) : ContMDiff 𝓘E 𝓘(ℝ, ℂ) ∞ (f * h) :=
  (contDiff_mul : ContDiff ℝ ∞ (fun z : ℂ × ℂ => z.1 * z.2)).contMDiff.comp
    (hf.prodMk_space hh)

/-- The product rule for one invariant derivative of smooth functions. -/
theorem groupDirectionalValue_mul (X : GroupLieAlgebra 𝓘E G) {f h : G → ℂ}
    (hf : ContMDiff 𝓘E 𝓘(ℝ, ℂ) ∞ f) (hh : ContMDiff 𝓘E 𝓘(ℝ, ℂ) ∞ h) (g : G) :
    groupDirectionalValue 𝓘E X (f * h) g =
      groupDirectionalValue 𝓘E X f g * h g + f g * groupDirectionalValue 𝓘E X h g := by
  let p (z : G) := f (g * z)
  let q (z : G) := h (g * z)
  have hm : ContMDiff 𝓘E 𝓘E ∞ (fun z : G => g * z) := contMDiff_const.mul contMDiff_id
  have hp : MDifferentiableAt 𝓘E 𝓘(ℝ, ℂ) p (1 : G) := (hf.comp hm).mdifferentiableAt (by simp)
  have hq : MDifferentiableAt 𝓘E 𝓘(ℝ, ℂ) q (1 : G) := (hh.comp hm).mdifferentiableAt (by simp)
  have hd := hp.hasMFDerivAt.mul hq.hasMFDerivAt
  have hd' : mvfderiv 𝓘E (p * q) 1 = p 1 • mvfderiv 𝓘E q 1 + q 1 • mvfderiv 𝓘E p 1 :=
    hd.mfderiv
  have hX := congrArg (fun D : TangentSpace 𝓘E (1 : G) →L[ℝ] ℂ => D X) hd'
  change mvfderiv 𝓘E (p * q) 1 X = mvfderiv 𝓘E p 1 X * h g + f g * mvfderiv 𝓘E q 1 X
  have hp1 : p 1 = f g := by simp only [p, mul_one]
  have hq1 : q 1 = h g := by simp only [q, mul_one]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul,
    hp1, hq1] at hX
  rw [hX]
  ring

/-- Products with functions all of whose iterated derivatives are bounded preserve weighted
bounds on all iterated derivatives. The functions are indexed by a parameter `b`, and the
constants are uniform in `b` and in the point. -/
theorem exists_bound_listDirectionalDerivative_mul {β : Type*} (wt : β → G → ℝ)
    (w : List (GroupLieAlgebra 𝓘E G)) :
    ∀ (f h : β → G → ℂ), (∀ b, ContMDiff 𝓘E 𝓘(ℝ, ℂ) ∞ (f b)) →
      (∀ b, ContMDiff 𝓘E 𝓘(ℝ, ℂ) ∞ (h b)) →
      (∀ v : List (GroupLieAlgebra 𝓘E G), ∃ C : ℝ, ∀ b x,
        ‖listDirectionalDerivative v (f b) x‖ ≤ C * wt b x) →
      (∀ v : List (GroupLieAlgebra 𝓘E G), ∃ C : ℝ, ∀ b x,
        ‖listDirectionalDerivative v (h b) x‖ ≤ C) →
      ∃ C : ℝ, ∀ b x, ‖listDirectionalDerivative w (f b * h b) x‖ ≤ C * wt b x := by
  induction w with
  | nil =>
    intro f h _ _ hfb hhb
    obtain ⟨C₁, hC₁⟩ := hfb []
    obtain ⟨C₂, hC₂⟩ := hhb []
    refine ⟨C₁ * C₂, fun b x => ?_⟩
    have h1 : ‖f b x‖ ≤ C₁ * wt b x := hC₁ b x
    have h2 : ‖h b x‖ ≤ C₂ := hC₂ b x
    change ‖f b x * h b x‖ ≤ _
    rw [norm_mul]
    calc ‖f b x‖ * ‖h b x‖ ≤ (C₁ * wt b x) * C₂ :=
          mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
      _ = C₁ * C₂ * wt b x := by ring
  | cons X w ih =>
    intro f h hf hh hfb hhb
    have hdf (b : β) := contMDiff_groupDirectionalValue 𝓘E X (hf b)
    have hdh (b : β) := contMDiff_groupDirectionalValue 𝓘E X (hh b)
    obtain ⟨C₁, hC₁⟩ := ih (fun b => groupDirectionalValue 𝓘E X (f b)) h hdf hh
      (fun v => hfb (X :: v)) hhb
    obtain ⟨C₂, hC₂⟩ := ih f (fun b => groupDirectionalValue 𝓘E X (h b)) hf hdh hfb
      (fun v => hhb (X :: v))
    refine ⟨C₁ + C₂, fun b x => ?_⟩
    have hprod : groupDirectionalValue 𝓘E X (f b * h b) =
        groupDirectionalValue 𝓘E X (f b) * h b + f b * groupDirectionalValue 𝓘E X (h b) :=
      funext fun g => groupDirectionalValue_mul X (hf b) (hh b) g
    rw [listDirectionalDerivative_cons, hprod,
      listDirectionalDerivative_add w (contMDiff_mul_complex (hdf b) (hh b))
        (contMDiff_mul_complex (hf b) (hdh b)), Pi.add_apply]
    calc _ ≤ ‖listDirectionalDerivative w (groupDirectionalValue 𝓘E X (f b) * h b) x‖ +
          ‖listDirectionalDerivative w (f b * groupDirectionalValue 𝓘E X (h b)) x‖ :=
          norm_add_le _ _
      _ ≤ C₁ * wt b x + C₂ * wt b x := add_le_add (hC₁ b x) (hC₂ b x)
      _ = (C₁ + C₂) * wt b x := by ring

/-- A smooth function that changes only by additive constants under left translation by the
elements of a set `S`, where `S · C` covers the group for a compact `C`, has bounded iterated
invariant derivatives along every nonempty list of directions. -/
theorem exists_bound_listDirectionalDerivative_of_quasiInvariant {s : G → ℂ}
    (hs : ContMDiff 𝓘E 𝓘(ℝ, ℂ) ∞ s) (S C : Set G) (hC : IsCompact C)
    (hcover : ∀ a, ∃ x ∈ S, ∃ c ∈ C, a = x * c)
    (hquasi : ∀ x ∈ S, ∃ κ : ℂ, ∀ a, s (x * a) = s a + κ)
    {w : List (GroupLieAlgebra 𝓘E G)} (hw : w ≠ []) :
    ∃ M : ℝ, ∀ a, ‖listDirectionalDerivative w s a‖ ≤ M := by
  have hcont : Continuous (listDirectionalDerivative w s) :=
    (contMDiff_listDirectionalDerivative w hs).continuous
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨M, fun a => ?_⟩
  obtain ⟨x, hx, c, hc, rfl⟩ := hcover a
  obtain ⟨κ, hκ⟩ := hquasi x hx
  have htrans := congrFun (listDirectionalDerivative_leftTranslation w x s) c
  have hshift : (fun y => s (x * y)) = fun y => s y + κ := funext hκ
  rw [hshift, listDirectionalDerivative_add_const hw hs] at htrans
  rw [← htrans]
  exact hM c hc

end Langlands.Geometry.Manifold
