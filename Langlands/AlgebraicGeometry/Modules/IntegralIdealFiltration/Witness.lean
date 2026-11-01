import Langlands.AlgebraicGeometry.Modules.IntegralIdealFiltration.MinimalPoint
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_isIntegral_subscheme_vanishingIdeal

/-! # Sections extending multiples of a minimal associated section -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Langlands.Cohomology

namespace Langlands.AlgebraicGeometry.Modules

namespace IntegralIdealFiltration

open AffineVanishing QuasicoherentLocal Scheme.IdealSheafData

variable {X : Scheme.{u}} {Q : X.Modules}

/-- A section `s` over an affine open `U` with prime annihilator `p`, relative to whose point the
module is torsion free (see `exists_minimal_witness`). -/
structure Witness (Q : X.Modules) where
  /-- the affine open -/
  U : X.affineOpens
  /-- the section -/
  s : Γ(Q, U.1)
  /-- the annihilator of `s` -/
  p : PrimeSpectrum Γ(X, U.1)
  ann : ∀ c, c • s = 0 ↔ c ∈ p.asIdeal
  tor : ∀ (W : X.Opens) (t : Γ(Q, W)),
    Killed (vanishingIdeal (Closeds.closure {U.2.fromSpec p})) t →
    (∀ (V : X.affineOpens) (hV : V.1 ≤ W ⊓ U.1), Cech.res (hV.trans inf_le_left) t = 0) → t = 0

theorem nonempty_witness [IsNoetherian X] [Q.IsQuasicoherent] (hQ : ¬ IsZero Q) :
    Nonempty (Witness Q) := by
  obtain ⟨U, s, p, hann, htor⟩ := exists_minimal_witness hQ
  exact ⟨⟨U, s, p, hann, htor⟩⟩

namespace Witness

variable (w : Witness Q)

/-- The point of `X` given by the annihilator prime. -/
def pt : X := w.U.2.fromSpec w.p

/-- The closure of the point. -/
def Zc : Closeds X := Closeds.closure {w.pt}

/-- The vanishing ideal of the closure of the point. -/
abbrev J : X.IdealSheafData := vanishingIdeal w.Zc

/-- The reduced closed subscheme on the closure of the point. -/
abbrev Z : Scheme.{u} := w.J.subscheme

/-- The closed immersion of the reduced closed subscheme. -/
abbrev i : w.Z ⟶ X := w.J.subschemeι

lemma pt_mem_U : w.pt ∈ w.U.1 := by
  have h := Set.mem_range_self (f := ⇑w.U.2.fromSpec) w.p
  rw [w.U.2.range_fromSpec] at h
  exact h

lemma pt_mem_Zc : w.pt ∈ w.Zc := subset_closure rfl

lemma pt_mem_of_mem_Zc {W : X.Opens} {y : X} (hyW : y ∈ W) (hyZ : y ∈ w.Zc) : w.pt ∈ W := by
  obtain ⟨z, hzW, hz⟩ := (mem_closure_iff.1 hyZ) W W.isOpen hyW
  rw [Set.mem_singleton_iff.1 hz] at hzW
  exact hzW

lemma J_U : w.J.ideal w.U = w.p.asIdeal := vanishingIdeal_closure_fromSpec w.U w.p

lemma s_killed : Killed w.J w.s :=
  killed_of_affine w.U.2 fun c hc => (w.ann c).2 (by rw [← w.J_U]; exact hc)

lemma ideal_eq_top {V : X.affineOpens} (hV : ∀ y ∈ V.1, y ∉ w.Zc) : w.J.ideal V = ⊤ := by
  rw [vanishingIdeal_ideal]
  have : V.2.fromSpec ⁻¹' (w.Zc : Set X) = ∅ := by
    ext q
    simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
    intro hq
    apply hV _ _ hq
    have h := Set.mem_range_self (f := ⇑V.2.fromSpec) q
    rw [V.2.range_fromSpec] at h
    exact h
  rw [this, PrimeSpectrum.vanishingIdeal_empty]

lemma range_i : Set.range w.i = w.Zc := by
  rw [range_subschemeι, coe_support_vanishingIdeal]

instance : IsIntegral w.Z :=
  Scheme.isIntegral_subscheme_vanishingIdeal w.Zc isIrreducible_singleton.closure

lemma app_surjective (V : X.affineOpens) : Function.Surjective (w.i.app V.1) :=
  w.J.subschemeι_app_surjective V

lemma app_eq_zero_iff (V : X.affineOpens) (r : Γ(X, V.1)) :
    w.i.app V.1 r = 0 ↔ r ∈ w.J.ideal V := by
  rw [← w.J.ker_subschemeι_app V]
  rfl

lemma pre_le {A B : X.Opens} (h : A ≤ B) : w.i ⁻¹ᵁ A ≤ w.i ⁻¹ᵁ B := fun _ hx => h hx

/-- Multiplication of the section `s` by a function on the closed subscheme over an affine
open of `U`, computed through any lift of the function. -/
def mu (V : X.affineOpens) (hV : V.1 ≤ w.U.1) (a : Γ(w.Z, w.i ⁻¹ᵁ V.1)) : Γ(Q, V.1) :=
  (w.app_surjective V a).choose • Cech.res hV w.s

lemma mu_eq (V : X.affineOpens) (hV : V.1 ≤ w.U.1) (a : Γ(w.Z, w.i ⁻¹ᵁ V.1))
    (r : Γ(X, V.1)) (hr : w.i.app V.1 r = a) : w.mu V hV a = r • Cech.res hV w.s := by
  have h0 := (w.app_surjective V a).choose_spec
  have hmem : (w.app_surjective V a).choose - r ∈ w.J.ideal V := by
    rw [← w.app_eq_zero_iff, map_sub, h0, hr, sub_self]
  have := w.s_killed V hV _ hmem
  rw [sub_smul, sub_eq_zero] at this
  exact this

lemma mu_add (V : X.affineOpens) (hV : V.1 ≤ w.U.1) (a b : Γ(w.Z, w.i ⁻¹ᵁ V.1)) :
    w.mu V hV (a + b) = w.mu V hV a + w.mu V hV b := by
  obtain ⟨r, rfl⟩ := w.app_surjective V a
  obtain ⟨r', rfl⟩ := w.app_surjective V b
  rw [w.mu_eq V hV _ r rfl, w.mu_eq V hV _ r' rfl, w.mu_eq V hV _ (r + r') (map_add _ _ _),
    add_smul]

lemma mu_zero (V : X.affineOpens) (hV : V.1 ≤ w.U.1) : w.mu V hV 0 = 0 := by
  rw [w.mu_eq V hV 0 0 (map_zero _), zero_smul]

lemma mu_mul (V : X.affineOpens) (hV : V.1 ≤ w.U.1) (r : Γ(X, V.1))
    (a : Γ(w.Z, w.i ⁻¹ᵁ V.1)) : w.mu V hV (w.i.app V.1 r * a) = r • w.mu V hV a := by
  obtain ⟨r', rfl⟩ := w.app_surjective V a
  rw [w.mu_eq V hV _ r' rfl, w.mu_eq V hV _ (r * r') (map_mul _ _ _), mul_smul]

lemma mu_one (V : X.affineOpens) (hV : V.1 ≤ w.U.1) : w.mu V hV 1 = Cech.res hV w.s := by
  rw [w.mu_eq V hV 1 1 (map_one _), one_smul]

lemma mu_res (V V' : X.affineOpens) (hV : V.1 ≤ w.U.1) (h : V'.1 ≤ V.1)
    (a : Γ(w.Z, w.i ⁻¹ᵁ V.1)) :
    w.mu V' (h.trans hV) (rres (w.pre_le h) a) = Cech.res h (w.mu V hV a) := by
  obtain ⟨r, rfl⟩ := w.app_surjective V a
  rw [w.mu_eq V hV _ r rfl, w.mu_eq V' (h.trans hV) _ (rres h r) (app_rres w.i h r),
    res_smul, Cech.res_res]

end Witness

end IntegralIdealFiltration

end Langlands.AlgebraicGeometry.Modules
