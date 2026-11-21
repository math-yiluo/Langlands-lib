import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalCentralImage
import Langlands.Representation.Plancherel.FiniteSmoothCompactEvaluation
import Langlands.Representation.Whittaker.Algebraic

/-! # Finite projected Schwartz levels on a compact central quotient -/

noncomputable section

universe u

open MeasureTheory Topology
open Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz

section CompactQuotient

variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]

/-- An equivariant right-invariant function is determined by its values
on the finitely many left cosets in the compact quotient. -/
private theorem finiteDimensional_of_compact_quotient
    (A : Subgroup Γ) [A.Normal] [CompactSpace (Γ ⧸ A)] (χ : A →* ℂˣ)
    (H : OpenSubgroup Γ) (E : Submodule ℂ (Γ → ℂ))
    (hχ : ∀ (f : E) (a : A) x, f.val ((a : Γ) * x) = (χ a : ℂ) * f.val x)
    (hH : ∀ (f : E) x (h : H), f.val (x * (h : Γ)) = f.val x) :
    FiniteDimensional ℂ E := by
  classical
  let p := QuotientGroup.mk' A
  let L := H.toSubgroup.map p
  let C := (Γ ⧸ A) ⧸ L
  have hL : IsOpen (L : Set (Γ ⧸ A)) :=
    (QuotientGroup.isOpenMap_coe (N := A)) _ H.isOpen
  let : Finite C := Subgroup.quotient_finite_of_isOpen L hL
  let : Fintype C := Fintype.ofFinite C
  let r (q : C) : Γ := q.out.out
  let evaluation : E →ₗ[ℂ] (C → ℂ) :=
    { toFun := fun f q => f.val (r q)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  apply FiniteDimensional.of_injective evaluation
  intro f g hfg
  apply Subtype.ext
  funext x
  let q : C := QuotientGroup.mk (p x)
  have hr : p (r q) = q.out := Quotient.out_eq _
  have hq : (QuotientGroup.mk (p (r q)) : C) = QuotientGroup.mk (p x) :=
    (congrArg (fun y => (QuotientGroup.mk y : C)) hr).trans (Quotient.out_eq q)
  obtain ⟨h, hh, heq⟩ := Subgroup.mem_map.mp (QuotientGroup.eq.mp hq)
  have hxq : p x = p (r q * h) := by
    rw [map_mul, heq, mul_inv_cancel_left]
  let a : A := ⟨x * (r q * h)⁻¹,
    by simpa only [div_eq_mul_inv] using QuotientGroup.eq_iff_div_mem.mp hxq⟩
  have hx : (a : Γ) * (r q * h) = x := inv_mul_cancel_right _ _
  have hval (w : E) : w.val x = (χ a : ℂ) * w.val (r q) := by
    rw [← hx, hχ w a, hH w (r q) ⟨h, hh⟩]
  change f.val x = g.val x
  rw [hval f, hval g]
  exact congrArg ((χ a : ℂ) * ·) (congrFun hfg q)

end CompactQuotient

variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
  (A : Subgroup Γ) [MeasurableSpace A] (muA : Measure A)
  (χ : A →* ℂˣ) (H : OpenSubgroup Γ) {Ξ σ : Γ → ℝ}
  (E : Submodule ℂ (Space Ξ σ))

/-- The compact-quotient case of finite dimensionality of a projected
Schwartz level, stated for its actual central integral span. -/
def CompactQuotientCentralProjectionFiniteStatement : Prop :=
  ∀ [IsTopologicalGroup Γ] [A.Normal] [MeasurableMul A] [muA.IsMulRightInvariant],
    A ≤ Subgroup.center Γ →
    CompactSpace (Γ ⧸ A) →
    (∀ f : E, IsBiInvariant H.toSubgroup (f.val : Γ → ℂ)) →
    FiniteDimensional ℂ (schwartzCentralIntegralSpan E muA χ)

/-- Projected functions retain bi-invariance and acquire character covariance,
which allow finite evaluation of their whole span. -/
theorem compactQuotientCentralProjectionFinite :
    CompactQuotientCentralProjectionFiniteStatement A muA χ H E := by
  intro _ _ _ _ hA hcompact hbi
  let : CompactSpace (Γ ⧸ A) := hcompact
  let I := LinearMap.id (R := ℂ) (M := Γ → ℂ)
  have hle : schwartzCentralIntegralSpan E muA χ ≤
      (Whittaker.equivariantFunctions A χ).toSubmodule ⊓
      rightInvariantEvaluationSubmodule I H.toSubgroup := by
    apply Submodule.span_le.mpr
    rintro _ ⟨f, hf, rfl⟩
    refine ⟨fun a x => centralProjection_mul_left (f : Γ → ℂ) a x, ?_⟩
    intro x h
    simpa only [I, LinearMap.id_apply, one_mul] using
      ((hbi ⟨f, hf⟩).centralProjection (μA := muA) hA χ) 1 H.one_mem h h.property x
  exact finiteDimensional_of_compact_quotient A χ H (schwartzCentralIntegralSpan E muA χ)
    (fun f => (hle f.property).1) (fun f => (hle f.property).2)

end Langlands.HarishChandraSchwartz
