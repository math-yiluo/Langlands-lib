import Langlands.Representation.Archimedean.SmoothDerivativeTopology
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.HahnBanach

/-! # Finite derivative coordinates of a smooth Hilbert functional -/

noncomputable section
set_option autoImplicit false

open scoped Manifold ContDiff

namespace Langlands.Archimedean

universe u𝔤 uH uG uE

variable {𝔤 : Type u𝔤} [NormedAddCommGroup 𝔤] [NormedSpace ℝ 𝔤]
  {H : Type uH} [TopologicalSpace H] (I : ModelWithCorners ℝ 𝔤 H)
  {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace H G] [LieGroup I ∞ G]
  {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (π : G →* (E →L[ℂ] E))

/-- A derivative-continuous scalar functional on genuine Hilbert smooth vectors
is a finite sum of pairings against actual word derivatives. -/
theorem exists_eq_sum_inner_iteratedLieDerivative
    (L : smoothVectors I π →ₗ[ℂ] ℂ) (hL : IsContinuousOnSmoothVectors I π L) :
    ∃ (S : Finset (List 𝔤)) (a : S → E), ∀ v : smoothVectors I π,
      L v = ∑ i : S, Inner.inner ℂ (a i) (iteratedLieDerivative I π i.val v) := by
  classical
  obtain ⟨S, C, hbound⟩ := hL
  let J : Finset (List 𝔤) := insert [] S
  let j : smoothVectors I π →ₗ[ℂ] (J → E) :=
    LinearMap.pi fun i : J => (smoothVectors I π).subtype.comp
      (smoothIteratedLieDerivative I π i.val)
  have hj (v : smoothVectors I π) (i : J) :
      j v i = iteratedLieDerivative I π i.val v :=
    smoothIteratedLieDerivative_apply I π i.val v
  have hjInj : Function.Injective j := by
    intro v w h
    let i : J := ⟨[], Finset.mem_insert_self _ _⟩
    exact Subtype.ext (congrFun h i)
  let e := LinearEquiv.ofInjective j hjInj
  have hjBound (v : smoothVectors I π) : ‖L v‖ ≤ (max C 0 * S.card) * ‖j v‖ := by
    calc
      ‖L v‖ ≤ C * ∑ Xs ∈ S, ‖iteratedLieDerivative I π Xs v‖ := hbound v
      _ ≤ max C 0 * ∑ Xs ∈ S, ‖iteratedLieDerivative I π Xs v‖ :=
        mul_le_mul_of_nonneg_right (le_max_left C 0) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
      _ ≤ max C 0 * ∑ _Xs ∈ S, ‖j v‖ := by
        apply mul_le_mul_of_nonneg_left _ (le_max_right C 0)
        apply Finset.sum_le_sum
        intro Xs hXs
        let i : J := ⟨Xs, Finset.mem_insert_of_mem hXs⟩
        exact (congrArg norm (hj v i)).symm.le.trans (norm_le_pi_norm (j v) i)
      _ = (max C 0 * S.card) * ‖j v‖ := by simp [mul_assoc]
  let f : LinearMap.range j →L[ℂ] ℂ :=
    (L.comp e.symm.toLinearMap).mkContinuous (max C 0 * S.card) fun x => by
      obtain ⟨v, rfl⟩ := e.surjective x
      change ‖L (e.symm (e v))‖ ≤ (max C 0 * S.card) * ‖j v‖
      rw [e.symm_apply_apply]
      exact hjBound v
  obtain ⟨g, hg⟩ := StrongDual.exists_extension (LinearMap.range j) f
  let coordinate (i : J) : E →L[ℂ] ℂ :=
    g.comp (ContinuousLinearMap.single ℂ (fun _ : J => E) i)
  let a (i : J) : E := (InnerProductSpace.toDual ℂ E).symm (coordinate i)
  have ha (i : J) (x : E) : Inner.inner ℂ (a i) x = coordinate i x :=
    congrArg (fun b : StrongDual ℂ E => b x)
      ((InnerProductSpace.toDual ℂ E).apply_symm_apply (coordinate i))
  refine ⟨J, a, fun v => ?_⟩
  calc
    L v = g (j v) := by
      have he := (hg (e v)).symm
      change L (e.symm (e v)) = g (j v) at he
      simpa only [LinearEquiv.symm_apply_apply] using he
    _ = ∑ i : J, coordinate i (j v i) :=
      (ContinuousLinearMap.sum_comp_single ℂ (fun _ : J => E) g (j v)).symm
    _ = ∑ i : J, Inner.inner ℂ (a i) (iteratedLieDerivative I π i.val v) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hj, ha]

/-- Every scalar functional with a finite genuine derivative bound has a
finite Hilbert pairing formula on the same smooth vectors. -/
def SmoothFunctionalCoordinatesStatement : Prop :=
  ∀ (𝔤 : Type u𝔤) [NormedAddCommGroup 𝔤] [NormedSpace ℝ 𝔤]
    (H : Type uH) [TopologicalSpace H] (I : ModelWithCorners ℝ 𝔤 H)
    (G : Type uG) [Group G] [TopologicalSpace G] [ChartedSpace H G] [LieGroup I ∞ G]
    (E : Type uE) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (π : G →* (E →L[ℂ] E)) (L : smoothVectors I π →ₗ[ℂ] ℂ),
    IsContinuousOnSmoothVectors I π L →
      ∃ (S : Finset (List 𝔤)) (a : S → E), ∀ v : smoothVectors I π,
        L v = ∑ i : S, Inner.inner ℂ (a i) (iteratedLieDerivative I π i.val v)

theorem smoothFunctionalCoordinates : SmoothFunctionalCoordinatesStatement.{u𝔤,uH,uG,uE} := by
  intro 𝔤 _ _ H _ I G _ _ _ _ E _ _ _ π L hL
  exact exists_eq_sum_inner_iteratedLieDerivative I π L hL

end Langlands.Archimedean
