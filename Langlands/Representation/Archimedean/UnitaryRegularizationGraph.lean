import Langlands.Representation.Archimedean.UnitaryCommutant
import Mathlib.Analysis.InnerProductSpace.ProdL2

noncomputable section

open Set
open scoped InnerProductSpace

namespace Langlands.Archimedean

variable {G X Y V : Type*} [Group G]
  [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
  [AddCommGroup V] [Module ℂ V]

private theorem action_inv_apply {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (ρ : G →* (H →L[ℂ] H)) (g : G) (x : H) : ρ g (ρ g⁻¹ x) = x := by
  change (ρ g * ρ g⁻¹) x = x
  rw [← map_mul, mul_inv_cancel, map_one]
  rfl

/-- A pairing identity gives a bounded comparison of two regularizations with a
common domain. The graph of their values is invariant for the product action.
The pairing identity makes the first projection of its closure injective. -/
theorem exists_unitaryIntertwiner_of_regularization_pairing
    (ρ : G →* (X →L[ℂ] X)) (σ : G →* (Y →L[ℂ] Y))
    (hρ : ∀ g x x', inner ℂ (ρ g x) (ρ g x') = inner ℂ x x')
    (hσ : ∀ g y y', inner ℂ (σ g y) (σ g y') = inner ℂ y y')
    (hirr : IsTopologicallyIrreducible ρ) (A : V →ₗ[ℂ] X) (B : V →ₗ[ℂ] Y)
    (hA : A ≠ 0)
    (hstable : ∀ g v, ∃ w, A w = ρ g (A v) ∧ B w = σ g (B v))
    {ι : Type*} (xTest : ι → X) (yTest : ι → Y) (hdense : DenseRange yTest)
    (hpair : ∀ v i, inner ℂ (B v) (yTest i) = inner ℂ (A v) (xTest i)) :
    ∃ T : X →L[ℂ] Y, (∀ v, T (A v) = B v) ∧ (∀ g x, T (ρ g x) = σ g (T x)) := by
  let P := WithLp 2 (X × Y)
  let fst : P →L[ℂ] X := WithLp.fstL 2 ℂ X Y
  let snd : P →L[ℂ] Y := WithLp.sndL 2 ℂ X Y
  let pair : V →ₗ[ℂ] P := (WithLp.linearEquiv 2 ℂ (X × Y)).symm.toLinearMap.comp (A.prod B)
  let W := (LinearMap.range pair).topologicalClosure
  have hclosed : IsClosed (W : Set P) := Submodule.isClosed_topologicalClosure _
  have : CompleteSpace W := hclosed.isComplete.completeSpace_coe
  have hmem (v : V) : pair v ∈ W :=
    Submodule.le_topologicalClosure _ (LinearMap.mem_range_self pair v)
  let p := fst.comp W.subtypeL
  let q := snd.comp W.subtypeL
  have hpInj : Function.Injective p := by
    apply (LinearMap.ker_eq_bot (f := p.toLinearMap)).mp
    rw [LinearMap.ker_eq_bot']
    intro z hz
    have htest (i : ι) : inner ℂ (q z) (yTest i) = 0 := by
      have hclosedPair : IsClosed {w : P |
          inner ℂ (snd w) (yTest i) = inner ℂ (fst w) (xTest i)} :=
        isClosed_eq (snd.continuous.inner continuous_const) (fst.continuous.inner continuous_const)
      have hrange : (LinearMap.range pair : Set P) ⊆ {w : P |
          inner ℂ (snd w) (yTest i) = inner ℂ (fst w) (xTest i)} := by
        rintro _ ⟨v, rfl⟩
        exact hpair v i
      have hi : (z : P) ∈ {w : P |
          inner ℂ (snd w) (yTest i) = inner ℂ (fst w) (xTest i)} :=
        closure_minimal hrange hclosedPair z.2
      change inner ℂ (q z) (yTest i) = inner ℂ (p z) (xTest i) at hi
      change p z = 0 at hz
      simpa [hz] using hi
    have hq : q z = 0 := by
      apply ext_inner_right ℂ
      intro y
      have hc : IsClosed {y : Y | inner ℂ (q z) y = 0} :=
        isClosed_eq (continuous_const.inner continuous_id) continuous_const
      have hy := closure_minimal (Set.range_subset_iff.mpr htest) hc (hdense y)
      simpa using hy
    apply Subtype.ext
    apply (WithLp.equiv 2 (X × Y)).injective
    exact Prod.ext hz hq
  have hp : p ≠ 0 := by
    intro he
    apply hA
    refine LinearMap.ext fun v => ?_
    exact congrArg (fun T : W →L[ℂ] X => T (⟨pair v, hmem v⟩ : W)) he
  let diag (g : G) : P →L[ℂ] P :=
    (WithLp.prodContinuousLinearEquiv 2 ℂ X Y).symm.toContinuousLinearMap.comp
      (((ρ g).comp fst).prod ((σ g).comp snd))
  have hdiag (g : G) : MapsTo (diag g) (W : Set P) W := by
    apply MapsTo.closure _ (diag g).continuous
    intro z hz
    obtain ⟨v, rfl⟩ := hz
    obtain ⟨w, hw₁, hw₂⟩ := hstable g v
    refine ⟨w, ?_⟩
    apply (WithLp.equiv 2 (X × Y)).injective
    exact Prod.ext hw₁ hw₂
  let act (g : G) (z : W) : W := ⟨diag g z, hdiag g z.2⟩
  have hpAct (g : G) (z : W) : p (act g z) = ρ g (p z) := rfl
  have hqAct (g : G) (z : W) : q (act g z) = σ g (q z) := rfl
  have hinv (g : G) (z : W) : act g (act g⁻¹ z) = z := by
    apply Subtype.ext
    apply (WithLp.equiv 2 (X × Y)).injective
    exact Prod.ext (action_inv_apply ρ g _) (action_inv_apply σ g _)
  have hinner (g : G) (z w : W) :
      inner ℂ (act g z) (act g w) = inner ℂ z w := by
    change inner ℂ (ρ g (p z)) (ρ g (p w)) + inner ℂ (σ g (q z)) (σ g (q w)) =
      inner ℂ (p z) (p w) + inner ℂ (q z) (q w)
    rw [hρ, hσ]
  have hAdj (g : G) (x : X) : p.adjoint (ρ g x) = act g (p.adjoint x) := by
    apply ext_inner_right ℂ
    intro z
    calc
      inner ℂ (p.adjoint (ρ g x)) z = inner ℂ x (p (act g⁻¹ z)) := by
        rw [ContinuousLinearMap.adjoint_inner_left, hpAct]
        simpa only [action_inv_apply] using hρ g x (ρ g⁻¹ (p z))
      _ = inner ℂ (act g (p.adjoint x)) z := by
        rw [← ContinuousLinearMap.adjoint_inner_left, ← hinner g, hinv]
  have hcomm (g : G) : Commute (p.comp p.adjoint) (ρ g) := by
    apply ContinuousLinearMap.ext
    intro x
    change p (p.adjoint (ρ g x)) = ρ g (p (p.adjoint x))
    rw [hAdj, hpAct]
  obtain ⟨c, hc⟩ := exists_eq_scalar_of_unitary_commute ρ hρ hirr _ hcomm
  have hc0 : c ≠ 0 := by
    intro hz
    rw [hz, zero_smul] at hc
    have he : p.adjoint.adjoint.comp p.adjoint = 0 := by simpa using hc
    have hpstar := ContinuousLinearMap.adjoint_comp_self_eq_zero_iff.mp he
    apply hp
    apply ContinuousLinearMap.ext
    intro z
    apply ext_inner_left ℂ
    intro x
    change inner ℂ x (p z) = inner ℂ x (0 : X)
    rw [← ContinuousLinearMap.adjoint_inner_left p z x, hpstar]
    simp
  have hpp (x : X) : p (p.adjoint x) = c • x :=
    congrArg (fun T : X →L[ℂ] X => T x) hc
  let r := c⁻¹ • p.adjoint
  have hpr (x : X) : p (r x) = x := by
    change p (c⁻¹ • p.adjoint x) = x
    rw [map_smul, hpp, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have hrp (z : W) : r (p z) = z := hpInj (hpr (p z))
  refine ⟨q.comp r, fun v => ?_, fun g x => ?_⟩
  · change q (r (p ⟨pair v, hmem v⟩)) = q ⟨pair v, hmem v⟩
    rw [hrp]
  · change q (c⁻¹ • p.adjoint (ρ g x)) = σ g (q (c⁻¹ • p.adjoint x))
    rw [hAdj, map_smul, map_smul, map_smul, hqAct]

end Langlands.Archimedean
