import Langlands.Global.RankinSelberg.ComplexCompactProbeBounds

/-! # Iterated differences on the compact picture of a complex standard module -/

noncomputable section

open scoped Classical Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexCompactDifferences

open Langlands.Archimedean (complexPositionCharacter complexStandardRep exists_sum_of_separating
  isComplexGKModule_complexStandardModule principalSeriesRep_apply_coe)
open Langlands.Archimedean.ComplexPrincipalSeriesExtension (eq_of_eqOn_unitary)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open ComplexCompactProbeBounds (CompactBound CompactRightDifferenceBound)

local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "K" => fun n => Matrix.unitaryGroup (Fin n) ℂ
local notation "Std" => Automorphic.complexStandardKFinite

variable {n : ℕ} {ds : List ComplexCharacterData}

/-- The difference between right compact translation and the identity. -/
def rightDifference (k : K n) : Module.End ℂ (Std n ds) :=
  complexStandardRep n ds k - 1

/-- The product of right differences in the order of a list of compact moves. -/
def iteratedDifference (ks : List (K n)) : Module.End ℂ (Std n ds) :=
  (ks.map rightDifference).prod

/-- The product of the operator-norm displacements of the compact moves. -/
def displacementProduct (ks : List (K n)) : ℝ :=
  (ks.map fun k => ‖k.val - 1‖).prod

theorem displacementProduct_nonneg (ks : List (K n)) : 0 ≤ displacementProduct ks := by
  induction ks with
  | nil => exact zero_le_one
  | cons k ks ih => exact mul_nonneg (norm_nonneg _) ih

/-- Bounds all iterated differences of length at most `J` by the product of the
compact displacements times `R`. The empty list tests the value of `f` itself. -/
def CompactDifferenceBound (J : ℕ) (f : Std n ds) (R : ℝ) : Prop :=
  ∀ ks : List (K n), ks.length ≤ J →
    CompactBound (iteratedDifference ks f) (R * displacementProduct ks)

theorem CompactDifferenceBound.value {J : ℕ} {f : Std n ds} {R : ℝ}
    (h : CompactDifferenceBound J f R) : CompactBound f R := by
  simpa [iteratedDifference, displacementProduct] using h [] (Nat.zero_le J)

theorem CompactDifferenceBound.constant_nonneg {J : ℕ} {f : Std n ds} {R : ℝ}
    (h : CompactDifferenceBound J f R) : 0 ≤ R :=
  (norm_nonneg _).trans (h.value 1)

theorem CompactDifferenceBound.mono {J : ℕ} {f : Std n ds} {R S : ℝ}
    (h : CompactDifferenceBound J f R) (hRS : R ≤ S) : CompactDifferenceBound J f S :=
  fun ks hks x => (h ks hks x).trans (mul_le_mul_of_nonneg_right hRS (displacementProduct_nonneg ks))

private theorem compactRep_apply (k : K n) (f : Std n ds) (g : G n) :
    (complexStandardRep n ds k f).val g = f.val (g * Unitary.toUnits k) :=
  congrFun (principalSeriesRep_apply_coe ℂ n (complexPositionCharacter ds) k f) g

theorem CompactDifferenceBound.rightDifference {J : ℕ} {f : Std n ds} {R : ℝ}
    (h : CompactDifferenceBound (J + 1) f R) (ks : List (K n)) (hks : ks.length ≤ J) :
    CompactRightDifferenceBound (iteratedDifference ks f) (R * displacementProduct ks) := by
  intro x k
  have hk := h (k :: ks) (Nat.succ_le_succ hks) x
  change ‖(complexStandardRep n ds k (iteratedDifference ks f)).val (Unitary.toUnits x) -
    (iteratedDifference ks f).val (Unitary.toUnits x)‖ ≤ R * (‖k.val - 1‖ * displacementProduct ks) at hk
  rw [compactRep_apply, ← map_mul] at hk
  convert hk using 1
  ring

theorem iteratedDifference_commutes (A : Module.End ℂ (Std n ds))
    (hA : ∀ k : K n, ∀ f : Std n ds, A (complexStandardRep n ds k f) = complexStandardRep n ds k (A f))
    (ks : List (K n)) (f : Std n ds) :
    A (iteratedDifference ks f) = iteratedDifference ks (A f) := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    change A (complexStandardRep n ds k (iteratedDifference ks f) - iteratedDifference ks f) =
      complexStandardRep n ds k (iteratedDifference ks (A f)) - iteratedDifference ks (A f)
    rw [map_sub, hA, ih]

theorem CompactDifferenceBound.residual {f : Std n ds} {C R : ℝ} {J : ℕ}
    (h : CompactDifferenceBound J f R) (A : Module.End ℂ (Std n ds))
    (hA : ∀ k : K n, ∀ v : Std n ds, A (complexStandardRep n ds k v) = complexStandardRep n ds k (A v))
    (hValue : ∀ v M, CompactBound v M → CompactBound (A v) (C * M)) :
    CompactDifferenceBound J (f - A f) ((1 + C) * R) := by
  intro ks hks x
  rw [map_sub, ← iteratedDifference_commutes A hA]
  calc
    _ ≤ ‖(iteratedDifference ks f).val (Unitary.toUnits x)‖ +
        ‖(A (iteratedDifference ks f)).val (Unitary.toUnits x)‖ := norm_sub_le _ _
    _ ≤ R * displacementProduct ks + C * (R * displacementProduct ks) :=
      add_le_add (h ks hks x) (hValue _ _ (h ks hks) x)
    _ = _ := by ring

theorem CompactDifferenceBound.residual_succ {f : Std n ds} {C ε R : ℝ} {J : ℕ}
    (h : CompactDifferenceBound (J + 1) f R) (A : Module.End ℂ (Std n ds))
    (hA : ∀ k : K n, ∀ v : Std n ds, A (complexStandardRep n ds k v) = complexStandardRep n ds k (A v))
    (hError : ∀ v R D, 0 ≤ D → CompactBound v R → CompactRightDifferenceBound v D →
      CompactBound (v - A v) (C * ε * (R + D))) :
    CompactDifferenceBound J (f - A f) (2 * C * ε * R) := by
  intro ks hks
  rw [map_sub, ← iteratedDifference_commutes A hA]
  have hp := mul_nonneg h.constant_nonneg (displacementProduct_nonneg ks)
  have hb := hError _ _ _ hp (h ks (hks.trans (Nat.le_succ J))) (h.rightDifference ks hks)
  convert hb using 1
  ring

private def compactEval (k : K n) : Std n ds →ₗ[ℂ] ℂ :=
  (LinearMap.proj (Unitary.toUnits k)).comp (Automorphic.complexStandardKFinite n ds).subtype

private theorem compactEval_separates {v w : Std n ds} (h : ∀ k : K n, compactEval k v = compactEval k w) :
    v = w := by
  apply Subtype.ext
  apply eq_of_eqOn_unitary v.2.1 w.2.1
  intro g hg
  let k : K n := ⟨g.val, hg⟩
  have hk : Unitary.toUnits k = g := Units.ext rfl
  simpa only [compactEval, LinearMap.comp_apply, LinearMap.proj_apply, Submodule.subtype_apply, hk] using h k

/-- On the orbit of a fixed compact-finite vector under endomorphisms commuting with
compact right translation, every linear functional is bounded by the compact norm. -/
def CompactEquivariantOrbitBoundStatement : Prop :=
  ∀ (n : ℕ) (ds : List ComplexCharacterData) (f : Std n ds) (ℓ : Std n ds →ₗ[ℂ] ℂ),
  ∃ S : ℝ, 0 ≤ S ∧ ∀ (T : Module.End ℂ (Std n ds)),
    (∀ (k : K n) (v : Std n ds), T (complexStandardRep n ds k v) = complexStandardRep n ds k (T v)) →
    ∀ R : ℝ, CompactBound (T f) R → ‖ℓ (T f)‖ ≤ S * R

theorem compactEquivariantOrbitBound : CompactEquivariantOrbitBoundStatement := by
  intro n ds f ℓ
  let ρ := complexStandardRep n ds
  let V := FiniteVectors.orbitSpan ρ f
  have : FiniteDimensional ℂ V := (isComplexGKModule_complexStandardModule n ds).1 f
  have : Module.Free ℂ V := Module.Free.of_divisionRing ℂ V
  have : Module.Projective ℂ V := Module.Projective.of_free
  have : FiniteDimensional ℂ (Module.Dual ℂ V) := Module.dual_finite
  let e : Std n ds →ₗ[ℂ] (K n → ℂ) := LinearMap.pi compactEval
  let F : Module.Dual ℂ V →ₗ[ℂ] (K n → ℂ) :=
    LinearMap.pi fun k => Module.Dual.eval ℂ V ⟨ρ k f, FiniteVectors.action_mem_orbitSpan ρ k f⟩
  have : FiniteDimensional ℂ F.range := LinearMap.finiteDimensional_range F
  let W := F.range.comap e
  let i : W →ₗ[ℂ] F.range := (e.comp W.subtype).codRestrict F.range fun v => v.2
  have : FiniteDimensional ℂ W := FiniteDimensional.of_injective i (fun v w h => by
    apply Subtype.ext
    exact compactEval_separates (fun k => congrFun (congrArg Subtype.val h) k))
  obtain ⟨m, p, c, hc⟩ := exists_sum_of_separating compactEval W (fun v _ hv =>
    compactEval_separates (fun k => (hv k).trans (map_zero (compactEval k)).symm)) ℓ
  refine ⟨∑ j, ‖c j‖, Finset.sum_nonneg (fun _ _ => norm_nonneg _), fun T hT R hR => ?_⟩
  have hW : T f ∈ W := by
    refine ⟨(compactEval 1).comp (T.comp V.subtype), ?_⟩
    funext k
    change (T (ρ k f)).val (Unitary.toUnits (1 : K n)) = (T f).val (Unitary.toUnits k)
    rw [hT, compactRep_apply, map_one, one_mul]
  rw [hc _ hW, Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  exact (norm_mul _ _).le.trans (mul_le_mul_of_nonneg_left (hR (p j)) (norm_nonneg _))

end Langlands.Global.RankinSelbergGlobal.ComplexCompactDifferences
