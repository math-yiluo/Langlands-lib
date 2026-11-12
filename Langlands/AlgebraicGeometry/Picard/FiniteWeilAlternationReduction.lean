import Langlands.AlgebraicGeometry.Picard.FiniteWeilAlternationStatement
import Langlands.AlgebraicGeometry.Picard.MumfordFiniteWeilAlternationProof
import Langlands.AlgebraicGeometry.Picard.PolarizationDiagonalMumfordProof
import Langlands.AbelianScheme.Tate.KernelTransitionEpimorphism

/-! # Relative finite Weil alternation from multiplication isogenies -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Langlands.GroupScheme.Tate

variable {S : Scheme.{u}} {G H : Grp (Over S)}
  [IsCommMonObj G.X] [IsCommMonObj H.X]

/-- Actual torsion maps commute with the divisibility transitions. -/
lemma kernelLevelMap_transition (f : G ⟶ H) {n m : ℕ} (h : n ∣ m) :
    kernelLevelMap f m ≫ kernelTransition H h =
      kernelTransition G h ≫ kernelLevelMap f n := by
  apply (cancel_mono (kernelι (multiplication H n)).hom.hom).mp
  calc
    _ = (kernelι (multiplication G m)).hom.hom ≫
        f.hom.hom ≫ (multiplication H (m / n : ℕ)).hom.hom := by
      rw [Category.assoc, kernelTransition_ι, ← Category.assoc, kernelLevelMap_ι,
        Category.assoc]
    _ = (kernelι (multiplication G m)).hom.hom ≫
        (multiplication G (m / n : ℕ)).hom.hom ≫ f.hom.hom :=
      congrArg ((kernelι (multiplication G m)).hom.hom ≫ ·)
        (congrArg (fun g ↦ g.hom.hom) (multiplication_naturality f (m / n : ℕ))).symm
    _ = _ := by
      symm
      rw [Category.assoc, kernelLevelMap_ι, ← Category.assoc, kernelTransition_ι,
        Category.assoc]

end Langlands.GroupScheme.Tate

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.GroupScheme

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (composition : PullbackTensorCompositionStatement.{u})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
  (symmetry : PullbackTensorSymmetryStatement.{u})
  (stability : PicardZeroPullbackStatement.{u})
  {S : Scheme.{u}} [QuasiSeparatedSpace S] {A : AbelianScheme S}
  (hA : HasDualScheme A) (geometryA : DualSchemeGeometry A hA)
  (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
    structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))

local notation "DA" => dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
  evaluationA stability composition unitCoherence associativity comparison symmetry
local notation "primal" n:arg => kernelCommGroupScheme (multiplication A (n : ℤ))
local notation "value" => finiteWeilAlongHomValue preservation composition unitCoherence
  associativity comparison symmetry stability hA geometryA MA evaluationA
local notation "torsionMap" => finiteWeilAlongHomTorsionMap preservation composition
  unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA

omit [QuasiSeparatedSpace S] in
/-- The actual torsion map is additive in its homomorphism argument. -/
lemma finiteWeilAlongHomTorsionMap_add (lam lam' : A ⟶ DA) (n : ℕ) :
    torsionMap (lam + lam') n = torsionMap lam n * torsionMap lam' n := by
  apply (cancel_mono (torsionι (DA).toGrp (n : ℤ)).hom.hom).mp
  rw [finiteWeilAlongHom_torsion_inclusion, MonObj.mul_comp,
    finiteWeilAlongHom_torsion_inclusion, finiteWeilAlongHom_torsion_inclusion]
  change _ ≫ ((groupHom lam).hom.hom * (groupHom lam').hom.hom) = _
  exact MonObj.comp_mul _ _ _

/-- The finite pairing is additive in the actual dual-valued homomorphism. -/
lemma finiteWeilAlongHomValue_add_hom (lam lam' : A ⟶ DA) (n : ℕ) {T : Over S}
    (x y : T ⟶ (primal n).X) :
    value (lam + lam') n x y = value lam n x y * value lam' n x y := by
  unfold finiteWeilAlongHomValue
  rw [finiteWeilAlongHomTorsionMap_add, MonObj.comp_mul, finiteWeilValue_mul_right]

/-- Evaluation at two actual torsion points is additive in the dual-valued homomorphism. -/
def finiteWeilAlongHomEvaluationAddHom (n : ℕ) {T : Over S}
    (x y : T ⟶ (primal n).X) :
    (A ⟶ DA) →+ Additive (T ⟶ (mu S n).X) where
  toFun lam := Additive.ofMul (value lam n x y)
  map_zero' := by
    have h := finiteWeilAlongHomValue_add_hom preservation composition unitCoherence
      associativity comparison symmetry stability hA geometryA MA evaluationA 0 0 n x y
    rw [zero_add] at h
    exact congrArg Additive.ofMul (mul_eq_left.mp h.symm)
  map_add' lam lam' := congrArg Additive.ofMul
    (finiteWeilAlongHomValue_add_hom preservation composition unitCoherence associativity
      comparison symmetry stability hA geometryA MA evaluationA lam lam' n x y)

/-- Doubling the actual homomorphism squares its finite pairing value. -/
lemma finiteWeilAlongHomValue_two_nsmul (lam : A ⟶ DA) (n : ℕ) {T : Over S}
    (x y : T ⟶ (primal n).X) :
    value (2 • lam) n x y = value lam n x y ^ 2 := by
  exact congrArg Additive.toMul
    (map_nsmul (finiteWeilAlongHomEvaluationAddHom preservation composition unitCoherence
      associativity comparison symmetry stability hA geometryA MA evaluationA n x y) 2 lam)

/-- After root inclusion, divisibility transition raises the along-hom pairing value
to the quotient power, on every test scheme. -/
lemma finiteWeilAlongHomValue_transition_incl (lam : A ⟶ DA)
    {n m : ℕ} (h : n ∣ m) {T : Over S} (x y : T ⟶ (primal m).X) :
    value lam n (x ≫ Tate.kernelTransition A.toGrp h)
        (y ≫ Tate.kernelTransition A.toGrp h) ≫ (mu.incl S n).toMul.hom.hom =
      (value lam m x y ≫ (mu.incl S m).toMul.hom.hom) ^ (m / n) := by
  unfold finiteWeilAlongHomValue finiteWeilAlongHomTorsionMap
  rw [Category.assoc, ← Tate.kernelLevelMap_transition, ← Category.assoc,
    finiteWeilValue_incl, finiteWeilValue_incl]
  exact dualTorsionCharacter_transition preservation composition unitCoherence associativity
    comparison symmetry stability hA MA evaluationA h x (y ≫ Tate.kernelLevelMap (groupHom lam) m)

/-- The published diagonal Mumford theorem and Mumford alternation prove that the diagonal
value of a relative polarization has square one, as a morphism on the actual kernel. -/
lemma finiteWeilAlongHomValue_self_sq
    (square : MumfordBundlePicardZeroStatement.{u})
    (universality : PicardZeroUniversalBaseChangeStatement.{u})
    (lam : A ⟶ DA)
    (hlam : IsPolarization preservation square universality A hA geometryA MA evaluationA
      stability composition unitCoherence associativity comparison symmetry lam)
    (n : ℕ) (hn : 0 < n) :
    value lam n (𝟙 (primal n).X) (𝟙 (primal n).X) ^ 2 = 1 := by
  obtain ⟨B, evaluationB, M, evaluation, hM⟩ :=
    polarizationDiagonalMumford preservation square universality composition unitCoherence
      associativity comparison symmetry stability S A hA geometryA MA evaluationA lam hlam
  have hd := mumfordFiniteWeilAlternation preservation square composition unitCoherence
    associativity comparison symmetry stability S A hA geometryA MA evaluationA
    (poincareDiagonalBundle A hA (groupHom lam).hom.hom) B evaluationB M evaluation
    (2 • lam) hM.symm n hn
  rw [finiteWeilAlongHomPairing_points, finiteWeilAlongHomValue_two_nsmul] at hd
  exact hd

/-- A relative polarization is alternating at level `n` whenever its actual doubling
transition is an epimorphism in the slice category. -/
lemma finiteWeilAlongHom_diagonal_of_doubling_epi
    (square : MumfordBundlePicardZeroStatement.{u})
    (universality : PicardZeroUniversalBaseChangeStatement.{u})
    (lam : A ⟶ DA)
    (hlam : IsPolarization preservation square universality A hA geometryA MA evaluationA
      stability composition unitCoherence associativity comparison symmetry lam)
    (n : ℕ) (hn : 0 < n)
    [Epi (Tate.kernelTransition A.toGrp (dvd_mul_left n 2))] :
    prod.lift (𝟙 _) (𝟙 _) ≫
        finiteWeilAlongHomPairing preservation composition unitCoherence associativity
          comparison symmetry stability hA geometryA MA evaluationA lam n =
      (1 : (primal n).X ⟶ (mu S n).X) := by
  let κ : (primal (2 * n)).X ⟶ (primal n).X :=
    Tate.kernelTransition A.toGrp (dvd_mul_left n 2)
  have : Epi κ := inferInstanceAs
    (Epi (Tate.kernelTransition A.toGrp (dvd_mul_left n 2)))
  apply (cancel_epi κ).mp
  rw [← Category.assoc, prod.comp_lift, Category.comp_id,
    finiteWeilAlongHomPairing_points, MonObj.comp_one]
  apply (cancel_mono (torsionι (Gm S).toGrp (n : ℤ)).hom.hom).mp
  have ht := finiteWeilAlongHomValue_transition_incl preservation composition unitCoherence
    associativity comparison symmetry stability hA geometryA MA evaluationA lam
    (dvd_mul_left n 2) (𝟙 (primal (2 * n)).X) (𝟙 (primal (2 * n)).X)
  have hratio : 2 * n / n = 2 := by
    simpa only [Nat.mul_comm] using Nat.mul_div_cancel_left 2 hn
  have hs := finiteWeilAlongHomValue_self_sq preservation composition unitCoherence
    associativity comparison symmetry stability hA geometryA MA evaluationA square universality
    lam hlam (2 * n) (by omega)
  change value lam n κ κ ≫ (mu.incl S n).toMul.hom.hom =
    1 ≫ (mu.incl S n).toMul.hom.hom
  rw [MonObj.one_comp]
  calc
    _ = (value lam (2 * n) (𝟙 _) (𝟙 _) ≫
        (mu.incl S (2 * n)).toMul.hom.hom) ^ 2 := by
      rw [Category.id_comp, hratio] at ht
      exact ht
    _ = (value lam (2 * n) (𝟙 _) (𝟙 _) ^ 2) ≫
        (mu.incl S (2 * n)).toMul.hom.hom :=
      (MonObj.pow_comp _ _ _).symm
    _ = (1 : (primal (2 * n)).X ⟶ (mu S (2 * n)).X) ≫
        (mu.incl S (2 * n)).toMul.hom.hom :=
      congrArg (· ≫ (mu.incl S (2 * n)).toMul.hom.hom) hs
    _ = 1 := MonObj.one_comp _

/-- Conditional assembly of the unchanged relative alternation target: the only remaining
external premise is the published general multiplication-isogeny statement. -/
theorem relativeFiniteWeilAlternation_of_multiplicationIsogeny
    (hIsogeny : MultiplicationIsogenyStatement.{u}) :
    RelativeFiniteWeilAlternationStatement.{u} := by
  intro preservation square universality composition unitCoherence associativity comparison
    symmetry stability S _ A hA geometryA MA evaluationA lam hlam n hn
  have := kernelDoubling_epi_of_multiplicationIsogeny hIsogeny S A n hn
  exact finiteWeilAlongHom_diagonal_of_doubling_epi preservation composition unitCoherence
    associativity comparison symmetry stability hA geometryA MA evaluationA square universality
    lam hlam n hn

end Langlands.AbelianScheme
