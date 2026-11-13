import Langlands.Shimura.PEL.PolarizedWeilIsogenyModel
import Langlands.AbelianScheme.Tate.IntegralReflectionAlgebra

/-! # Polarization preservation on an exact integral power model -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.PolarizedWeilLevel

open Langlands.AbelianScheme Langlands.AbelianScheme.PolarizedFiniteLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

variable (P : Prerequisites.{u})
  {S : Scheme.{u}} {R : Type v} [Ring R] [Algebra ℚ R] [StarRing R]

local notation "PObj" => PolarizedAction P.preservation P.composition P.unitCoherence
  P.associativity P.comparison P.symmetry P.stability P.square P.universality S R

variable (additivity : PairAdditivity P.preservation P.composition P.unitCoherence
  P.associativity P.comparison P.symmetry P.stability P.square P.universality
  (S := S) (D := R))

local notation "Mult" => Multiple P.preservation P.composition P.unitCoherence
  P.associativity P.comparison P.symmetry P.stability P.square P.universality additivity

/-- Actual powers of an equivariant self-isogeny retain the corresponding
power of its rational polarization multiplier. -/
theorem multiple_pow (X : PObj) (q : ℚˣ) (e : Aut X.actionObj)
    (he : Mult X X q e) (k : ℕ) : Mult X X (q ^ k) (e ^ k) := by
  induction k with
  | zero =>
    have h1 : (1 : Aut X.actionObj) = Iso.refl _ := rfl
    simpa only [pow_zero, h1] using multiple_refl P.preservation P.composition
      P.unitCoherence P.associativity P.comparison P.symmetry P.stability
      P.square P.universality additivity X
  | succ k ih =>
    simp only [pow_succ, Aut.Aut_mul_def]
    simpa only [mul_comm q] using multiple_trans P.preservation P.composition
      P.unitCoherence P.associativity P.comparison P.symmetry P.stability
      P.square P.universality additivity he ih

variable [QuasiSeparatedSpace S]
  (hu : ∀ k : GroupScheme.Tate.Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
  (X : PolarizedAction P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability P.square P.universality S R)
  (B : AbelianScheme S)
  (r : Rationalization.of B ≅ Rationalization.of X.actionObj.abelianScheme)
  (W : DualWitness B)
  {K : Type u} [Field K] [CharZero K] (p : S ⟶ Spec (.of K))

local notation "Y" => PolarizedAction.isogenyModel
  (R := R) (P := P) (X := X) (B := B) (e := r) (W := W) (p := p)
local notation "pullB" => integralDualPullbackHom P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability
  W.hasDual W.hasDual W.geometry W.geometry W.inverseBundle W.evaluation
  W.inverseBundle W.evaluation

/-- If a power has trivial multiplier and its exact conjugate is an integral
automorphism, that automorphism preserves the actual model polarization. -/
def IntegralPolarizedPowerModelStatement : Prop := by
  let M : PObj := Y
  exact ∀ (q : ℚˣ) (e : Aut X.actionObj), Mult X X q e →
    ∀ k : ℕ, q ^ k = 1 → ∀ g : B ≅ B,
      let a : Aut (Rationalization.of X.actionObj.abelianScheme) :=
        RationalAlgebraAction.underlyingIso (S := S) (D := R) e
      Rationalization.ofHom g.hom = r.hom ≫ (a ^ k).hom ≫ r.inv →
        W.IsPolarization P M.polarization ∧
          pullB g.hom M.polarization = M.polarization

include hu in
/-- Transport the actual multiple equation to the exact supplied model and
reflect its rational equality to an equality of integral homomorphisms. -/
theorem integralPolarizedPowerModel :
    IntegralPolarizedPowerModelStatement P additivity X B r W p := by
  intro q e he k hq g a hg
  let t := PolarizedAction.isogenyModelIso
    (P := P) (X := X) (B := B) (e := r) (W := W) (p := p)
  have ht := PolarizedAction.isogenyModelMultiple
    (P := P) (X := X) (B := B) (e := r) (W := W) (p := p) additivity
  have ha : Mult X X 1 (e ^ k) := by
    simpa only [hq] using multiple_pow P additivity X q e he k
  have hconj : Mult (Y) (Y) 1 (t.symm.trans ((e ^ k).trans t)) := by
    have hc := multiple_trans P.preservation P.composition P.unitCoherence
      P.associativity P.comparison P.symmetry P.stability P.square P.universality
      additivity
      (multiple_symm P.preservation P.composition P.unitCoherence P.associativity
        P.comparison P.symmetry P.stability P.square P.universality additivity ht)
      (multiple_trans P.preservation P.composition P.unitCoherence P.associativity
        P.comparison P.symmetry P.stability P.square P.universality additivity ha ht)
    simpa only [one_mul, inv_mul_cancel] using hc
  have hpow : RationalAlgebraAction.hom0 (e ^ k).hom = (a ^ k).hom := by
    exact congrArg (fun z : Aut (Rationalization.of X.actionObj.abelianScheme) => z.hom)
      (map_pow ((RationalAlgebraAction.forget S R).mapAut X.actionObj) e k)
  have hg' : Rationalization.ofHom g.hom =
      RationalAlgebraAction.hom0 (t.symm.trans ((e ^ k).trans t)).hom := by
    change Rationalization.ofHom g.hom =
      r.hom ≫ RationalAlgebraAction.hom0 (e ^ k).hom ≫ r.inv
    rw [hpow]
    exact hg
  refine ⟨(Y).isPolarization, ?_⟩
  apply Tate.ofHom_injective hu B (W.dual P)
  change homToHom0 (pullB g.hom (Y).polarization) =
    homToHom0 (Y).polarization
  rw [← rationalDualPullbackHom0_homToHom0 P.preservation P.composition
    P.unitCoherence P.associativity P.comparison P.symmetry P.stability
    W.hasDual W.hasDual W.geometry W.geometry W.inverseBundle W.evaluation
    W.inverseBundle W.evaluation (additivity (Y) (Y))]
  change rationalDualPullbackHom0 P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability W.hasDual W.hasDual
    W.geometry W.geometry W.inverseBundle W.evaluation W.inverseBundle W.evaluation
    (additivity (Y) (Y)) (Rationalization.ofHom g.hom)
    (homToHom0 (Y).polarization) = homToHom0 (Y).polarization
  rw [hg']
  have hc : rationalDualPullbackHom0 P.preservation P.composition P.unitCoherence
      P.associativity P.comparison P.symmetry P.stability W.hasDual W.hasDual
      W.geometry W.geometry W.inverseBundle W.evaluation W.inverseBundle W.evaluation
      (additivity (Y) (Y))
      (RationalAlgebraAction.hom0 (t.symm.trans ((e ^ k).trans t)).hom)
      (homToHom0 (Y).polarization) = (1 : ℚ) • homToHom0 (Y).polarization := hconj
  simpa only [one_smul] using hc

end Langlands.Shimura.PEL.PolarizedWeilLevel
