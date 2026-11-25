import Langlands.AlgebraicGeometry.Picard.Rosati
import Langlands.AbelianScheme.Tate.WeilRationalFunctorialityProof
import Langlands.AbelianScheme.Tate.WeilPrimeRationalPolarizationNondegeneracyProof
import Langlands.AlgebraicGeometry.Picard.FiniteWeilTransitionProof
import Langlands.AbelianScheme.Tate.TwistRankProof
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-! # Actual prime Weil adjunction for Rosati conjugation -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Langlands.AbelianScheme.Rosati

section PrimeAdjunction

variable (P : Prerequisites.{u}) {S : Scheme.{u}} [QuasiSeparatedSpace S]
  {A : AbelianScheme S} (W : DualData A) (hadd : W.Additivity P)
  (compatibility : RelativeFiniteWeilTransitionStatement.{u})
  (T : Over S) (p : ℕ) [Fact p.Prime]

local notation "primePair" => primeRationalWeilBilinearMap P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability W.hasDual
  W.inversePoincare W.evaluation compatibility T p
local notation "fullPair" => rationalWeilBilinearMap P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability W.hasDual
  W.inversePoincare W.evaluation compatibility T (fun _ => True)

/-- Prime extraction of the actual rational Weil adjunction. -/
theorem primeWeil_dual0 (a : End0 A)
    (x : Tate.PrimeAdic.Rational A T p)
    (y : Tate.PrimeAdic.Rational (W.dual P) T p) :
    primePair (Tate.PrimeAdic.rationalHomMap T p a.asHom x) y =
      primePair x (Tate.PrimeAdic.rationalHomMap T p (W.dual0 P hadd a).asHom y) := by
  obtain ⟨x, rfl⟩ := Tate.PrimeComparison.rationalFullToPrime_surjective T p A x
  obtain ⟨y, rfl⟩ := Tate.PrimeComparison.rationalFullToPrime_surjective T p (W.dual P) y
  have h := rationalWeilFunctoriality P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability compatibility S A A W.hasDual
    W.hasDual W.geometry W.geometry W.inversePoincare W.evaluation W.inversePoincare
    W.evaluation hadd T (fun _ => True) a.asHom x y
  change fullPair (Tate.rationalHomMap T (fun _ => True) a.asHom x) y =
    fullPair x (Tate.rationalHomMap T (fun _ => True) (W.dual0 P hadd a).asHom y) at h
  have h' := congrArg (TateTwist.Divisibility.rationalFullToPrime Γ(T.left, ⊤) p) h
  rw [rationalFullToPrime_rationalWeilBilinearMap,
    rationalFullToPrime_rationalWeilBilinearMap] at h'
  change primePair
    (Tate.PrimeComparison.rationalFullToPrime A T p
      (Tate.rationalHomMap T (fun _ => True) a.asHom x))
    (Tate.PrimeComparison.rationalFullToPrime (W.dual P) T p y) =
    primePair (Tate.PrimeComparison.rationalFullToPrime A T p x)
      (Tate.PrimeComparison.rationalFullToPrime (W.dual P) T p
        (Tate.rationalHomMap T (fun _ => True) (W.dual0 P hadd a).asHom y)) at h'
  simpa only [Tate.PrimeComparison.rationalFullToPrime_homMap] using h'

/-- Adjointness for the actual prime Weil pairing pulled back along `lam`. -/
def IsPrimeWeilAdjoint (lam : A ⟶ W.dual P) (a b : End0 A) : Prop :=
  ∀ x y : Tate.PrimeAdic.Rational A T p,
    primeRationalWeilAlongHomBilinearMap P.preservation P.composition P.unitCoherence
      P.associativity P.comparison P.symmetry P.stability W.hasDual W.geometry
      W.inversePoincare W.evaluation compatibility T p lam
      (Tate.PrimeAdic.rationalHomMap T p a.asHom x) y =
    primeRationalWeilAlongHomBilinearMap P.preservation P.composition P.unitCoherence
      P.associativity P.comparison P.symmetry P.stability W.hasDual W.geometry
      W.inversePoincare W.evaluation compatibility T p lam x
      (Tate.PrimeAdic.rationalHomMap T p b.asHom y)

variable (lam : A ⟶ W.dual P) [HasRationalInverse P W lam]

/-- The defining Rosati conjugation is adjoint for the actual polarization pairing. -/
theorem primeWeil_involution (a : End0 A) :
    IsPrimeWeilAdjoint P W compatibility T p lam a (involution P W hadd lam a) := by
  intro x y
  have hc : comp0 A A (W.dual P) (involution P W hadd lam a).asHom (homToHom0 lam) =
      comp0 A (W.dual P) (W.dual P) (homToHom0 lam) (W.dual0 P hadd a).asHom := by
    rw [involution_apply, comp0_assoc, inverse_comp_polarization, comp0_id0]
  have ht := LinearMap.congr_fun
    (congrArg (Tate.PrimeAdic.rationalHomMap T p) hc) y
  change (Tate.PrimeAdic.rationalHomMap T p
      (Langlands.Rationalization.comp A A (W.dual P)
        (involution P W hadd lam a).asHom (homToHom0 lam))) y =
    (Tate.PrimeAdic.rationalHomMap T p
      (Langlands.Rationalization.comp A (W.dual P) (W.dual P)
        (homToHom0 lam) (W.dual0 P hadd a).asHom)) y at ht
  simp only [Tate.PrimeAdic.rationalHomMap_comp, LinearMap.comp_apply,
    homToHom0, Tate.PrimeAdic.rationalHomMap_ofHom] at ht
  rw [primeRationalWeilAlongHomBilinearMap_apply,
    primeRationalWeilAlongHomBilinearMap_apply]
  exact (primeWeil_dual0 P W hadd compatibility T p a x _).trans
    (congrArg (primePair x) ht.symm)

end PrimeAdjunction

end Langlands.AbelianScheme.Rosati
