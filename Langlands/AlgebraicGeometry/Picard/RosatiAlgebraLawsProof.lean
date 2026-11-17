import Langlands.AlgebraicGeometry.Picard.RosatiAlgebraLawsStatement
import Langlands.AlgebraicGeometry.Picard.RosatiPrimeAdjunction
import Langlands.AlgebraicGeometry.Picard.FiniteWeilAlternationProof
import Langlands.AbelianScheme.Tate.WeilRationalPolarizationAlternationProof
import Langlands.AbelianScheme.Tate.FieldPrimeRationalFaithfulnessProof

/-! # Algebra laws of the actual rational Rosati operation -/

universe u

open CategoryTheory AlgebraicGeometry

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Langlands.AbelianScheme.Rosati

section Algebra

variable (P : Prerequisites.{u}) {S : Scheme.{u}}
  {A : AbelianScheme S} (W : DualData A) (hadd : W.Additivity P)

/-- Actual rational dualization preserves the identity. -/
lemma DualData.dual0_id : W.dual0 P hadd (id0 A) = id0 (W.dual P) := by
  unfold DualData.dual0
  apply dualHom0_id

/-- Actual rational dualization reverses composition. -/
lemma DualData.dual0_comp (a b : End0 A) :
    W.dual0 P hadd (comp0 A A A a b) =
      comp0 (W.dual P) (W.dual P) (W.dual P)
        (W.dual0 P hadd b) (W.dual0 P hadd a) := by
  unfold DualData.dual0
  apply dualHom0_comp

variable (lam : A ⟶ W.dual P) [HasRationalInverse P W lam]

/-- Conjugation by the actual polarization reverses multiplication. -/
theorem involution_mul (a b : End0 A) :
    involution P W hadd lam (a * b) =
      involution P W hadd lam b * involution P W hadd lam a := by
  simp only [end0_mul, involution_apply, DualData.dual0_comp, comp0_assoc]
  rw [← comp0_assoc (polarizationInverse P W lam) (homToHom0 lam),
    inverse_comp_polarization, id0_comp0]

/-- Conjugation fixes the actual rational identity. -/
theorem involution_id :
    involution P W hadd lam (id0 A) = id0 A := by
  rw [involution_apply, DualData.dual0_id, comp0_id0, polarization_comp_inverse]

/-- Conjugation fixes every rational scalar endomorphism. -/
theorem involution_algebraMap (q : ℚ) :
    involution P W hadd lam (algebraMap ℚ (End0 A) q) =
      algebraMap ℚ (End0 A) q := by
  have hq : algebraMap ℚ (End0 A) q = q • id0 A := by
    rw [Algebra.algebraMap_eq_smul_one]
    rfl
  rw [hq, map_smul, involution_id]

end Algebra

section Involutivity

variable (P : Prerequisites.{u}) {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
  {A : AbelianScheme (Spec (.of k))} (W : DualData A) (hadd : W.Additivity P)
  (lam : A ⟶ W.dual P) (hpol : W.IsPolarization P lam)
  [hInverse : HasRationalInverse P W lam]

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

include hpol

/-- Alternation and nondegeneracy of the actual Weil pairing make Rosati involutive. -/
theorem involution_involutive (a : End0 A) :
    involution P W hadd lam (involution P W hadd lam a) = a := by
  let T : Over (Spec (.of k)) := Over.mk (𝟙 _)
  let E := primeRationalWeilAlongHomBilinearMap P.preservation P.composition
    P.unitCoherence P.associativity P.comparison P.symmetry P.stability W.hasDual
    W.geometry W.inversePoincare W.evaluation relativeFiniteWeilTransition T 2 lam
  have hE : E.Nondegenerate := primeRationalPolarizationWeilNondegeneracy
    P.preservation P.square P.universality P.composition P.unitCoherence P.associativity
    P.comparison P.symmetry P.stability relativeFiniteWeilTransition _ A W.hasDual
    W.geometry W.inversePoincare W.evaluation lam hpol k (𝟙 _) 2 (by norm_num)
  have hAlt : E.IsAlt := primeRationalWeilAlongPolarization_isAlt
    P.preservation P.square P.universality P.composition P.unitCoherence P.associativity
    P.comparison P.symmetry P.stability relativeFiniteWeilTransition
    relativeFiniteWeilAlternation W.hasDual W.geometry W.inversePoincare W.evaluation
    T lam hpol 2
  apply Tate.fieldPrimeRationalFaithfulness k A A 2
  apply LinearMap.ext
  intro y
  apply sub_eq_zero.mp
  apply hE.2
  intro x
  rw [map_sub, sub_eq_zero]
  calc
    E x (Tate.PrimeAdic.rationalHomMap T 2
        (involution P W hadd lam (involution P W hadd lam a)) y) =
        E (Tate.PrimeAdic.rationalHomMap T 2 (involution P W hadd lam a) x) y :=
      (primeWeil_involution P W hadd relativeFiniteWeilTransition T 2 lam
        (involution P W hadd lam a) x y).symm
    _ = -E y (Tate.PrimeAdic.rationalHomMap T 2 (involution P W hadd lam a) x) :=
      (hAlt.neg _ _).symm
    _ = -E (Tate.PrimeAdic.rationalHomMap T 2 a y) x :=
      congrArg Neg.neg
        (primeWeil_involution P W hadd relativeFiniteWeilTransition T 2 lam a y x).symm
    _ = E x (Tate.PrimeAdic.rationalHomMap T 2 a y) := hAlt.neg _ _

end Involutivity

/-- The full existing actual rational Rosati algebra-law statement. -/
theorem algebraLaws : AlgebraLawsStatement.{u} := by
  intro P k _ _ _ A W hadd lam hpol hInv
  exact ⟨(involution P W hadd lam).map_add,
    (involution P W hadd lam).map_smul,
    involution_mul P W hadd lam,
    involution_algebraMap P W hadd lam,
    involution_involutive (k := k) (A := A) P W hadd lam hpol (hInverse := hInv)⟩

end Langlands.AbelianScheme.Rosati
