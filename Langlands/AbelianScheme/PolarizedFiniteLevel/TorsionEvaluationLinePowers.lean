import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicBundleSymmetry
import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicBundleMumfordProof
import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameLocus

/-! # The level annihilates the classes of the cubic evaluation lines -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open GroupScheme.Tate
open Langlands.AlgebraicGeometry.Picard.LineBundle (isoClass pullbackHom)

variable {P : Prerequisites.{u}} {S : Scheme.{u}} {g d n : ℕ}

/-- The actual line bundle obtained by evaluating the cubic bundle at a labelled torsion
section. Its module is the target of the corresponding torsion evaluation. -/
def Datum.torsionEvaluationLine (a : Datum P S g d n) (r : Fin (2 * g) → ZMod n) : LineBundle S :=
  (LineBundle.pullback (a.torsionPoint r)).obj a.cubicBundle

private lemma familyPointClass_poincareFamily_pow_right (a : Datum P S g d n)
    {Z : Over S} (z : Z ⟶ dualScheme a.abelian a.dualWitness.hasDual)
    (x : Z ⟶ a.abelian.X) (k : ℕ) :
    familyPointClass P.preservation a.abelian (poincareFamily a.abelian a.dualWitness.hasDual)
        z (x ^ k) =
      (familyPointClass P.preservation a.abelian (poincareFamily a.abelian a.dualWitness.hasDual)
        z x) ^ k := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero]
    exact familyPointClass_poincareFamily_one_right P.preservation a.abelian
      a.dualWitness.hasDual P.stability z
  | succ k ih =>
    rw [pow_succ, familyPointClass_poincareFamily_mul_right P.preservation a.abelian
      a.dualWitness.hasDual P.stability, ih, pow_succ]

/-- The level kills the class of the canonical diagonal bundle evaluated at a labelled
level section. The Poincaré class is powered in the abelian variable, keeping its dual
variable fixed. -/
theorem Datum.isoClass_torsionCanonicalBundle_pow (a : Datum P S g d n)
    (r : Fin (2 * g) → ZMod n) :
    (isoClass P.preservation ((LineBundle.pullback (a.torsionPoint r)).obj a.canonicalBundle)) ^ n = 1 := by
  let x : Over.mk (𝟙 S) ⟶ a.abelian.X := (Additive.toMul (enumerateTuple a.level.sections r)).val
  have hx : x ^ n = 1 := (mem_levelGroup a.abelian.toGrp (Over.mk (𝟙 S)) n x).mp
    (Additive.toMul (enumerateTuple a.level.sections r)).property
  let f := a.dualWitness.parameterMap P a.polarization
  change (isoClass P.preservation ((LineBundle.pullback x.left).obj
    (poincareDiagonalBundle a.abelian a.dualWitness.hasDual f))) ^ n = 1
  rw [isoClass_pullback_poincareDiagonalBundle, ← familyPointClass_poincareFamily_pow_right a, hx]
  exact familyPointClass_poincareFamily_one_right P.preservation a.abelian
    a.dualWitness.hasDual P.stability (x ≫ f)

/-- The `n`-th tensor power of a cubic evaluation line is actually trivial. This uses no
fibre hypothesis on the base and makes no assertion of a choice coherent across base changes. -/
theorem Datum.nonempty_torsionEvaluationLine_tensorPowIso (a : Datum P S g d n)
    (r : Fin (2 * g) → ZMod n) :
    Nonempty (tensorPow (a.torsionEvaluationLine r).obj n ≅ structureSheaf S) := by
  let L := a.torsionEvaluationLine r
  let Q : LineBundle S := ⟨tensorPow L.obj n, tensorPow_isLocallyFreeRankOne S L n⟩
  have h : isoClass P.preservation Q = isoClass P.preservation (LineBundle.trivial S) := by
    change (isoClass P.preservation ⟨tensorPow L.obj n, _⟩) = _
    rw [isoClass_tensorPow, LineBundle.isoClass_trivial]
    change (isoClass P.preservation ((LineBundle.pullback (a.torsionPoint r)).obj
      (⟨tensorPow a.canonicalBundle.obj 3, _⟩ : LineBundle a.abelian.X.left))) ^ n = 1
    rw [← LineBundle.pullbackHom_isoClass, isoClass_tensorPow, map_pow, ← pow_mul,
      Nat.mul_comm 3 n, pow_mul, LineBundle.pullbackHom_isoClass,
      a.isoClass_torsionCanonicalBundle_pow r, one_pow]
  obtain ⟨e⟩ := LineBundle.isoClass_eq_iff.mp h
  exact ⟨(LineBundle.forget S).mapIso e⟩

/-- A chosen trivialization of the level power of the actual cubic evaluation line. -/
def Datum.torsionEvaluationLinePowerIso (a : Datum P S g d n)
    (r : Fin (2 * g) → ZMod n) :
    tensorPow (a.torsionEvaluationLine r).obj n ≅ structureSheaf S :=
  (a.nonempty_torsionEvaluationLine_tensorPowIso r).some

end Langlands.AbelianScheme.PolarizedFiniteLevel
