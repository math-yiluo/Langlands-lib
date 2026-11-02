import Langlands.AbelianScheme.PolarizedFiniteLevel.CanonicalCubicBundleAmpleStatement
import Langlands.AbelianScheme.PolarizedFiniteLevel.AmpleMumfordDiagonalProof
import Langlands.AlgebraicGeometry.Picard.FieldBaseChangeAmpleReflectionProof
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Ampleness of the actual canonical diagonal bundle and its cube -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.AlgebraicGeometry.Picard

/-- A field-ample Mumford presentation makes the same diagonal bundle ample
over its original presentation field. -/
lemma poincareDiagonal_isAmple_of_fieldPresentation (P : Prerequisites.{u})
    (K : Type u) [Field K] (A : AbelianScheme (Spec (CommRingCat.of K)))
    (W : DualWitness A) (f : A.X ⟶ dualScheme A W.hasDual)
    (hf : HasFieldAmpleMumfordPresentation P.preservation P.square P.universality K A
      W.hasDual f) :
    (poincareDiagonalBundle A W.hasDual f).IsAmple := by
  obtain ⟨K', instK', iota, h⟩ :=
    poincareDiagonal_isAmple_after_fieldExtension P K A W f hf
  let : Field K' := instK'
  exact fieldBaseChangeAmpleReflection K K' (Spec.map (CommRingCat.ofHom iota))
    A.X.left A.X.hom (poincareDiagonalBundle A W.hasDual f) h

/-- The actual canonical bundle of an ordinary polarized datum over any field
is ample over that same field. -/
lemma Datum.canonicalBundle_isAmple {P : Prerequisites.{u}}
    {K : Type u} [Field K] {g d n : ℕ}
    (a : Datum P (Spec (CommRingCat.of K)) g d n) :
    a.canonicalBundle.IsAmple := by
  let F := AlgebraicClosure K
  let b : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K F))
  have hf := a.polarized.2 F b
  have ham := poincareDiagonal_isAmple_of_fieldPresentation P F
    ((baseChange b).obj a.abelian) (a.dualWitness.pullback P b)
    (dualBaseChangeMap a.abelian a.dualWitness.hasDual P.universality b
      (a.dualWitness.parameterMap P a.polarization)) hf
  have hbase : ((LineBundle.pullback
      (CategoryTheory.Limits.pullback.fst a.abelian.X.hom b)).obj
        a.canonicalBundle).IsAmple :=
    ham.of_iso ((LineBundle.forget _).mapIso
      (poincareDiagonalBaseChangeIso P.universality b a.abelian
        a.dualWitness.hasDual (a.dualWitness.parameterMap P a.polarization)))
  exact fieldBaseChangeAmpleReflection K F b a.abelian.X.left a.abelian.X.hom
    a.canonicalBundle hbase

/-- The actual cubic bundle of an ordinary polarized datum over any field is ample. -/
lemma Datum.cubicBundle_isAmple {P : Prerequisites.{u}}
    {K : Type u} [Field K] {g d n : ℕ}
    (a : Datum P (Spec (CommRingCat.of K)) g d n) :
    a.cubicBundle.IsAmple :=
  a.cubicBundle_isAmple_of_canonicalBundle a.canonicalBundle_isAmple

/-- Both actual bundles are ample, with no extra assumptions on the datum. -/
theorem canonicalCubicBundleAmple : CanonicalCubicBundleAmpleStatement.{u} := by
  intro P K _ g d n a
  exact ⟨a.canonicalBundle_isAmple, a.cubicBundle_isAmple⟩

end Langlands.AbelianScheme.PolarizedFiniteLevel
