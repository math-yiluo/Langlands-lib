import Langlands.Representation.Exponents.RepresentedJacquetLengthWitnessStatement
import Langlands.Representation.Exponents.MaximalLeviSupercuspidalLengthTwoReduction
import Langlands.Representation.Aubert.General.AlternatingOperator
import Langlands.Representation.Filtration.ExactFamilyLengthProof

/-! # From an actual detecting Jacquet family to length two -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

section Witness

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance witnessReductionAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

/-- Exactness of the actual Jacquet functor to the Levi's own point group, for
every short exact sequence, from an explicit compact-limit radical. -/
theorem leviJacquetFunctor_mapsShortExactIntertwiners
    (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r))
    (hUc : Jacquet.Localization.IsLimitOfCompactSubgroups (pointImage (r ≫ p))) :
    letI := leviPointTopology l hl
    Derivative.Mirabolic.MapsShortExactIntertwiners
      (leviJacquetFunctor.{u, w} p l r hp hr hl hmul) := by
  let := leviPointTopology l hl
  intro A B C f g hf hg hex
  have h := Langlands.Aubert.General.jacquetFunctor_map_isShortExact
    (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul)
    (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
    hUc f g ⟨hf, hg, hex⟩
  exact ⟨h.1, h.2.2, h.2.1⟩

/-- Actual finite-family image bounds and irreducible-subquotient detection
bound composition length, without a source finite-length premise. -/
theorem repLength_le_of_hasRepresentedJacquetLengthWitness
    (A : SmoothRep.{0, u, w} ℂ (rationalPoints G)) {bound : ℕ}
    (hA : HasRepresentedJacquetLengthWitness A bound) :
    repLength A.representation ≤ (bound : ℕ∞) := by
  classical
  obtain ⟨n, P, M, U, p, l, r, hp, hl, hr, hmul, hUc, b, hbudget, hb, hdet⟩ := hA
  let : ∀ i : Fin n, TopologicalSpace (rationalPoints (M i)) :=
    fun i => leviPointTopology (l i) (hl i)
  let F (i : Fin n) : SmoothRep.{0, u, w} ℂ (rationalPoints G) ⥤
      SmoothRep.{0, u, w} ℂ (rationalPoints (M i)) :=
    leviJacquetFunctor (p i) (l i) (r i) (hp i) (hr i) (hl i) (hmul i)
  have hF : ∀ i, Derivative.Mirabolic.MapsShortExactIntertwiners (F i) :=
    fun i => leviJacquetFunctor_mapsShortExactIntertwiners
      (p i) (l i) (r i) (hp i) (hl i) (hr i) (hmul i) (hUc i)
  obtain ⟨m, hm, s, hs⟩ := exactFamilyLengthBound
    (Fin n) (rationalPoints G) (fun i => rationalPoints (M i)) F hF A b hb hdet
  rw [repLength_eq_of_hasSimpleFactors s hs]
  exact_mod_cast hm.trans hbudget

end Witness

/-- The actual Jacquet-family witness supplies the represented maximal-Levi
length bound; its existence is the remaining geometric/support input. -/
theorem maximalLeviSupercuspidalLengthBound_of_jacquetLengthWitness
    (hwitness : MaximalLeviSupercuspidalJacquetLengthWitnessStatement.{u, v}) :
    MaximalLeviSupercuspidalInductionLengthBoundStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  let := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M U p l r hp hl hr hmul hproper hmax
  let := hl.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  let : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  let : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  intro ρ hirr hsc
  exact repLength_le_of_hasRepresentedJacquetLengthWitness _
    (hwitness k G hG P M U p l r hp hl hr hmul hproper hmax ρ hirr hsc)

/-- The same witness yields the actual irreducible subrepresentation and quotient
of a reducible maximal-Levi supercuspidal induction. -/
theorem maximalLeviSupercuspidalLengthTwo_of_jacquetLengthWitness
    (hwitness : MaximalLeviSupercuspidalJacquetLengthWitnessStatement.{u, v}) :
    MaximalLeviSupercuspidalInductionLengthTwoStatement.{u, v} :=
  maximalLeviSupercuspidalLengthTwo_of_lengthBound
    (maximalLeviSupercuspidalLengthBound_of_jacquetLengthWitness hwitness)

end Langlands.Aubert.General.RepresentedParabolic
