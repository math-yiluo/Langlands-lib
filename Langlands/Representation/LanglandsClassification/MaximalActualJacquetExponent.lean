import Langlands.Representation.Exponents.ArbitraryParabolicExponentProof
import Langlands.Representation.Exponents.JacquetNontrivialityTransfer
import Langlands.Representation.Exponents.LeviCuspidalEmbeddingSteps
import Langlands.Representation.LanglandsClassification.MaximalPositiveProjection
import Mathlib.Basic.Finite.Sigma

/-! # Maximal selection among actual normalized Jacquet exponents

The published VII.1.1 decomposition makes the actual exponent set nonempty
exactly when the Jacquet module is nonzero. Its finite-support assertion
then permits a maximal-norm choice over finitely many supplied parabolics.
The chosen element retains its parabolic label and actual character.
-/

noncomputable section

universe u v w z

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance actualExponentAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

/-- For an admissible representation, the actual normalized Jacquet spectrum
is nonempty exactly when the normalized Jacquet module is nonzero. -/
theorem normalizedJacquetExponents_nonempty_iff
    (hG : IsConnectedReductive G)
    {P M U : GroupScheme (Spec (CommRingCat.of k))}
    {A : CommGroupScheme (Spec (CommRingCat.of k))}
    (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r)) {a : A.toGrp ⟶ M}
    (ha : IsSplitComponent a) (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (hadm : π.IsAdmissible) :
    (normalizedJacquetExponents p l r hp hl hr hmul ha π).Nonempty ↔
      Nontrivial ((jacquetFunctor p l r hp hr hl hmul).obj π) := by
  constructor
  · rintro ⟨χ, hχ⟩
    exact nontrivial_jacquet_of_isNormalizedJacquetExponent p l r hp hl hr hmul ha π χ hχ
  · intro hJ
    have := hJ
    by_contra hempty
    have : IsEmpty (normalizedJacquetExponents p l r hp hl hr hmul ha π) :=
      ⟨fun χ => hempty ⟨χ.val, χ.property⟩⟩
    have hspan := ((arbitraryParabolicExponent k G hG).1
      P M U A p l r a hp hl hr hmul ha π hadm).2.1
    have hbot :
        (⨆ χ : normalizedJacquetExponents p l r hp hl hr hmul ha π,
          (normalizedJacquetWeightSpace p l r hp hl hr hmul ha π χ).toSubmodule) = ⊥ :=
      iSup_of_empty _
    exact bot_ne_top (hbot.symm.trans hspan)

section Family

variable {Index : Type w}
  (D : Index → ParabolicDatum G)
  (A : Index → CommGroupScheme (Spec (CommRingCat.of k)))
  (a : ∀ j, (A j).toGrp ⟶ (D j).M) (ha : ∀ j, IsSplitComponent (a j))
  (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))

/-- An actual exponent together with the original supplied parabolic label.
Characters of different split components remain in their original types. -/
def taggedActualJacquetExponents : Type (max u w) :=
  Σ j : Index, normalizedJacquetExponents
    (D j).p (D j).l (D j).r (D j).hp (D j).hl (D j).hr (D j).hmul (ha j) π

/-- Finite length and admissibility give finitely many tagged actual
exponents over any finite family of supplied parabolic data. -/
theorem finite_taggedActualJacquetExponents [Finite Index]
    (hG : IsConnectedReductive G) (hadm : π.IsAdmissible) (hfl : π.HasFiniteLength) :
    Finite (taggedActualJacquetExponents D A a ha π) := by
  have : ∀ j : Index, Finite (normalizedJacquetExponents
      (D j).p (D j).l (D j).r (D j).hp (D j).hl (D j).hr (D j).hmul (ha j) π) :=
    fun j => (((arbitraryParabolicExponent k G hG).1
      (D j).P (D j).M (D j).U (A j) (D j).p (D j).l (D j).r (a j)
      (D j).hp (D j).hl (D j).hr (D j).hmul (ha j) π hadm).2.2 hfl).to_subtype
  unfold taggedActualJacquetExponents
  infer_instance

/-- A tagged exponent exists precisely when one of the supplied actual
Jacquet modules is nonzero. No finite-length hypothesis is needed. -/
theorem nonempty_taggedActualJacquetExponents_iff
    (hG : IsConnectedReductive G) (hadm : π.IsAdmissible) :
    Nonempty (taggedActualJacquetExponents D A a ha π) ↔
      ∃ j : Index, Nontrivial
        ((jacquetFunctor (D j).p (D j).l (D j).r
          (D j).hp (D j).hr (D j).hl (D j).hmul).obj π) := by
  constructor
  · rintro ⟨⟨j, χ⟩⟩
    exact ⟨j, nontrivial_jacquet_of_isNormalizedJacquetExponent
      (D j).p (D j).l (D j).r (D j).hp (D j).hl (D j).hr (D j).hmul
      (ha j) π χ.val χ.property⟩
  · rintro ⟨j, hj⟩
    obtain ⟨χ, hχ⟩ := (normalizedJacquetExponents_nonempty_iff hG
      (D j).p (D j).l (D j).r (D j).hp (D j).hl (D j).hr (D j).hmul
      (ha j) π hadm).mpr hj
    exact ⟨⟨j, ⟨χ, hχ⟩⟩⟩

variable [Finite Index] (hG : IsConnectedReductive G)
  (hadm : π.IsAdmissible) (hfl : π.HasFiniteLength)
  (hne : ∃ j : Index, Nontrivial
    ((jacquetFunctor (D j).p (D j).l (D j).r
      (D j).hp (D j).hr (D j).hl (D j).hmul).obj π))
  {E : Type z} [NormedAddCommGroup E]
  (positive : taggedActualJacquetExponents D A a ha π → E)

/-- Choose a maximal-norm supplied positive part of an actual exponent,
retaining both its parabolic label and its split-component character. -/
def maximalActualJacquetExponent : taggedActualJacquetExponents D A a ha π := by
  classical
  letI := finite_taggedActualJacquetExponents D A a ha π hG hadm hfl
  letI := Fintype.ofFinite (taggedActualJacquetExponents D A a ha π)
  letI := (nonempty_taggedActualJacquetExponents_iff D A a ha π hG hadm).mpr hne
  exact (Renard.maximalPositiveProjectionIndex Finset.univ Finset.univ_nonempty positive).val

/-- The selected norm dominates the supplied positive part of every
actual exponent in the finite family. -/
theorem norm_le_maximalActualJacquetExponent
    (x : taggedActualJacquetExponents D A a ha π) :
    ‖positive x‖ ≤
      ‖positive (maximalActualJacquetExponent D A a ha π hG hadm hfl hne positive)‖ := by
  classical
  let := finite_taggedActualJacquetExponents D A a ha π hG hadm hfl
  let := Fintype.ofFinite (taggedActualJacquetExponents D A a ha π)
  let := (nonempty_taggedActualJacquetExponents_iff D A a ha π hG hadm).mpr hne
  exact Renard.norm_le_maximalPositiveProjectionIndex Finset.univ
    Finset.univ_nonempty positive (Finset.mem_univ x)

end Family

end Langlands.Aubert.General.RepresentedParabolic
