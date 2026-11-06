import Langlands.Representation.CompactCoefficient.FixedTypeDetection
import Langlands.Representation.CompactCoefficient.SemisimplicityProof
import Langlands.Representation.CompactCoefficient.AmbientProjector
import Langlands.Topology.Nonarchimedean.Subgroup
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected

/-! # Finite class sets detected by compact irreducible types -/

noncomputable section

open CategoryTheory MeasureTheory

namespace Langlands.CompactCoefficient

universe uG uV uI uC

section Embedding

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {I : Type uI} (N : Subgroup G) (L : Subgroup N)
  (A : I → SmoothRep.{0, uG, uV} ℂ G)
  (D : ∀ x, CompactFixedType (SmoothRep.restrictSubgroup N (A x)) L)
  (hsep : ∀ x y,
    (∃ f : (SmoothRep.restrictSubgroup N (A x)).representation.IntertwiningMap
      (SmoothRep.restrictSubgroup N (A y)).representation, f ≠ 0) → x = y)

/-- A separating family of ambient representations embeds into the fixed
stratum of its chosen compact irreducible types on the subgroup. -/
def fixedTypeClassEmbedding : I ↪ CompactCoefficientClass.fixedStratum L where
  toFun x := ⟨CompactCoefficientClass.ofRep (D x).compactRep, (D x).fixed⟩
  inj' := by
    intro x y h
    have hclass : CompactCoefficientClass.ofRep (D x).compactRep =
        CompactCoefficientClass.ofRep (D y).compactRep := congrArg Subtype.val h
    obtain ⟨e⟩ := (CompactCoefficientClass.ofRep_eq_iff _ _).mp hclass
    apply hsep x y
    exact (D x).exists_nonzero_intertwiner (D y)
      (SmoothRep.equivOfIso ((irreducibleCompactCoefficientProperty N).ι.mapIso e))

end Embedding

/-- Compact coefficients on an open subgroup, finite compact-type fixed
strata, and separation by nonzero restricted intertwiners imply finiteness
of the specified ambient irreducible classes with fixed vectors. -/
theorem finite_classes_of_compactRestriction
    {G : Type uG} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
    [LocallyCompactSpace G] [T2Space G] {C : Type uC}
    (N : Subgroup G) (hN : IsOpen (N : Set G))
    (classOf : (A : SmoothRep.{0, uG, uV} ℂ G) → A.IsIrreducible → C)
    (P : ObjectProperty (SmoothRep.{0, uG, uV} ℂ G))
    (hc : ∀ A, P A →
      HasCompactSmoothDualCoefficients (SmoothRep.restrictSubgroup N A).representation)
    (hsep : ∀ A B hA hB,
      (∃ f : (SmoothRep.restrictSubgroup N A).representation.IntertwiningMap
        (SmoothRep.restrictSubgroup N B).representation, f ≠ 0) →
      classOf A hA = classOf B hB)
    (K : Subgroup G) (L : Subgroup N)
    (hLK : ∀ x : N, x ∈ L → (x : G) ∈ K)
    (hfin : (CompactCoefficientClass.fixedStratum.{uG, uV} L).Finite) :
    Set.Finite {c : C | ∃ A hA, P A ∧ classOf A hA = c ∧
      Nontrivial (fixedVectors A.representation K)} := by
  classical
  let s : Set C := {c | ∃ A hA, P A ∧ classOf A hA = c ∧
    Nontrivial (fixedVectors A.representation K)}
  choose A hA hP hclass hfix using fun c : s => c.property
  let : LocallyCompactSpace N := hN.locallyCompactSpace
  let : MeasurableSpace N := borel N
  let : BorelSpace N := ⟨rfl⟩
  have hfixed (c : s) :
      fixedVectors (SmoothRep.restrictSubgroup N (A c)).representation L ≠ ⊥ := by
    obtain ⟨v, hv, hv0⟩ := (fixedVectors (A c).representation K).ne_bot_iff.mp
      (Submodule.nontrivial_iff_ne_bot.mp (hfix c))
    apply (fixedVectors (SmoothRep.restrictSubgroup N (A c)).representation L).ne_bot_iff.mpr
    refine ⟨v, ?_, hv0⟩
    intro x
    exact hv ⟨(x : N).val, hLK x.val x.property⟩
  let D (c : s) :
      CompactFixedType (SmoothRep.restrictSubgroup N (A c)) L :=
    detectCompactFixedType _ L
      (CompactCoefficientSemisimplicity.isSemisimpleRepresentation_of_compactCoefficients
        (Measure.haar (G := N)) _ (SmoothRep.restrictSubgroup N (A c)).isSmooth
        (hc (A c) (hP c)))
      (hc (A c) (hP c)) (hfixed c)
  have hseparate (c d : s)
      (h : ∃ f : (SmoothRep.restrictSubgroup N (A c)).representation.IntertwiningMap
        (SmoothRep.restrictSubgroup N (A d)).representation, f ≠ 0) : c = d := by
    apply Subtype.ext
    exact (hclass c).symm.trans ((hsep (A c) (A d) (hA c) (hA d) h).trans (hclass d))
  let e := fixedTypeClassEmbedding N L A D hseparate
  let : Finite (CompactCoefficientClass.fixedStratum.{uG, uV} L) := hfin.to_subtype
  let : Finite s := Finite.of_injective e e.injective
  exact Set.finite_coe_iff.mp inferInstance

end Langlands.CompactCoefficient
