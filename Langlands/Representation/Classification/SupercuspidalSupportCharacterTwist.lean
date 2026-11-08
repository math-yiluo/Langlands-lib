import Langlands.Representation.Classification.MultisegmentConstituentCharacterTwistCompatibilityProof
import Langlands.Representation.Classification.SupercuspidalSupportTwist
import Langlands.Representation.Induction.NormalizedProductCharacterTwist

/-! # Arbitrary smooth determinant-character twists of actual supports -/

noncomputable section

open CategoryTheory

universe uF uV

namespace Langlands.PadicField.TopologicalData

open GeneralLinear

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-- Twist the actual class of a cuspidal datum by a smooth field character. -/
def CuspidalDatum.characterTwist
    (χ : letI := T.topology; Induction.SmoothCharacter ℂ F.Carrierˣ)
    (ρ : CuspidalDatum.{uV, uF} T) : CuspidalDatum.{uV, uF} T :=
  letI := T.topology
  Langlands.Classification.cuspidalCharacterTwist χ.toMonoidHom χ.isOpen_ker ρ

@[simp]
theorem CuspidalDatum.characterTwist_rank
    (χ : letI := T.topology; Induction.SmoothCharacter ℂ F.Carrierˣ)
    (ρ : CuspidalDatum.{uV, uF} T) : (ρ.characterTwist χ).rank = ρ.rank := rfl

set_option maxHeartbeats 2000000 in
/-- The actual normalized product twist, as an isomorphism of smooth objects. -/
def normalizedProductCharacterTwistIso {n : ℕ} (B : BlockShape n)
    (χ : letI := T.topology; Induction.SmoothCharacter ℂ F.Carrierˣ)
    (A : letI := T.topology
      ∀ i : Fin B.length, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (((T.normalizedProductInductionFunctor B).obj A).twist
      (χ.toMonoidHom.comp determinant)
      (χ.isOpen_ker.preimage (T.generalLinearDeterminant n).continuous)) ≅
      (T.normalizedProductInductionFunctor B).obj
        (fun i => (A i).twist (χ.toMonoidHom.comp determinant)
          (χ.isOpen_ker.preimage (T.generalLinearDeterminant (B.size i)).continuous)) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  let e := T.normalizedProductDeterminantTwistEquiv B χ
    (fun i => (A i).representation)
  refine SmoothRep.mkIso ?_
  simp only [normalizedProductInductionFunctor_obj]
  exact e

/-- A supplied constituent twists by any smooth field character, in every block. -/
theorem IsCuspidalConstituent.characterTwist {r : ℕ}
    {ρ : Fin r → CuspidalDatum.{uV, uF} T} {n : ℕ}
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (hπ : T.IsCuspidalConstituent ρ π)
    (χ : letI := T.topology; Induction.SmoothCharacter ℂ F.Carrierˣ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    T.IsCuspidalConstituent (fun i => (ρ i).characterTwist χ)
      (π.twist (χ.toMonoidHom.comp determinant)
        (χ.isOpen_ker.preimage (T.generalLinearDeterminant n).continuous)) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  obtain ⟨h, A, hA, hirr, hsub⟩ := hπ
  let As (i : Fin r) : SupercuspidalRep.{uF, uV}
      (F := F.Carrier) (n := (ρ i).rank) :=
    SupercuspidalRep.twist (χ.toMonoidHom.comp determinant)
      (χ.isOpen_ker.preimage (T.generalLinearDeterminant (ρ i).rank).continuous)
      (ker_determinant_le_ker_comp χ.toMonoidHom) (A i)
  refine ⟨h, As, ?_, (SmoothRep.isIrreducible_twist_iff _ _ π).mpr hirr, ?_⟩
  · intro i
    change (As i).isoClass = SupercuspidalClass.twist (χ.toMonoidHom.comp determinant)
      (χ.isOpen_ker.preimage (T.generalLinearDeterminant (ρ i).rank).continuous)
      (ker_determinant_le_ker_comp χ.toMonoidHom) (ρ i).cls
    rw [← show (A i).isoClass = (ρ i).cls from hA i]
    rfl
  · have hprod : T.cuspidalProductInduced (fun i => (ρ i).characterTwist χ) h As =
        (T.normalizedProductInductionFunctor.{uF, uV} (T.cuspidalShape ρ h)).obj
          (fun i => (As i).obj) := rfl
    rw [hprod]
    change SmoothRep.IsSubquotient π
      ((T.normalizedProductInductionFunctor (T.cuspidalShape ρ h)).obj
        (fun i => (A i).obj)) at hsub
    exact (hsub.twist (χ.toMonoidHom.comp determinant)
      (χ.isOpen_ker.preimage (T.generalLinearDeterminant n).continuous)).of_iso_right
        (normalizedProductCharacterTwistIso (T.cuspidalShape ρ h) χ (fun i => (A i).obj))

/-- A smooth determinant twist transports every supplied supercuspidal support. -/
theorem IsSupercuspidalSupport.characterTwist {n : ℕ}
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    {a : Multiset (CuspidalDatum.{uV, uF} T)}
    (ha : T.IsSupercuspidalSupport π a)
    (χ : letI := T.topology; Induction.SmoothCharacter ℂ F.Carrierˣ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    T.IsSupercuspidalSupport
      (π.twist (χ.toMonoidHom.comp determinant)
        (χ.isOpen_ker.preimage (T.generalLinearDeterminant n).continuous))
      (a.map (CuspidalDatum.characterTwist χ)) := by
  obtain ⟨r, ρ, rfl, hρ⟩ := ha
  refine ⟨r, fun i => (ρ i).characterTwist χ, ?_, hρ.characterTwist χ⟩
  rw [Multiset.map_coe, List.map_ofFn]
  rfl

end Langlands.PadicField.TopologicalData
