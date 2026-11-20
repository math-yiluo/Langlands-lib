import Langlands.Representation.Classification.IsobaricSum
import Langlands.Representation.Classification.CuspidalScalarNorm
import Langlands.Representation.Classification.OrderedMultisegmentHeadExistenceProof
import Langlands.Representation.Classification.MultisegmentHeadClassificationProof
import Langlands.Representation.Classification.SegmentSocleDecreasingHead
import Langlands.Representation.Classification.TadicSocleIndependence
import Langlands.Representation.Unramified.OrderedSphericalQuotient
import Langlands.Representation.Unramified.SphericalConstituentUniquenessProof
import Langlands.Representation.Unramified.SphericalSpectrumExistenceProof
import Langlands.Representation.Unramified.UnitaryPrincipalSeriesBlocks
import Langlands.Representation.Induction.BlockEquivalence
import Mathlib.Data.Fin.Tuple.Sort

/-! Sphericity of local isobaric sums of spherical representations. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.Unramified

open CategoryTheory Classification Correspondence GeneralLinear PadicField.TopologicalData

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance (n : ℕ) : TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n
local instance (n : ℕ) : IsTopologicalGroup (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopologicalGroup n

private def unramifiedSegment (z : ℂˣ) : F.canonicalTopologicalData.Segment.{uF, uF} :=
  F.canonicalTopologicalData.singletonSegment (unramifiedCuspidalDatum F z)

private theorem scalarUniformizerNorm_unramified (z : ℂˣ) :
    (unramifiedCuspidalDatum F z).scalarUniformizerNorm = ‖(z : ℂ)‖ := by
  let A := rankOneSupercuspidalObject.{uF, uF} F (character F z)
  have hω : HasScalarCharacter A.obj.representation
      GeneralLinear.scalar (character F z).toMonoidHom := by
    intro a v
    change ((character F z) (GeneralLinear.determinant (GeneralLinear.scalar a)) : ℂ) • v =
      ((character F z) a : ℂ) • v
    rw [GeneralLinear.determinant, Matrix.GeneralLinearGroup.det_scalar]
    simp
  have he := CuspidalDatum.scalarCharacter_eq_of_isRepresentedBy
    (unramifiedCuspidalDatum F z) A rfl (character F z).toMonoidHom hω
  unfold CuspidalDatum.scalarUniformizerNorm
  rw [he]
  exact congrArg (fun w : ℂˣ => ‖(w : ℂ)‖) (character_uniformizer F z)

private theorem orderedSingletons {n : ℕ} (z : Fin n → ℂˣ)
    (hz : Monotone (fun i => ‖(z i : ℂ)‖)) :
    F.canonicalTopologicalData.IsPrecedenceOrdered (fun i => unramifiedSegment F (z i)) := by
  intro i j hij h
  obtain ⟨_, d, hd, he⟩ := h
  change unramifiedCuspidalDatum F (z j) = (unramifiedCuspidalDatum F (z i)).twist (d : ℝ) at he
  have hlt := (unramifiedCuspidalDatum F (z i)).strictAnti_scalarUniformizerNorm_twist
    (show (0 : ℝ) < d by exact_mod_cast hd)
  change ((unramifiedCuspidalDatum F (z i)).twist (d : ℝ)).scalarUniformizerNorm <
    ((unramifiedCuspidalDatum F (z i)).twist 0).scalarUniformizerNorm at hlt
  rw [← he, CuspidalDatum.twist_zero, scalarUniformizerNorm_unramified,
    scalarUniformizerNorm_unramified] at hlt
  exact (not_lt_of_ge (hz hij.le)) hlt

private def spectrumMultisegment {n : ℕ} (s : Eigenvalues n) :
    F.canonicalTopologicalData.Multisegment.{uF, uF} :=
  (s : Multiset ℂˣ).map (unramifiedSegment F)

private theorem exists_sphericalHead_of_orderedTuple {r : ℕ} (z : Fin (r + 1) → ℂˣ)
    (hz : Monotone (fun i => ‖(z i : ℂ)‖)) :
    ∃ A : AutomorphicObject.{uF, uF} F r.succPNat,
      (spectrumMultisegment F (Eigenvalues.ofTuple z)).IsLanglandsHead A.obj ∧
      IsSphericalConstituent F z A := by
  let T := F.canonicalTopologicalData
  let ρ := fun i : Fin (r + 1) => unramifiedCuspidalDatum F (z i)
  let X := fun i : Fin (r + 1) => rankOneSupercuspidalObject.{uF, uF} F (character F (z i))
  have hsum : ∑ i, (ρ i).rank = r + 1 := by simp [ρ, unramifiedCuspidalDatum]
  let d := SegmentProductDatum.ofCuspidals T ρ hsum X
  have ho : d.IsPrecedenceOrdered := orderedSingletons F z hz
  have hh : d.HasSegmentHeads :=
    fun i => singletonSegment_isSegmentHead F T (ρ i) (X i) rfl
  obtain ⟨P, hP⟩ := orderedMultisegmentHeadExistence.{uF, uF} F T (r + 1) d ho hh
  obtain ⟨Q, hQ, hsph⟩ := exists_spherical_irreducible_quotient F z hz
  have e₁ := SmoothRep.equivOfIso (SegmentProductDatum.ofCuspidalsInducedIso T ρ hsum X)
  have e₂ : (T.cuspidalProductInduced ρ hsum X).representation.Equiv (principalSeriesOfTuple F z) :=
    T.normalizedProductInducedEquiv (borelShape r)
      (fun i => FiniteRepresentation.characterLineEquiv.{uF, uF}
        (determinantQuasiCharacter F 1 (character F (z i))))
  obtain ⟨hirr, f, hf⟩ := IsIrreducibleQuotient.of_equiv
    (Parabolic.equivTrans e₁ e₂).symm hQ
  obtain ⟨e⟩ := hP.2.2.nonempty_equiv_of_quotient hirr f hf
  let A : AutomorphicObject.{uF, uF} F r.succPNat :=
    ⟨Q, hirr, TwoFactorCommutativity.isAdmissible_of_isIrreducible F T
      Q.representation Q.isSmooth hirr⟩
  have hlabel : d.multisegment = spectrumMultisegment F (Eigenvalues.ofTuple z) := by
    change (List.ofFn (fun i => unramifiedSegment F (z i)) : Multiset _) =
      (List.ofFn z : Multiset ℂˣ).map (unramifiedSegment F)
    simp only [Multiset.map_coe, List.map_ofFn, Function.comp_def]
  have hhead : (spectrumMultisegment F (Eigenvalues.ofTuple z)).IsLanglandsHead P :=
    ⟨d, hlabel, hP⟩
  obtain ⟨_, q, hq⟩ := hQ
  exact ⟨A, Classification.Multisegment.IsLanglandsHead.of_iso hhead (SmoothRep.mkIso e).symm,
    hsph, WeylBranchPieces.IsSubquotient.of_surjective q hq⟩

private theorem exists_sphericalHead_of_spectrum {r : ℕ} (s : Eigenvalues (r + 1)) :
    ∃ z : Fin (r + 1) → ℂˣ, Eigenvalues.ofTuple z = s ∧
      ∃ A : AutomorphicObject.{uF, uF} F r.succPNat,
        (spectrumMultisegment F s).IsLanglandsHead A.obj ∧ IsSphericalConstituent F z A := by
  obtain ⟨z, hz⟩ := Eigenvalues.ofTuple_surjective _ s
  let e := Tuple.sort (fun i => ‖(z i : ℂ)‖)
  have horder : Monotone (fun i => ‖((z ∘ e) i : ℂ)‖) :=
    Tuple.monotone_sort (fun i => ‖(z i : ℂ)‖)
  have hs : Eigenvalues.ofTuple (z ∘ e) = s := (Eigenvalues.ofTuple_reindex z e).trans hz
  obtain ⟨A, hA, hsph⟩ := exists_sphericalHead_of_orderedTuple F (z ∘ e) horder
  rw [hs] at hA
  exact ⟨z ∘ e, hs, A, hA, hsph⟩

private theorem isLanglandsHead_of_sphericalSpectrum {r : ℕ}
    {A : AutomorphicObject.{uF, uF} F r.succPNat} {s : Eigenvalues (r + 1)}
    (h : HasSphericalSpectrum F A s) : (spectrumMultisegment F s).IsLanglandsHead A.obj := by
  obtain ⟨z, hz, hA⟩ := h
  obtain ⟨w, hw, B, hB, hsph⟩ := exists_sphericalHead_of_spectrum F s
  obtain ⟨e⟩ := sphericalConstituentUniqueness.{uF, uF, uF} p F r w z
    (hw.trans hz.symm) B A hsph hA
  exact Classification.Multisegment.IsLanglandsHead.of_iso hB (SmoothRep.mkIso e)

/-- A local isobaric sum of spherical representations has a nonzero spherical
fixed vector. The assertion applies to any supplied representative of the sum. -/
theorem isSpherical_of_isIsobaricSum {r k : ℕ} {m : Fin k → ℕ}
    (hm : ∑ i, (m i + 1) = r + 1)
    {σ : ∀ i, AutomorphicObject.{uF, uF} F (m i).succPNat}
    {A : AutomorphicObject.{uF, uF} F r.succPNat}
    (h : F.canonicalTopologicalData.IsIsobaricSum.{uF, uF} (fun i => (σ i).obj) A.obj)
    (hσ : ∀ i, fixedVectors (σ i).obj.representation (sphericalSubgroup F (m i)) ≠ ⊥) :
    fixedVectors A.obj.representation (sphericalSubgroup F r) ≠ ⊥ := by
  obtain ⟨a, hinput, hA⟩ := h
  have hspec (i : Fin k) := sphericalSpectrumExistence.{uF, uF} p F (m i) (σ i) (hσ i)
  choose s hs using hspec
  let T := F.canonicalTopologicalData
  have hlabel (i : Fin k) : a i = spectrumMultisegment F (s i) :=
    (multisegmentHeadClassification.{uF, uF} F T (m i + 1) (a i)
      (spectrumMultisegment F (s i)) (σ i).obj (σ i).obj (hinput i)
      (isLanglandsHead_of_sphericalSpectrum F (hs i))).mpr ⟨Iso.refl _⟩
  let t : Eigenvalues (r + 1) := ⟨∑ i, (s i : Multiset ℂˣ), by simpa using hm⟩
  have hsum : (∑ i, a i) = spectrumMultisegment F t := by
    calc
      _ = ∑ i, spectrumMultisegment F (s i) := Finset.sum_congr rfl (fun i _ => hlabel i)
      _ = _ := (map_sum (Multiset.mapAddMonoidHom (unramifiedSegment F))
        (fun i => (s i : Multiset ℂˣ)) Finset.univ).symm
  rw [hsum] at hA
  obtain ⟨_, _, B, hB, hsph⟩ := exists_sphericalHead_of_spectrum F t
  obtain ⟨e⟩ := (multisegmentHeadClassification.{uF, uF} F T (r + 1) _ _
    A.obj B.obj hA hB).mp rfl
  exact (fixedVectors_ne_bot_iff_of_equiv (SmoothRep.equivOfIso e) (sphericalSubgroup F r)).mpr
    hsph.1

end Langlands.Unramified
