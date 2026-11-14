import Langlands.Representation.CuspidalSupport.JacquetDetectingFamilyLengthProof
import Langlands.AllField.Representation.CuspidalSupport.JacquetDetectingFamilyLengthStatement
import Langlands.AllField.Representation.Parabolic.NormalizedJacquetExactnessProof
noncomputable section

open CategoryTheory
open scoped BigOperators

namespace Langlands.AllField.CuspidalSupport
open Langlands.CuspidalSupport hiding JacquetDetectingFamilyLengthTheorem jacquetDetectingFamilyLength
open Langlands.AllField.CuspidalSupport

universe uF uV

namespace JacquetDetectingFamilyLengthProof
open Langlands.CuspidalSupport.JacquetDetectingFamilyLengthProof hiding jacquet_injective jacquet_length_le jacquet_length_step
open Langlands.AllField.CuspidalSupport.JacquetDetectingFamilyLengthProof
open Langlands.CuspidalSupport hiding JacquetDetectingFamilyLengthTheorem jacquetDetectingFamilyLength
open Langlands.AllField.CuspidalSupport

open _root_.Representation
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear

section Subquotient


end Subquotient

section Jacquet

variable {F : Type uF} [Field F]
  (T : LocalFieldData F) {n : ℕ} (C : BlockShape n)

/-- Normalized Jacquet descent preserves injections of smooth representations. -/
theorem jacquet_injective :
    letI := T.topology
    ∀ {A B : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F)}
      (f : A.representation.IntertwiningMap B.representation),
      Function.Injective f → Function.Injective (T.normalizedJacquetMap C f) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro A B f hf
  change Function.Injective (T.normalizedJacquetMap C f).toLinearMap
  rw [T.normalizedJacquetMap_toLinearMap_eq_coinvariantsMap]
  exact coinvariants_map_injective_of_smooth (Langlands.AllField.Parabolic.unipotentFiniteContainment F T C)
    _ hf (Langlands.AllField.Parabolic.isSmooth_radical F T C _ B.isSmooth)

/-- Consequently Jacquet module length is monotone under smooth injections. -/
theorem jacquet_length_le :
    letI := T.topology
    ∀ {A B : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F)}
      (f : A.representation.IntertwiningMap B.representation),
      Function.Injective f →
      repLength ((T.normalizedJacquetFunctor C).obj A).representation ≤
        repLength ((T.normalizedJacquetFunctor C).obj B).representation := by
  let := T.topology
  intro A B f hf
  exact Module.length_le_of_injective
    (IntertwiningMap.equivLinearMapAsModule _ _ (T.normalizedJacquetMap C f))
    (jacquet_injective T C f hf)

/-- Additivity on the actual Jacquet sequence of nested subspaces. -/
theorem jacquet_length_step :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F))
      (S U : Subrepresentation A.representation) (_h : S ≤ U),
      repLength ((T.normalizedJacquetFunctor C).obj (SmoothRep.subrepresentation A U)).representation =
        repLength ((T.normalizedJacquetFunctor C).obj (SmoothRep.subrepresentation A S)).representation +
        repLength ((T.normalizedJacquetFunctor C).obj
          (SmoothRep.subquotient A U (lower A S U))).representation := by
  let := T.topology
  intro A S U h
  let i := inclusion A S U h
  let q := SmoothRep.hom (SmoothRep.mkQ (SmoothRep.subrepresentation A U) (lower A S U))
  obtain ⟨hi, hex, hq⟩ := T.normalizedJacquetMap_exact C i q
    (SmoothRep.subrepresentation A U).isSmooth (Submodule.inclusion_injective h)
    (SmoothRep.mkQ_surjective _ _) (inclusion_exact A S U h)
  exact repLength_eq_add_of_exact (T.normalizedJacquetMap C i)
    (T.normalizedJacquetMap C q) hi hq hex

end Jacquet

end JacquetDetectingFamilyLengthProof

open Langlands.CuspidalSupport.JacquetDetectingFamilyLengthProof hiding jacquet_injective jacquet_length_le jacquet_length_step in
open Langlands.AllField.CuspidalSupport.JacquetDetectingFamilyLengthProof in
/-- A finite family of normalized Jacquet functors detecting all nonzero
subquotients bounds both module length and actual composition-series length. -/
theorem jacquetDetectingFamilyLength : JacquetDetectingFamilyLengthTheorem.{uF, uV} := by
  classical
  intro F _ T n
  let := T.topology
  intro A s b hlength hdetect
  have hbound (C : GeneralLinear.BlockShape n) (hC : C ∈ s) :
      repLength ((T.normalizedJacquetFunctor C).obj A).representation ≤ b C := by
    obtain ⟨k, hk, f, hf⟩ := hlength C hC
    rw [repLength_eq_of_hasSimpleFactors f hf]
    exact_mod_cast hk
  let L := fun (S : Subrepresentation A.representation) (C : GeneralLinear.BlockShape n) =>
    repLength ((T.normalizedJacquetFunctor C).obj (SmoothRep.subrepresentation A S)).representation
  have hL (S : Subrepresentation A.representation) (C : GeneralLinear.BlockShape n)
      (hC : C ∈ s) : L S C ≤ b C :=
    (jacquet_length_le T C (SmoothRep.hom (SmoothRep.subtype A S))
      (SmoothRep.subtype_injective A S)).trans (hbound C hC)
  have hfinite (S : Subrepresentation A.representation) (C : GeneralLinear.BlockShape n)
      (hC : C ∈ s) : L S C ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) (hL S C hC)
  have hmono (S U : Subrepresentation A.representation) (h : S ≤ U)
      (C : GeneralLinear.BlockShape n) (hC : C ∈ s) :
      (L S C).toNat ≤ (L U C).toNat :=
    ENat.toNat_le_toNat (jacquet_length_le T C (inclusion A S U h)
      (Submodule.inclusion_injective h)) (hfinite U C hC)
  let measure := fun S : Subrepresentation A.representation => ∑ C ∈ s, (L S C).toNat
  have hmeasure_bound (S : Subrepresentation A.representation) :
      measure S ≤ ∑ C ∈ s, b C :=
    Finset.sum_le_sum fun C hC => ENat.toNat_le_of_le_natCast (hL S C hC)
  have hmeasure_strict : StrictMono measure := by
    intro S U hSU
    let D := SmoothRep.subquotient A U (lower A S U)
    have hD : SmoothRep.IsSubquotient D A := ⟨U, lower A S U, ⟨Iso.refl _⟩⟩
    obtain ⟨C, hC, hnonzero⟩ := hdetect D hD (quotient_nontrivial A S U hSU)
    have hpos : 0 < repLength ((T.normalizedJacquetFunctor C).obj D).representation :=
      repLength_pos_iff.mpr hnonzero
    have hadd := jacquet_length_step T C A S U hSU.le
    have hlt : L S C < L U C := by
      change L U C = L S C + repLength ((T.normalizedJacquetFunctor C).obj D).representation at hadd
      rw [hadd]
      simpa only [add_zero] using
        (ENat.add_lt_add_iff_left (hfinite S C hC)).mpr hpos
    have hnat : (L S C).toNat < (L U C).toNat := by
      have hcast : ((L S C).toNat : ℕ∞) < ((L U C).toNat : ℕ∞) := by
        simpa only [ENat.natCast_toNat (hfinite S C hC),
          ENat.natCast_toNat (hfinite U C hC)] using hlt
      exact_mod_cast hcast
    exact Finset.sum_lt_sum (fun C hC => hmono S U hSU.le C hC) ⟨C, hC, hnat⟩
  have hchain (m : ℕ) (c : Fin (m + 1) → Subrepresentation A.representation)
      (hc : StrictMono c) : m ≤ ∑ C ∈ s, b C := by
    let q := LTSeries.mk m (fun i => measure (c i)) (hmeasure_strict.comp hc)
    have h := q.head_add_length_le_nat
    have hb := hmeasure_bound (c (Fin.last m))
    change measure (c 0) + m ≤ measure (c (Fin.last m)) at h
    omega
  have hcomp := LengthCriterionProof.hasCompositionLengthAtMost_of_bound hchain
  exact ⟨(objectCompositionLengthCriterion ℂ (GeneralLinear n F)
    (Rep.of A.representation) (∑ C ∈ s, b C)).2 hcomp, hcomp⟩

end Langlands.AllField.CuspidalSupport
