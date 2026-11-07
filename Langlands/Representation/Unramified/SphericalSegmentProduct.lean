import Langlands.Representation.Classification.RankOneSegmentUnramified
import Langlands.Representation.Classification.LanglandsData
import Langlands.Representation.Classification.UnlinkedCuspidalContentInjectivityProof
import Langlands.Representation.Unramified.SphericalProductVector

/-! Spherical vectors in products of unramified rank-one segment socles. -/

noncomputable section

namespace Langlands.PadicField.TopologicalData

open GeneralLinear Classification

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- The norm-one fixed-space result expressed using a rank-one base class. -/
theorem IsSegmentSubrepresentation.normOne_fixedVectors_of_base
    {Δ : T.Segment.{uV,uF}}
    {π : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)}
    (hπ : T.IsSegmentSubrepresentation Δ π)
    (A : letI := T.topology; SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := 1))
    (hbase : Δ.base = (letI := T.topology; ⟨1, Nat.one_pos, A.isoClass⟩))
    (χ : F.Carrierˣ →* ℂˣ) (hχ : T.IsUnramifiedCharacter χ)
    (hA : letI := T.topology
      HasScalarCharacter A.obj.representation (MonoidHom.id _) (χ.comp determinant)) :
    letI := T.topology
    fixedVectors π.representation (T.determinantNorm Δ.degree).ker = ⊤ := by
  letI := T.topology
  obtain ⟨⟨n, hn, c⟩, m, hm⟩ := Δ
  have hn' : n = 1 := congrArg CuspidalDatum.rank hbase
  subst n
  have hc : A.isoClass = c := by
    simpa only [CuspidalDatum.mk.injEq, heq_eq_eq, true_and] using hbase.symm
  exact hπ.normOne_fixedVectors T A hc rfl χ hχ hA

/-- Every base occurs in the total cuspidal content, so scalar unramified
rank-one content makes the entire carrier of every segment socle norm-one fixed. -/
theorem SegmentProductDatum.normOne_fixedVectors_of_rankOne_content
    {n m : ℕ} (d : T.SegmentProductDatum.{uV,uF} n) (hsoc : d.HasSegmentSocles)
    (X : letI := T.topology
      Fin m → SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := 1))
    (hX : ∀ i, ∃ χ : F.Carrierˣ →* ℂˣ, T.IsUnramifiedCharacter χ ∧
      (letI := T.topology;
        HasScalarCharacter (X i).obj.representation (MonoidHom.id _) (χ.comp determinant)))
    (hcontent : d.multisegment.cuspidalContent =
      List.ofFn (fun i => (letI := T.topology;
        (⟨1, Nat.one_pos, (X i).isoClass⟩ : T.CuspidalDatum.{uV,uF})))) :
    letI := T.topology
    ∀ j, fixedVectors (d.blocks j).representation
      (T.determinantNorm (d.segments j).degree).ker = ⊤ := by
  letI := T.topology
  intro j
  have hb := (Multisegment.mem_cuspidalContent_iff d.multisegment (d.segments j).base).mpr
    ⟨d.segments j, Multiset.mem_coe.mpr (List.mem_ofFn.mpr ⟨j, rfl⟩),
      (d.segments j).base_mem_support⟩
  rw [hcontent] at hb
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp (Multiset.mem_coe.mp hb)
  obtain ⟨χ, hχ, hA⟩ := hX i
  exact (hsoc j).isSegmentSubrepresentation.normOne_fixedVectors_of_base T
    (X i) hi.symm χ hχ hA

end Langlands.PadicField.TopologicalData

namespace Langlands.Unramified.SphericalProduct

open Correspondence GeneralLinear Classification PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance (n : ℕ) : TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n
local instance (n : ℕ) : IsTopologicalGroup (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopologicalGroup n

/-- A nonzero spherical vector in any actual segment-socle product whose
cuspidal content is supplied by scalar unramified rank-one representations. -/
def sphericalSegmentProductVector
    {r m : ℕ} (d : F.canonicalTopologicalData.SegmentProductDatum.{uV,uF} (r + 1))
    (hsoc : d.HasSegmentSocles)
    (X : Fin m → SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := 1))
    (hX : ∀ i, ∃ χ : F.Carrierˣ →* ℂˣ,
      F.canonicalTopologicalData.IsUnramifiedCharacter χ ∧
      HasScalarCharacter (X i).obj.representation (MonoidHom.id _) (χ.comp determinant))
    (hcontent : d.multisegment.cuspidalContent = List.ofFn
      (fun i => (⟨1, Nat.one_pos, (X i).isoClass⟩ : F.canonicalTopologicalData.CuspidalDatum))) :
    {v : fixedVectors d.induced.representation (sphericalSubgroup F r) // v ≠ 0} := by
  have hV : ∀ j, Nontrivial (d.blocks j) := by
    intro j
    obtain ⟨A, hA, hI, -⟩ := (hsoc j).isSegmentSubrepresentation
    exact CuspidalSupport.nontrivial_of_isIrreducible _ (hρ := hI)
  exact sphericalProductVector F d.shape (fun i => (d.blocks i).representation) hV
    (d.normOne_fixedVectors_of_rankOne_content F.canonicalTopologicalData hsoc X hX hcontent)

theorem segmentProduct_fixedVectors_ne_bot
    {r m : ℕ} (d : F.canonicalTopologicalData.SegmentProductDatum.{uV,uF} (r + 1))
    (hsoc : d.HasSegmentSocles)
    (X : Fin m → SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := 1))
    (hX : ∀ i, ∃ χ : F.Carrierˣ →* ℂˣ,
      F.canonicalTopologicalData.IsUnramifiedCharacter χ ∧
      HasScalarCharacter (X i).obj.representation (MonoidHom.id _) (χ.comp determinant))
    (hcontent : d.multisegment.cuspidalContent = List.ofFn
      (fun i => (⟨1, Nat.one_pos, (X i).isoClass⟩ : F.canonicalTopologicalData.CuspidalDatum))) :
    fixedVectors d.induced.representation (sphericalSubgroup F r) ≠ ⊥ := by
  let v := sphericalSegmentProductVector F d hsoc X hX hcontent
  intro h
  have hv : v.val.val = 0 := (Submodule.mem_bot ℂ).mp (h ▸ v.val.property)
  exact v.property (Subtype.ext hv)

end Langlands.Unramified.SphericalProduct
