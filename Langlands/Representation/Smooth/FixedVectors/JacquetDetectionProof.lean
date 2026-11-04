import Langlands.Representation.Smooth.FixedVectors.JacquetDetectionStatement
import Langlands.Representation.Smooth.FixedVectors.CompactRestrictionDetectionProof
import Langlands.Representation.Jacquet.FixedVectorsGenerationProof
import Langlands.Representation.Jacquet.ExactProof
import Langlands.Representation.Jacquet.IwahoriContractionAdmissibility
import Langlands.Representation.Filtration.SubquotientAlgebraProof
import Langlands.Representation.Compact.SurjectivityProof

/-! # Fixed-vector detection through actual Jacquet subquotients -/

set_option autoImplicit false

noncomputable section

namespace Langlands

universe uG uV uI

namespace SmoothRep

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- At a fixed compact open subgroup, finite dimension of fixed vectors
passes to every actual smooth subquotient. -/
theorem finiteDimensional_fixedVectors_of_isSubquotient
    {A D : SmoothRep.{0, uG, uV} ℂ G} (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (hDA : IsSubquotient D A)
    (hA : FiniteDimensional ℂ (fixedVectors A.representation K.toSubgroup)) :
    FiniteDimensional ℂ (fixedVectors D.representation K.toSubgroup) := by
  obtain ⟨C, i, q, hi, hq⟩ := isSubquotient_iff_exists.mp hDA
  let iK := Compact.fixedVectorMap C.representation A.representation (hom i) K.toSubgroup
  have hiK : Function.Injective iK := fun x y hxy =>
    Subtype.ext (hi (congrArg Subtype.val hxy))
  let := hA
  let : FiniteDimensional ℂ (fixedVectors C.representation K.toSubgroup) :=
    Module.Finite.of_injective iK hiK
  exact Module.Finite.of_surjective
    (Compact.fixedVectorMap C.representation D.representation (hom q) K.toSubgroup)
    (Compact.fixedVectorSurjectivity G C D C.representation D.representation
      C.isSmooth D.isSmooth K hK (hom q) hq)

/-- A nonzero fixed vector of an actual subquotient forces a nonzero fixed
vector of the ambient object, by compact-open exactness. -/
theorem exists_nonzero_fixedVector_of_isSubquotient
    {A D : SmoothRep.{0, uG, uV} ℂ G} (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (hDA : IsSubquotient D A)
    (hD : ∃ v : D, v ∈ fixedVectors D.representation K.toSubgroup ∧ v ≠ 0) :
    ∃ v : A, v ∈ fixedVectors A.representation K.toSubgroup ∧ v ≠ 0 := by
  obtain ⟨w, hw, hw0⟩ := hD
  obtain ⟨C, i, q, hi, hq⟩ := isSubquotient_iff_exists.mp hDA
  obtain ⟨v, hv⟩ := Compact.fixedVectorSurjectivity G C D
    C.representation D.representation C.isSmooth D.isSmooth K hK (hom q) hq ⟨w, hw⟩
  refine ⟨hom i v.val,
    (Compact.fixedVectorMap C.representation A.representation (hom i) K.toSubgroup v).property,
    ?_⟩
  intro hz
  have hv0 : v.val = 0 := hi (hz.trans (map_zero (hom i)).symm)
  have hqw : hom q v.val = w := congrArg Subtype.val hv
  apply hw0
  exact hqw.symm.trans (by rw [hv0, map_zero])

/-- Finite compact containment in the subgroup of coinvariants makes actual
smooth subquotient presentations descend to the actual Jacquet action. -/
theorem isSubquotient_jacquet_of_compactContainment
    (N M : Subgroup G) (hMN : M ≤ Subgroup.normalizer N)
    (hN : ∀ s : Finset N, ∃ L : OpenSubgroup N,
      IsCompact (L : Set N) ∧ ∀ n ∈ s, n ∈ L)
    {A D : SmoothRep.{0, uG, uV} ℂ G} (hDA : IsSubquotient D A) :
    IsSubquotient
      (of (Jacquet.action D.representation N M hMN)
        (Jacquet.isSmooth_action D.representation N M hMN D.isSmooth))
      (of (Jacquet.action A.representation N M hMN)
        (Jacquet.isSmooth_action A.representation N M hMN A.isSmooth)) := by
  obtain ⟨C, i, q, hi, hq⟩ := isSubquotient_iff_exists.mp hDA
  refine isSubquotient_iff_exists.mpr
    ⟨of (Jacquet.action C.representation N M hMN)
        (Jacquet.isSmooth_action C.representation N M hMN C.isSmooth),
      ofHom (Jacquet.map N M hMN (hom i)),
      ofHom (Jacquet.map N M hMN (hom q)), ?_, ?_⟩
  · exact coinvariants_map_injective_of_smooth hN (Jacquet.restrictMap (hom i) N) hi
      (isSmooth_comp N.subtype continuous_subtype_val A.isSmooth)
  · exact coinvariants_map_surjective (Jacquet.restrictMap (hom q) N) hq

end SmoothRep

/-- The complete Jacquet/subquotient detection composition. -/
theorem jacquetSubquotientFixedVectorDetection :
    JacquetSubquotientFixedVectorDetectionStatement.{uG, uV, uI} := by
  intro G _ _ _ N M Nbar hMN hM hN K K₀ hK hK₀ hfactor g hcon
    H _ _ _ _ _ _ μ _ hKH A D hfin hgen hDA
  let JA := SmoothRep.of (Jacquet.action A.representation N M hMN)
    (Jacquet.isSmooth_action A.representation N M hMN A.isSmooth)
  let JD := SmoothRep.of (Jacquet.action D.representation N M hMN)
    (Jacquet.isSmooth_action D.representation N M hMN D.isSmooth)
  dsimp only
  intro E ι _ _ V hVirr hVcomp hspan hE
  have hJDA : SmoothRep.IsSubquotient JD JA :=
    SmoothRep.isSubquotient_jacquet_of_compactContainment N M hMN hN hDA
  have hEJA : SmoothRep.IsSubquotient E JA :=
    smoothSubquotientTransitivity ℂ M JA JD E hE hJDA
  have hgenJA : ∀ S : Subrepresentation JA.representation,
      fixedVectors JA.representation (K.toSubgroup.comap M.subtype) ≤ S.toSubmodule →
      S = ⊤ :=
    Jacquet.fixedVectors_generate_of_factorization A.representation N M K.toSubgroup K₀
      hMN hK₀ hfactor hgen
  obtain ⟨e, he, he0⟩ := compactRestrictionFixedVectorDetection M H μ JA E
    (K.toSubgroup.comap M.subtype) hKH hgenJA ι V hVirr hVcomp hspan hEJA
  let KM : OpenSubgroup M := K.comap M.subtype continuous_subtype_val
  have hKM : IsCompact (KM : Set M) :=
    hM.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  obtain ⟨j, hj, hj0⟩ := SmoothRep.exists_nonzero_fixedVector_of_isSubquotient
    KM hKM hE ⟨e, he, he0⟩
  have hDfin := SmoothRep.finiteDimensional_fixedVectors_of_isSubquotient K hK hDA hfin
  obtain ⟨d, hd⟩ := Jacquet.fixedJacquetMap_surjective_of_iwahoriContraction
    D.representation D.isSmooth hK hcon hMN hDfin ⟨j, hj⟩
  refine ⟨d.val, d.property, ?_⟩
  intro hz
  apply hj0
  have hdj : Jacquet.mk D.representation N d.val = j := congrArg Subtype.val hd
  exact hdj.symm.trans (by rw [hz, map_zero])

end Langlands
