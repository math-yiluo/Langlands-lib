import Langlands.Representation.Aubert.General.CorrectedOrbitJacquet
import Langlands.Representation.Aubert.General.CorrectedGradedNatural

/-!
# Naturality of the explicit orbit Jacquet data

The orbit Jacquet data `orbitJacquetData` of `CorrectedOrbitJacquet` are built from
Haar measures and a quotient measure that do not depend on the representation `E`.
For two representations and the same measures, they are natural along every
`φ : A ⟶ B` in the sense of `OrbitJacquetData.IsNatural`; this is
`orbitJacquetMap_natural` at every surviving `s`. Under the compact-limit hypothesis
on `U_I ∩ P_I`, `naturalOrbitJacquetData` is one such family for all representations,
natural along every morphism.
-/

noncomputable section

open CategoryTheory MeasureTheory MeasureTheory.Measure
open Langlands.QuotientIntegration
open scoped NNReal

namespace Langlands.Aubert.General.CorrectedFiltration

universe uI uG uV

section Natural

variable {ι : Type uI} [LinearOrder ι] [Fintype ι]
variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] [T2Space G]
variable {P M U : Finset ι → Subgroup G}
  (h : ∀ J, IsSemidirectDecomposition (P J) (M J) (U J))
  (hclosed : ∀ J, IsClosed (U J : Set G)) (hU : Antitone U)
  (hP : Monotone P) (hPc : ∀ J, IsClosed (P J : Set G))
variable (T : Subgroup G) {Mx : CoxeterMatrix ι}
  (cs : CoxeterSystem Mx (Group.RelativeWeyl.Weyl T))
variable (I : Finset ι) (w : Group.RelativeWeyl.Weyl T) (m : G) (K : Finset ι)
  (hK : ∀ x : G, x ∈ M I ↔ m⁻¹ * x * m ∈ M K)

/-- The explicit orbit Jacquet data of `A` and `B`, built from the same measures,
are natural along every `φ : A ⟶ B`. -/
theorem orbitJacquetData_isNatural
    (hS1 : ∀ s, K ⊆ Finset.univ \ s →
      Group.RelativeWeylIndexing.IsMinimal cs (Finset.univ \ s) I w →
      ∀ x ∈ U I, m⁻¹ * x * m ∈ P (Finset.univ \ s) → m⁻¹ * x * m ∈ U K)
    (hS2 : ∀ s, K ⊆ Finset.univ \ s →
      Group.RelativeWeylIndexing.IsMinimal cs (Finset.univ \ s) I w →
      ∀ x ∈ M (Finset.univ \ s), x ∈ U K → m * x * m⁻¹ ∈ U I)
    (hr : Continuous (h I).projection)
    (hD07 : ∀ l : M I,
      (HaarModulus.closedRestrictCharacter (U I) (hclosed I) (M I) (h I).levi_le_normalizer l :
          ℝ≥0) *
          (HaarModulus.closedRestrictCharacter (U K) (hclosed K) (M K) (h K).levi_le_normalizer
            (conjugationEquiv m hK l) : ℝ≥0) =
        (HaarModulus.closedRestrictCharacter (orbitUnipotentIntersection (U I) (U K) m)
            (isClosed_orbitUnipotentIntersection (hclosed I) (hclosed K) m) (M I)
            (levi_le_normalizer_orbitUnipotentIntersection (h I) (h K) m hK) l : ℝ≥0) ^ 2)
    [MeasurableSpace (h I).projection.ker] [BorelSpace (h I).projection.ker]
    [MeasurableSpace (orbitKernelIntersection (h I) (U K) m)]
    [BorelSpace (orbitKernelIntersection (h I) (U K) m)]
    [MeasurableSpace (LeftQuotient (orbitKernelIntersection (h I) (U K) m))]
    [BorelSpace (LeftQuotient (orbitKernelIntersection (h I) (U K) m))]
    (μN : Measure (h I).projection.ker) (μI : Measure (orbitKernelIntersection (h I) (U K) m))
    [IsHaarMeasure μN] [μN.Regular] [IsMulRightInvariant μN]
    [IsHaarMeasure μI] [μI.Regular] [IsMulRightInvariant μI]
    (ν : Measure (LeftQuotient (orbitKernelIntersection (h I) (U K) m)))
    [IsFiniteMeasureOnCompacts ν]
    (hCompatible : IsCompatible (orbitKernelIntersection (h I) (U K) m) μN μI ν)
    {A B : SmoothRep.{0, uG, max uG uV} ℂ G} (φ : A ⟶ B) :
    (orbitJacquetData h hclosed hU hP hPc T cs I A w m K hK hS1 hS2 hr hD07 μN μI ν
        hCompatible).IsNatural
      (orbitJacquetData h hclosed hU hP hPc T cs I B w m K hK hS1 hS2 hr hD07 μN μI ν
        hCompatible) φ :=
  fun s hKs hs ψ ψ' hψ =>
    orbitJacquetMap_natural (h I) (h (Finset.univ \ s)).le_normalizer (hU hKs) m A
      ((h K).unipotent_le.trans (hP hKs)) (hS1 s hKs hs)
      (fun x hx => hP hKs ((h K).levi_le ((hK x).mp hx))) hr ν φ ψ ψ' hψ

omit [LinearOrder ι] [Fintype ι] [T2Space G] in
include h hclosed hPc in
/-- Under the compact-limit hypothesis on `U_I ∩ P_I`, every element of `U_I` lies in a
compact open subgroup of `U_I`. -/
theorem exists_compactOpen_unipotent_of_isLimitOfCompactSubgroups
    (hNc : Jacquet.Localization.IsLimitOfCompactSubgroups ((U I).subgroupOf (P I)))
    (u : U I) :
    ∃ C : OpenSubgroup (U I), IsCompact (C : Set (U I)) ∧ u ∈ C := by
  let V := (U I).subgroupOf (P I)
  have : NonarchimedeanGroup V :=
    nonarchimedeanGroup_of_isInducing ((P I).subtype.comp V.subtype)
      (Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal)
  have : LocallyCompactSpace (P I) := (hPc I).locallyCompactSpace
  have hVc : IsClosed (V : Set (P I)) := (hclosed I).preimage continuous_subtype_val
  have : LocallyCompactSpace V := hVc.locallyCompactSpace
  let e := subgroupOfEquiv (h I).unipotent_le
  obtain ⟨C, hC, hu⟩ := exists_compactOpen_mem_of_isLimitOfCompactSubgroups V hNc (e.symm u)
  exact ⟨OpenSubgroup.comap e.symm.toMonoidHom e.symm.continuous C,
    e.symm.toHomeomorph.isClosedEmbedding.isCompact_preimage hC, hu⟩

/-- The natural family of orbit Jacquet data under the compact-limit hypothesis on
`U_I ∩ P_I`: for every `E`, the data `orbitJacquetData` built from Haar measures on the
kernel of the Levi projection and on `U_I ∩ m U_K m⁻¹` and from one chosen compatible
quotient measure. None of these choices depends on `E`. -/
def naturalOrbitJacquetData
    (hS1 : ∀ s, K ⊆ Finset.univ \ s →
      Group.RelativeWeylIndexing.IsMinimal cs (Finset.univ \ s) I w →
      ∀ x ∈ U I, m⁻¹ * x * m ∈ P (Finset.univ \ s) → m⁻¹ * x * m ∈ U K)
    (hS2 : ∀ s, K ⊆ Finset.univ \ s →
      Group.RelativeWeylIndexing.IsMinimal cs (Finset.univ \ s) I w →
      ∀ x ∈ M (Finset.univ \ s), x ∈ U K → m * x * m⁻¹ ∈ U I)
    (hr : Continuous (h I).projection)
    (hD07 : ∀ l : M I,
      (HaarModulus.closedRestrictCharacter (U I) (hclosed I) (M I) (h I).levi_le_normalizer l :
          ℝ≥0) *
          (HaarModulus.closedRestrictCharacter (U K) (hclosed K) (M K) (h K).levi_le_normalizer
            (conjugationEquiv m hK l) : ℝ≥0) =
        (HaarModulus.closedRestrictCharacter (orbitUnipotentIntersection (U I) (U K) m)
            (isClosed_orbitUnipotentIntersection (hclosed I) (hclosed K) m) (M I)
            (levi_le_normalizer_orbitUnipotentIntersection (h I) (h K) m hK) l : ℝ≥0) ^ 2)
    (hNc : Jacquet.Localization.IsLimitOfCompactSubgroups ((U I).subgroupOf (P I)))
    (E : SmoothRep.{0, uG, max uG uV} ℂ G) :
    OrbitJacquetData P M U h hclosed hU T cs I E w m K hK := by
  let N := (h I).projection.ker
  let I₀ := orbitKernelIntersection (h I) (U K) m
  let : MeasurableSpace N := borel N
  have : BorelSpace N := ⟨rfl⟩
  let : MeasurableSpace I₀ := borel I₀
  have : BorelSpace I₀ := ⟨rfl⟩
  let : MeasurableSpace (LeftQuotient I₀) := borel (LeftQuotient I₀)
  have : BorelSpace (LeftQuotient I₀) := ⟨rfl⟩
  have : LocallyCompactSpace (P I) := (hPc I).locallyCompactSpace
  have : LocallyCompactSpace N := (isClosed_projection_ker (h I) (hclosed I)).locallyCompactSpace
  have hI₀ := isClosed_orbitKernelIntersection (h I) (U K) (hclosed K) m
  have : LocallyCompactSpace I₀ := hI₀.locallyCompactSpace
  let e := projectionKerEquiv (h I)
  have hcoverN : ∀ x : N, ∃ C : OpenSubgroup N, IsCompact (C : Set N) ∧ x ∈ C := by
    intro x
    obtain ⟨C, hC, hx⟩ :=
      exists_compactOpen_unipotent_of_isLimitOfCompactSubgroups h hclosed hPc I hNc (e x)
    exact ⟨OpenSubgroup.comap e.toMonoidHom e.continuous C,
      e.toHomeomorph.isClosedEmbedding.isCompact_preimage hC, hx⟩
  have hu := Haar.compactOpenCoverUnimodularity hcoverN
  let μN : Measure N := haar
  let μI : Measure I₀ := haar
  have : IsMulRightInvariant μN := hu.1 μN
  have : IsMulRightInvariant μI := hu.2 I₀ hI₀ μI
  have hν := Classical.choose_spec (compatibleMeasureExists I₀ hI₀ μN μI)
  have : (Classical.choose (compatibleMeasureExists I₀ hI₀ μN μI)).Regular := hν.regular
  exact orbitJacquetData h hclosed hU hP hPc T cs I E w m K hK hS1 hS2 hr hD07 μN μI
    (Classical.choose (compatibleMeasureExists I₀ hI₀ μN μI)) hν

/-- The family `naturalOrbitJacquetData` is natural along every morphism `φ : A ⟶ B`. -/
theorem naturalOrbitJacquetData_isNatural
    (hS1 : ∀ s, K ⊆ Finset.univ \ s →
      Group.RelativeWeylIndexing.IsMinimal cs (Finset.univ \ s) I w →
      ∀ x ∈ U I, m⁻¹ * x * m ∈ P (Finset.univ \ s) → m⁻¹ * x * m ∈ U K)
    (hS2 : ∀ s, K ⊆ Finset.univ \ s →
      Group.RelativeWeylIndexing.IsMinimal cs (Finset.univ \ s) I w →
      ∀ x ∈ M (Finset.univ \ s), x ∈ U K → m * x * m⁻¹ ∈ U I)
    (hr : Continuous (h I).projection)
    (hD07 : ∀ l : M I,
      (HaarModulus.closedRestrictCharacter (U I) (hclosed I) (M I) (h I).levi_le_normalizer l :
          ℝ≥0) *
          (HaarModulus.closedRestrictCharacter (U K) (hclosed K) (M K) (h K).levi_le_normalizer
            (conjugationEquiv m hK l) : ℝ≥0) =
        (HaarModulus.closedRestrictCharacter (orbitUnipotentIntersection (U I) (U K) m)
            (isClosed_orbitUnipotentIntersection (hclosed I) (hclosed K) m) (M I)
            (levi_le_normalizer_orbitUnipotentIntersection (h I) (h K) m hK) l : ℝ≥0) ^ 2)
    (hNc : Jacquet.Localization.IsLimitOfCompactSubgroups ((U I).subgroupOf (P I)))
    {A B : SmoothRep.{0, uG, max uG uV} ℂ G} (φ : A ⟶ B) :
    (naturalOrbitJacquetData h hclosed hU hP hPc T cs I w m K hK hS1 hS2 hr hD07 hNc
        A).IsNatural
      (naturalOrbitJacquetData h hclosed hU hP hPc T cs I w m K hK hS1 hS2 hr hD07 hNc B) φ := by
  let N := (h I).projection.ker
  let I₀ := orbitKernelIntersection (h I) (U K) m
  let : MeasurableSpace N := borel N
  have : BorelSpace N := ⟨rfl⟩
  let : MeasurableSpace I₀ := borel I₀
  have : BorelSpace I₀ := ⟨rfl⟩
  let : MeasurableSpace (LeftQuotient I₀) := borel (LeftQuotient I₀)
  have : BorelSpace (LeftQuotient I₀) := ⟨rfl⟩
  have : LocallyCompactSpace (P I) := (hPc I).locallyCompactSpace
  have : LocallyCompactSpace N := (isClosed_projection_ker (h I) (hclosed I)).locallyCompactSpace
  have hI₀ := isClosed_orbitKernelIntersection (h I) (U K) (hclosed K) m
  have : LocallyCompactSpace I₀ := hI₀.locallyCompactSpace
  let e := projectionKerEquiv (h I)
  have hcoverN : ∀ x : N, ∃ C : OpenSubgroup N, IsCompact (C : Set N) ∧ x ∈ C := by
    intro x
    obtain ⟨C, hC, hx⟩ :=
      exists_compactOpen_unipotent_of_isLimitOfCompactSubgroups h hclosed hPc I hNc (e x)
    exact ⟨OpenSubgroup.comap e.toMonoidHom e.continuous C,
      e.toHomeomorph.isClosedEmbedding.isCompact_preimage hC, hx⟩
  have hu := Haar.compactOpenCoverUnimodularity hcoverN
  let μN : Measure N := haar
  let μI : Measure I₀ := haar
  have : IsMulRightInvariant μN := hu.1 μN
  have : IsMulRightInvariant μI := hu.2 I₀ hI₀ μI
  have hν := Classical.choose_spec (compatibleMeasureExists I₀ hI₀ μN μI)
  have : (Classical.choose (compatibleMeasureExists I₀ hI₀ μN μI)).Regular := hν.regular
  exact orbitJacquetData_isNatural h hclosed hU hP hPc T cs I w m K hK hS1 hS2 hr hD07 μN μI
    (Classical.choose (compatibleMeasureExists I₀ hI₀ μN μI)) hν φ

end Natural

end Langlands.Aubert.General.CorrectedFiltration
