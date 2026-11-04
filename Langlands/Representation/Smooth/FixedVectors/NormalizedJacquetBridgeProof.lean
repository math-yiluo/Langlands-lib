import Langlands.Representation.Smooth.FixedVectors.NormalizedJacquetBridgeStatement
import Langlands.Representation.Smooth.FixedVectors.CompactRestrictionDetectionProof
import Langlands.Representation.Jacquet.FixedVectorsGenerationProof
import Langlands.Representation.Jacquet.ExactProof
import Langlands.Representation.Jacquet.IwahoriContractionAdmissibility
import Langlands.Representation.Filtration.SubquotientAlgebraProof
import Langlands.Representation.Compact.SurjectivityProof
import Langlands.Representation.Smooth.FixedVectors.LawsProof
import Langlands.Representation.Twist.SubquotientDefinitions
import Langlands.Representation.Twist.AdmissibilityProof
import Langlands.Group.PositiveCharacterExtension

/-! # Fixed-vector detection for the actual normalized Jacquet functor -/

set_option autoImplicit false

noncomputable section

namespace Langlands

universe uG uV uI

namespace NormalizedJacquetBridge

/-- Generation by fixed vectors is transported by an actual equivariant equivalence. -/
theorem generation_of_equiv
    {G : Type uG} [Group G] {V W : Type uV}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (e : ρ.Equiv σ) (K : Subgroup G)
    (hgen : ∀ S : Subrepresentation ρ, fixedVectors ρ K ≤ S.toSubmodule → S = ⊤) :
    ∀ S : Subrepresentation σ, fixedVectors σ K ≤ S.toSubmodule → S = ⊤ := by
  intro S hS
  let C : Subrepresentation ρ :=
    { toSubmodule := S.toSubmodule.comap e.toLinearEquiv.toLinearMap
      apply_mem_toSubmodule := by
        intro g v hv
        change e.toIntertwiningMap (ρ g v) ∈ S
        rw [Representation.IntertwiningMap.isIntertwining ρ σ e.toIntertwiningMap g v]
        exact S.apply_mem_toSubmodule g hv }
  have hC : C = ⊤ := hgen C (fun v hv => hS (map_mem_fixedVectors e.toIntertwiningMap hv))
  apply top_unique
  intro w _
  obtain ⟨v, rfl⟩ := e.surjective w
  have hv : v ∈ C := by rw [hC]; trivial
  exact hv

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- Compact-open exactness transfers finite fixed dimension to an actual subquotient. -/
theorem finite_fixed_subquotient [IsTopologicalGroup G]
    {A D : SmoothRep.{0, uG, uV} ℂ G} (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (hDA : SmoothRep.IsSubquotient D A)
    (hA : FiniteDimensional ℂ (fixedVectors A.representation K.toSubgroup)) :
    FiniteDimensional ℂ (fixedVectors D.representation K.toSubgroup) := by
  obtain ⟨C, i, q, hi, hq⟩ := SmoothRep.isSubquotient_iff_exists.mp hDA
  let iK := Compact.fixedVectorMap C.representation A.representation (SmoothRep.hom i) K.toSubgroup
  have hiK : Function.Injective iK := fun x y hxy =>
    Subtype.ext (hi (congrArg Subtype.val hxy))
  let := hA
  let : FiniteDimensional ℂ (fixedVectors C.representation K.toSubgroup) :=
    Module.Finite.of_injective iK hiK
  exact Module.Finite.of_surjective
    (Compact.fixedVectorMap C.representation D.representation (SmoothRep.hom q) K.toSubgroup)
    (Compact.fixedVectorSurjectivity G C D C.representation D.representation
      C.isSmooth D.isSmooth K hK (SmoothRep.hom q) hq)

/-- Compact-open exactness lifts nonvanishing from a genuine subquotient. -/
theorem nonzero_fixed_subquotient [IsTopologicalGroup G]
    {A D : SmoothRep.{0, uG, uV} ℂ G} (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (hDA : SmoothRep.IsSubquotient D A)
    (hD : ∃ v : D, v ∈ fixedVectors D.representation K.toSubgroup ∧ v ≠ 0) :
    ∃ v : A, v ∈ fixedVectors A.representation K.toSubgroup ∧ v ≠ 0 := by
  obtain ⟨w, hw, hw0⟩ := hD
  obtain ⟨C, i, q, hi, hq⟩ := SmoothRep.isSubquotient_iff_exists.mp hDA
  obtain ⟨v, hv⟩ := Compact.fixedVectorSurjectivity G C D
    C.representation D.representation C.isSmooth D.isSmooth K hK (SmoothRep.hom q) hq ⟨w, hw⟩
  refine ⟨SmoothRep.hom i v.val,
    map_mem_fixedVectors (SmoothRep.hom i) v.property, ?_⟩
  intro hz
  have hv0 : v.val = 0 := hi (hz.trans (map_zero (SmoothRep.hom i)).symm)
  have hqw : SmoothRep.hom q v.val = w := congrArg Subtype.val hv
  apply hw0
  exact hqw.symm.trans (by rw [hv0, map_zero])

variable [LocallyCompactSpace G] [NonarchimedeanGroup G]

/-- The intrinsic normalizing character kills the compact intersection with a closed Levi. -/
theorem character_trivial (N M : Subgroup G) (hN : IsClosed (N : Set G))
    (hMN : M ≤ Subgroup.normalizer N) (hM : IsClosed (M : Set G))
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) :
    K.toSubgroup.comap M.subtype ≤
      (HaarModulus.closedInverseHalfCharacter N hN M hMN).ker := by
  let KM : OpenSubgroup M := K.comap M.subtype continuous_subtype_val
  have hKM : IsCompact (KM : Set M) :=
    hM.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  intro m hm
  change Jacquet.inverseHalfCharacter (HaarModulus.closedRestrictCharacter N hN M hMN) m = 1
  apply (Jacquet.inverseHalfCharacter_eq_one _ _).mpr
  exact PositiveCharacter.eq_one_on_compact
    (HaarModulus.closedRestrictCharacter N hN M hMN)
    (HaarModulus.isOpen_ker_closedRestrictCharacter N hN M hMN)
    KM.toSubgroup hKM ⟨m, hm⟩

/-- The actual normalized map has the same underlying localization map, and the
trivial-character comparison identifies it with the older coinvariant map. -/
theorem comparison_natural (N M : Subgroup G) (hN : IsClosed (N : Set G))
    (hMN : M ≤ Subgroup.normalizer N)
    {A B : SmoothRep.{0, uG, uV} ℂ G} (f : A ⟶ B)
    (x : (Aubert.General.normalizedJacquetFunctor N M hN hMN).obj A) :
    Jacquet.map N M hMN (SmoothRep.hom f)
        (Jacquet.Localization.trivialEquiv A.representation N M hMN x) =
      Jacquet.Localization.trivialEquiv B.representation N M hMN
        (SmoothRep.hom ((Aubert.General.normalizedJacquetFunctor N M hN hMN).map f) x) := by
  exact congrArg (fun t => t x)
    (Jacquet.Localization.trivialEquiv_natural N M hMN (SmoothRep.hom f))

/-- Exact coinvariants and the actual functor maps preserve a genuine subquotient presentation. -/
theorem normalized_isSubquotient (N M : Subgroup G) (hN : IsClosed (N : Set G))
    (hMN : M ≤ Subgroup.normalizer N)
    (hcompact : ∀ s : Finset N, ∃ L : OpenSubgroup N,
      IsCompact (L : Set N) ∧ ∀ n ∈ s, n ∈ L)
    {A D : SmoothRep.{0, uG, uV} ℂ G} (hDA : SmoothRep.IsSubquotient D A) :
    SmoothRep.IsSubquotient
      ((Aubert.General.normalizedJacquetFunctor N M hN hMN).obj D)
      ((Aubert.General.normalizedJacquetFunctor N M hN hMN).obj A) := by
  obtain ⟨C, i, q, hi, hq⟩ := SmoothRep.isSubquotient_iff_exists.mp hDA
  let F := Aubert.General.normalizedJacquetFunctor N M hN hMN
  refine SmoothRep.isSubquotient_iff_exists.mpr ⟨F.obj C, F.map i, F.map q, ?_, ?_⟩
  · have hiOld : Function.Injective (Jacquet.map N M hMN (SmoothRep.hom i)) :=
      coinvariants_map_injective_of_smooth hcompact (Jacquet.restrictMap (SmoothRep.hom i) N)
        hi (isSmooth_comp N.subtype continuous_subtype_val A.isSmooth)
    intro x y hxy
    apply (Jacquet.Localization.trivialEquiv C.representation N M hMN).injective
    apply hiOld
    exact (comparison_natural N M hN hMN i x).trans
      ((congrArg (Jacquet.Localization.trivialEquiv A.representation N M hMN) hxy).trans
        (comparison_natural N M hN hMN i y).symm)
  · have hqOld : Function.Surjective (Jacquet.map N M hMN (SmoothRep.hom q)) :=
      coinvariants_map_surjective (Jacquet.restrictMap (SmoothRep.hom q) N) hq
    intro w
    obtain ⟨v, hv⟩ := hqOld (Jacquet.Localization.trivialEquiv D.representation N M hMN w)
    obtain ⟨z, hz⟩ := (Jacquet.Localization.trivialEquiv C.representation N M hMN).surjective v
    refine ⟨z, ?_⟩
    apply (Jacquet.Localization.trivialEquiv D.representation N M hMN).injective
    exact (comparison_natural N M hN hMN q z).symm.trans
      ((congrArg (Jacquet.map N M hMN (SmoothRep.hom q)) hz).trans hv)

end NormalizedJacquetBridge

/-- The fixed-vector generation, subquotient and nonvanishing bridge for the
actual intrinsic Haar-normalized Jacquet functor. -/
theorem normalizedJacquetFixedVectorBridge :
    NormalizedJacquetFixedVectorBridgeStatement.{uG, uV} := by
  intro G _ _ _ _ N M Nbar hN hMN hM hcompact K K₀ hK hK₀ hfactor
    g hcon A D hfin hgen hDA
  let χ := HaarModulus.closedInverseHalfCharacter N hN M hMN
  let F := Aubert.General.normalizedJacquetFunctor N M hN hMN
  let JA := F.obj A
  let JD := F.obj D
  let ρA := Jacquet.Localization.action A.representation N 1 M hMN
    (Jacquet.Localization.isInvariant_one N M hMN)
  let ρD := Jacquet.Localization.action D.representation N 1 M hMN
    (Jacquet.Localization.isInvariant_one N M hMN)
  let KM := K.toSubgroup.comap M.subtype
  have hχ : KM ≤ χ.ker := NormalizedJacquetBridge.character_trivial N M hN hMN hM K hK
  dsimp only
  refine ⟨hχ, ?_, NormalizedJacquetBridge.normalized_isSubquotient N M hN hMN hcompact hDA, ?_⟩
  · have hgenOld := Jacquet.fixedVectors_generate_of_factorization
      A.representation N M K.toSubgroup K₀ hMN hK₀ hfactor hgen
    have hgenLoc : ∀ S : Subrepresentation ρA,
        fixedVectors ρA KM ≤ S.toSubmodule → S = ⊤ :=
      NormalizedJacquetBridge.generation_of_equiv
        (Jacquet.Localization.trivialEquiv A.representation N M hMN).symm KM hgenOld
    intro S hS
    let T : Subrepresentation ρA := untwistSubrepresentation χ S
    have hT : T = ⊤ := by
      apply hgenLoc T
      intro v hv
      apply hS
      change v ∈ fixedVectors (twist χ ρA) KM
      rwa [fixedVectors_twist_eq_of_le_ker χ ρA KM hχ]
    apply Subrepresentation.toSubmodule_injective
    have hTsub : T.toSubmodule = (⊤ : Subrepresentation ρA).toSubmodule :=
      congrArg Subrepresentation.toSubmodule hT
    exact hTsub
  · rintro ⟨w, hw, hw0⟩
    have hwLoc : w ∈ fixedVectors ρD KM := by
      change w ∈ fixedVectors (twist χ ρD) KM at hw
      rwa [fixedVectors_twist_eq_of_le_ker χ ρD KM hχ] at hw
    let e := Jacquet.Localization.trivialEquiv D.representation N M hMN
    have hew : e w ∈ fixedVectors (Jacquet.action D.representation N M hMN) KM :=
      map_mem_fixedVectors e.toIntertwiningMap hwLoc
    have hew0 : e w ≠ 0 := fun hz => hw0 (e.injective (hz.trans (map_zero e).symm))
    have hDfin := NormalizedJacquetBridge.finite_fixed_subquotient K hK hDA hfin
    obtain ⟨d, hd⟩ := Jacquet.fixedJacquetMap_surjective_of_iwahoriContraction
      D.representation D.isSmooth hK hcon hMN hDfin ⟨e w, hew⟩
    refine ⟨d.val, d.property, ?_⟩
    intro hz
    apply hew0
    have hdw : Jacquet.mk D.representation N d.val = e w := congrArg Subtype.val hd
    exact hdw.symm.trans (by rw [hz, map_zero])

/-- A finite compact restriction detects vectors directly in an actual
normalized Jacquet subquotient, without changing its normalization. -/
theorem normalizedJacquetSubquotientFixedVectorDetection
    (G : Type uG) [Group G] [TopologicalSpace G]
    [LocallyCompactSpace G] [NonarchimedeanGroup G]
    (N M Nbar : Subgroup G) (hN : IsClosed (N : Set G))
    (hMN : M ≤ Subgroup.normalizer N) (hM : IsClosed (M : Set G))
    (hcompact : ∀ s : Finset N, ∃ L : OpenSubgroup N,
      IsCompact (L : Set N) ∧ ∀ n ∈ s, n ∈ L)
    (K : OpenSubgroup G) (K₀ : Subgroup G) (hK : IsCompact (K : Set G))
    (hK₀ : K₀ ≤ Subgroup.normalizer K.toSubgroup)
    (hfactor : ∀ x : G, ∃ m ∈ M, ∃ n ∈ N, ∃ k ∈ K₀, x = m * n * k)
    (g : G) (hcon : Jacquet.IsIwahoriContraction K N M Nbar g)
    (H : Subgroup M) [H.Normal]
    [T2Space H] [LocallyCompactSpace H] [TotallyDisconnectedSpace H]
    [MeasurableSpace H] [BorelSpace H]
    (μ : MeasureTheory.Measure H) [μ.IsHaarMeasure]
    (hKH : K.toSubgroup.comap M.subtype ≤ H)
    (A D : SmoothRep.{0, uG, uV} ℂ G)
    (hfin : FiniteDimensional ℂ (fixedVectors A.representation K.toSubgroup))
    (hgen : ∀ S : Subrepresentation A.representation,
      fixedVectors A.representation K.toSubgroup ≤ S.toSubmodule → S = ⊤)
    (hDA : SmoothRep.IsSubquotient D A)
    (E : SmoothRep.{0, uG, uV} ℂ M)
    (ι : Type uI) [Fintype ι] [Nonempty ι]
    (V : ι → Subrepresentation (SmoothRep.restrictSubgroup H E).representation)
    (hVirr : ∀ i, Representation.IsIrreducible (V i).toRepresentation)
    (hVcomp : ∀ i, HasCompactSmoothDualCoefficients (V i).toRepresentation)
    (hspan : (⨆ i, (V i).toSubmodule) = ⊤)
    (hE : SmoothRep.IsSubquotient E
      ((Aubert.General.normalizedJacquetFunctor N M hN hMN).obj D)) :
    ∃ v : D, v ∈ fixedVectors D.representation K.toSubgroup ∧ v ≠ 0 := by
  let F := Aubert.General.normalizedJacquetFunctor N M hN hMN
  let JA := F.obj A
  let JD := F.obj D
  obtain ⟨_, hgenJA, hJDA, hlift⟩ := normalizedJacquetFixedVectorBridge G N M Nbar hN hMN
    hM hcompact K K₀ hK hK₀ hfactor g hcon A D hfin hgen hDA
  have hEJA : SmoothRep.IsSubquotient E JA :=
    smoothSubquotientTransitivity ℂ M JA JD E hE hJDA
  have he := compactRestrictionFixedVectorDetection M H μ JA E
    (K.toSubgroup.comap M.subtype) hKH hgenJA ι V hVirr hVcomp hspan hEJA
  let KM : OpenSubgroup M := K.comap M.subtype continuous_subtype_val
  have hKM : IsCompact (KM : Set M) :=
    hM.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  exact hlift (NormalizedJacquetBridge.nonzero_fixed_subquotient KM hKM hE he)

end Langlands
