import Langlands.Representation.Aubert.General.RationalCompactRestrictionCuspidalStatement
import Langlands.Representation.Aubert.General.RationalOppositeIwahoriBasisProof
import Langlands.Representation.CompactCoefficient.IwahoriConverse
import Langlands.GroupScheme.Rational.NormKernelContractingPoint

/-! # Compact norm-kernel restriction and proper standard Jacquet vanishing -/

noncomputable section

universe uF uV

open CategoryTheory AlgebraicGeometry Topology Filter
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

/-- Every contracting field unit, evaluated at a standard cocharacter, gives
an ambient-cofinal opposite Iwahori basis for that same evaluated point. -/
theorem rational_cocharPoint_hasOppositeIwahoriBasis
    (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) :
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    letI : TopologicalSpace (RationalPoint F G.X) := pointTopology
    ∀ [LocallyCompactSpace (RationalPoint F G.X)]
      [NonarchimedeanGroup (RationalPoint F G.X)] [T2Space (RationalPoint F G.X)]
      (ν : cocharacterLattice T) (_hν : IsGenericCocharacter i ν)
      (_hStandard : StandardCocharacterStatement.{uF})
      (I : Finset (SimpleRoot i ν))
      (_hU : IsClosed (unipotent i ν I : Set (RationalPoint F G.X)))
      (ζ : cocharacterLattice T)
      (_hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ)
      (t : Fˣ) (_ht : Tendsto (fun n : ℕ => (t : F) ^ n) atTop (𝓝 0)),
      Jacquet.HasOppositeIwahoriContractionBasis
        (unipotent i ν I) (levi i ν I) (oppositeUnipotent i ζ)
        (BruhatTits.DynamicUnipotentContainment.cocharPoint
          (CommGroupScheme.groupHom ζ ≫ i) t) := by
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  let : TopologicalSpace (RationalPoint F G.X) := pointTopology
  intro _ _ _ ν hν hStandard I hU ζ hζ t ht
  have := hG.smooth
  have := hG.isSeparated
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : T2Space F := BruhatTits.localField_t2Space F
  let χ := CommGroupScheme.groupHom ζ ≫ i
  have hStd := (hStandard F G hG T i hi ν hν
    (rootSet i ν I) (rootSet_subset i ν I)).2 ζ hζ
  have hM : levi i ν I = (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)) := by
    change (standardLevi i ν (rootSet i ν I)).carrier (Over.mk (𝟙 _)) = _
    rw [hStd.2.1]
  have hUeq : unipotent i ν I = (Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)) := by
    change (standardUnipotent i ν (rootSet i ν I)).carrier (Over.mk (𝟙 _)) = _
    rw [hStd.2.2]
  have hOeq : oppositeUnipotent i ζ =
      (Dynamic.unipotent (Dynamic.inverseCocharacter χ)).carrier (Over.mk (𝟙 _)) := rfl
  have hOc := isClosed_oppositeUnipotent_localField i ζ
  rw [hOeq] at hOc
  rw [hUeq] at hU
  rw [hM, hUeq, hOeq]
  have htop : (pointTopology : TopologicalSpace (RationalPoint F G.X)) =
      rationalSchemeTopology F G.X :=
    rationalPointTopology_eq_rationalSchemeTopology F G.X
  apply Jacquet.hasOppositeIwahoriContractionBasis_of_contraction hOc hU
    (BruhatTits.DynamicUnipotentContainment.cocharPoint_mem_centralizer χ t)
    (fun m hm => (BruhatTits.DynamicUnipotentContainment.commute_cocharPoint χ hm t).eq)
  · rw [← Dynamic.centralizer_inverseCocharacter χ]
    exact Dynamic.centralizer_le_normalizer_unipotent _ _
  · exact Dynamic.centralizer_le_normalizer_unipotent _ _
  · exact dynamic_opposite_factorization_unique χ
  · rw [htop]
    exact Dynamic.opposite_cell_mem_nhds_one F G χ
  · exact BruhatTits.DynamicUnipotentContainment.eventually_cocharPoint_pow_conj_mem_ambient
      χ t ht
  · intro C hC hCO W hW
    have h := BruhatTits.DynamicUnipotentContainment.eventually_cocharPoint_pow_conj_mem_ambient
      (Dynamic.inverseCocharacter χ) t ht C hC hCO W hW
    simpa only [BruhatTits.DynamicUnipotentContainment.cocharPoint_inverseCocharacter,
      inv_pow, inv_inv] using h

/-- Top actual Jacquet relations make the actual normalized Jacquet carrier
subsingleton; normalization only changes the descended action. -/
theorem normalizedJacquet_subsingleton_of_relations_eq_top
    {H : Type uF} [Group H] [TopologicalSpace H] [LocallyCompactSpace H]
    [NonarchimedeanGroup H]
    (N M : Subgroup H) (hN : IsClosed (N : Set H))
    (hMN : M ≤ Subgroup.normalizer N)
    (A : SmoothRep.{0, uF, uV} ℂ H)
    (hrel : Jacquet.relations A.representation N = ⊤) :
    Subsingleton ((normalizedJacquetFunctor N M hN hMN).obj A) := by
  change Subsingleton (Jacquet.Localization.Coinvariants A.representation N 1)
  have hloc : Jacquet.Localization.relations A.representation N 1 = ⊤ :=
    (Jacquet.Localization.relations_one A.representation N).trans hrel
  have hz (q : Jacquet.Localization.Coinvariants A.representation N 1) : q = 0 := by
    obtain ⟨v, rfl⟩ := Jacquet.Localization.mk_surjective A.representation N 1 q
    apply (Jacquet.Localization.mk_eq_zero A.representation N 1 v).mpr
    rw [hloc]
    trivial
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩

/-- Compact coefficients and an escaping element with an opposite Iwahori
basis force vanishing of the actual normalized Jacquet module. -/
theorem normalizedJacquet_subsingleton_of_compactCoefficients_of_oppositeIwahoriBasis
    {H : Type uF} [Group H] [TopologicalSpace H] [LocallyCompactSpace H]
    [NonarchimedeanGroup H]
    (C N M Nbar : Subgroup H) (hN : IsClosed (N : Set H))
    (hMN : M ≤ Subgroup.normalizer N)
    (A : SmoothRep.{0, uF, uV} ℂ H)
    (hcoeff : HasCompactSmoothDualCoefficients
      (SmoothRep.restrictSubgroup C A).representation)
    (g : H) (hg : g ∈ C)
    (hbasis : Jacquet.HasOppositeIwahoriContractionBasis N M Nbar g)
    (hescape : Jacquet.HasEscapingPowers g) :
    Subsingleton ((normalizedJacquetFunctor N M hN hMN).obj A) := by
  apply normalizedJacquet_subsingleton_of_relations_eq_top N M hN hMN A
  apply Jacquet.relations_eq_top_of_compactCoefficients_of_iwahoriBasis
    A.representation A.isSmooth C hcoeff N M Nbar hMN g hg
  · intro O hO h1
    obtain ⟨K, hK, hKO, hc, _⟩ := hbasis O hO h1
    exact ⟨K, hK, hKO, hc⟩
  · exact hescape

/-- Renard VI.2.1(c) implies (a), with the complete published general
rational-point telescope and independent field and carrier universes. -/
theorem rationalCompactRestrictionCuspidal :
    RationalCompactRestrictionCuspidalStatement.{uF, uV} := by
  classical
  intro F _ _ _ _ G hG T i hi
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hG.smooth
  have := hi.isSplitSubtorus.mono
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  intro _ _ _ ν hν hStandard hRoots hU
  let := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  let := relativeWeylGroupFintype i hRoots
  dsimp only
  intro A hcoeff I
  have hJ : rootSet i ν I.val ⊂ simpleRelativeRoots i ν := by
    refine Set.ssubset_iff_subset_ne.mpr ⟨rootSet_subset i ν I.val, ?_⟩
    intro heq
    exact I.property (rootSet_injective i ν
      (heq.trans (rootSet_univ i ν).symm))
  obtain ⟨ζ, hζ⟩ := (hStandard F G hG T i hi ν hν
    (rootSet i ν I.val) hJ.le).1
  let ζ' := normKernelCocharacter i ζ
  have hζ' : IsStandardCocharacter i ν (rootSet i ν I.val) ζ' :=
    hζ.normKernelCocharacter_of_relativeRootSystem i hi.isSplitSubtorus.1 hRoots ν
  obtain ⟨t, ht⟩ :=
    BruhatTits.DynamicUnipotentContainment.exists_unit_tendsto_pow_zero (F := F)
  apply normalizedJacquet_subsingleton_of_compactCoefficients_of_oppositeIwahoriBasis
    (Plancherel.rationalCommonNormKernel G)
    (unipotent i ν I.val) (levi i ν I.val) (oppositeUnipotent i ζ')
    (hU I.val)
    (isSemidirectDecomposition_of_standardCocharacterStatement
      i ν hStandard hG hi hν I.val).levi_le_normalizer A hcoeff
    (normKernelCocharacterPoint i ζ t) (normKernelCocharacterPoint_mem i ζ t)
  · exact rational_cocharPoint_hasOppositeIwahoriBasis
      F G hG T i hi ν hν hStandard I.val (hU I.val) ζ' hζ' t ht
  · exact eventually_normKernelCocharacterPoint_pow_not_mem_compact
      i hi.isSplitSubtorus hRoots ν hζ hJ t ht

end Langlands.Aubert.General.RationalPointFamily
