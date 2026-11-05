import Langlands.Representation.Aubert.General.RationalOppositeIwahoriBasisProof
import Langlands.GroupScheme.Rational.NormKernelCocharacter
import Langlands.BruhatTits.Unipotent.CocharacterEscape
import Langlands.Representation.CompactCoefficient.IwahoriContractionConverse

/-! # Escaping opposite Iwahori bases in the actual rational norm kernel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology Filter
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology
open BruhatTits.DynamicUnipotentContainment

set_option backward.isDefEq.respectTransparency false

section Data

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of F))}
    (i : T.toGrp ⟶ G) (ν : cocharacterLattice T) (I : Finset (SimpleRoot i ν))

local instance : TopologicalSpace (RationalPoint F G.X) := pointTopology

/-- A specified standard cocharacter and an actual norm-kernel element with
opposite ambient Iwahori bases and escaping powers in the kernel topology. -/
structure NormKernelEscapingOppositeIwahoriData where
  cocharacter : cocharacterLattice T
  element : Plancherel.rationalCommonNormKernel G
  standard : IsStandardCocharacter i ν (rootSet i ν I) cocharacter
  commute : ∀ m ∈ levi i ν I, m * element.val = element.val * m
  basis : Jacquet.HasOppositeIwahoriContractionBasis
    (unipotent i ν I) (levi i ν I) (oppositeUnipotent i cocharacter) element.val
  escapes : CompactCoefficient.EscapesCompactSets (fun r : ℕ => element ^ r)

end Data

/-- The opposite Iwahori basis can use the specified cocharacter value itself. -/
theorem oppositeIwahoriBasis_of_cocharPoint
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
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
      (_hStandard : StandardCocharacterStatement.{u})
      (I : Finset (SimpleRoot i ν))
      (_hU : IsClosed (unipotent i ν I : Set (RationalPoint F G.X)))
      (ζ : cocharacterLattice T) (_hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ)
      (t : Fˣ) (_ht : Tendsto (fun n : ℕ => (t : F) ^ n) atTop (𝓝 0)),
      (∀ m ∈ levi i ν I,
        m * cocharPoint (CommGroupScheme.groupHom ζ ≫ i) t =
          cocharPoint (CommGroupScheme.groupHom ζ ≫ i) t * m) ∧
      Jacquet.HasOppositeIwahoriContractionBasis
        (unipotent i ν I) (levi i ν I) (oppositeUnipotent i ζ)
        (cocharPoint (CommGroupScheme.groupHom ζ ≫ i) t) := by
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  let : TopologicalSpace (RationalPoint F G.X) := pointTopology
  intro _ _ _ ν hν hStandard I hU ζ hζ t ht
  have := hG.smooth
  have := hG.isSeparated
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : T2Space F := Langlands.BruhatTits.localField_t2Space F
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
  have hgM := cocharPoint_mem_centralizer χ t
  have hcomm : ∀ m ∈ (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)),
      m * cocharPoint χ t = cocharPoint χ t * m :=
    fun m hm => (commute_cocharPoint χ hm t).eq
  constructor
  · rw [hM]
    exact hcomm
  rw [hM, hUeq, hOeq]
  have htop : (pointTopology : TopologicalSpace (RationalPoint F G.X)) =
      rationalSchemeTopology F G.X :=
    rationalPointTopology_eq_rationalSchemeTopology F G.X
  refine Jacquet.hasOppositeIwahoriContractionBasis_of_contraction hOc hU hgM hcomm ?_ ?_
    (dynamic_opposite_factorization_unique χ) ?_ ?_ ?_
  · rw [← Dynamic.centralizer_inverseCocharacter χ]
    exact Dynamic.centralizer_le_normalizer_unipotent _ _
  · exact Dynamic.centralizer_le_normalizer_unipotent _ _
  · rw [htop]
    exact Dynamic.opposite_cell_mem_nhds_one F G χ
  · exact eventually_cocharPoint_pow_conj_mem_ambient χ t ht
  · intro C hC hCO W hW
    have h := eventually_cocharPoint_pow_conj_mem_ambient (Dynamic.inverseCocharacter χ)
      t ht C hC hCO W hW
    simpa only [cocharPoint_inverseCocharacter, inv_pow, inv_inv] using h

/-- For a proper actual standard root subset, one corrected standard cocharacter
gives an opposite Iwahori basis and powers escaping in the actual norm kernel. -/
theorem exists_normKernel_escaping_oppositeIwahoriBasis
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
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
      (_hStandard : StandardCocharacterStatement.{u}) (_hRoots : HasRelativeRootSystem i)
      (I : Finset (SimpleRoot i ν))
      (_hU : IsClosed (unipotent i ν I : Set (RationalPoint F G.X)))
      (_hproper : ∃ α ∈ simpleRelativeRoots i ν, α ∉ rootSet i ν I),
      ∃ (ζ : cocharacterLattice T) (g : Plancherel.rationalCommonNormKernel G),
        IsStandardCocharacter i ν (rootSet i ν I) ζ ∧
        (∀ m ∈ levi i ν I, m * g.val = g.val * m) ∧
        Jacquet.HasOppositeIwahoriContractionBasis
          (unipotent i ν I) (levi i ν I) (oppositeUnipotent i ζ) g.val ∧
        CompactCoefficient.EscapesCompactSets (fun r : ℕ => g ^ r) := by
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  let : TopologicalSpace (RationalPoint F G.X) := pointTopology
  intro _ _ _ ν hν hStandard hRoots I hU hproper
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsClosedImmersion i.hom.hom.left := hi.isSplitSubtorus.2
  have : IsAffine T.X.left := isAffine_of_isAffineHom i.hom.hom.left
  have : T2Space F := Langlands.BruhatTits.localField_t2Space F
  let := relativeWeylGroupFintype i hRoots
  obtain ⟨ζ, hζ⟩ := (hStandard F G hG T i hi ν hν
    (rootSet i ν I) (rootSet_subset i ν I)).1
  let ζ' := normKernelCocharacter i ζ
  have hζ' : IsStandardCocharacter i ν (rootSet i ν I) ζ' :=
    hζ.normKernelCocharacter i hi.isSplitSubtorus.1
      (fun _ hα => hRoots.exists_isRelativeReflection hα)
  obtain ⟨α, hα, hαI⟩ := hproper
  obtain ⟨t, ht⟩ := exists_unit_tendsto_pow_zero (F := F)
  let g0 := cocharPoint (CommGroupScheme.groupHom ζ' ≫ i) t
  have hgH : g0 ∈ Plancherel.rationalCommonNormKernel G := by
    dsimp only [g0]
    rw [cocharPoint_comp_eq_map_cocharacterPoints]
    exact normKernelCocharacter_mem_rationalCommonNormKernel i ζ t
  let g : Plancherel.rationalCommonNormKernel G := ⟨g0, hgH⟩
  obtain ⟨hcomm, hbasis⟩ := oppositeIwahoriBasis_of_cocharPoint
    F G hG T i hi ν hν hStandard I hU ζ' hζ' t ht
  refine ⟨ζ', g, hζ', hcomm, hbasis, ?_⟩
  apply CompactCoefficient.EscapesCompactSets.of_continuous
    (f := (Subtype.val : Plancherel.rationalCommonNormKernel G → RationalPoint F G.X))
    (hf := continuous_subtype_val)
  intro C hC
  exact eventually_cocharPoint_pow_notMem i ζ' t ht α (hζ'.2.2 α hα hαI) C hC

/-- Package the constructed witnesses as reusable actual norm-kernel data. -/
theorem nonempty_normKernelEscapingOppositeIwahoriData
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
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
      (_hStandard : StandardCocharacterStatement.{u}) (_hRoots : HasRelativeRootSystem i)
      (I : Finset (SimpleRoot i ν))
      (_hU : IsClosed (unipotent i ν I : Set (RationalPoint F G.X)))
      (_hproper : ∃ α ∈ simpleRelativeRoots i ν, α ∉ rootSet i ν I),
      Nonempty (NormKernelEscapingOppositeIwahoriData i ν I) := by
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  let : TopologicalSpace (RationalPoint F G.X) := pointTopology
  intro _ _ _ ν hν hStandard hRoots I hU hproper
  obtain ⟨ζ, g, hζ, hcomm, hbasis, hescape⟩ :=
    exists_normKernel_escaping_oppositeIwahoriBasis
      F G hG T i hi ν hν hStandard hRoots I hU hproper
  exact ⟨⟨ζ, g, hζ, hcomm, hbasis, hescape⟩⟩

end Langlands.Aubert.General.RationalPointFamily
