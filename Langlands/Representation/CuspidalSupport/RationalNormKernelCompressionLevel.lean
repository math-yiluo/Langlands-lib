import Langlands.Representation.CuspidalSupport.RationalNormKernelPositiveGenerators
import Langlands.Representation.CuspidalSupport.RationalNormKernelJacquetVanishing
import Langlands.Representation.Aubert.General.RationalLatticeCoefficientDecayProof
import Langlands.GroupScheme.Rational.StandardParabolicOrderFromRoots
import Langlands.GroupScheme.Rational.RootSignUnipotentInclusion
import Langlands.GroupScheme.Rational.RelativeRootStandardCocharacter
import Langlands.Representation.Hecke.IwahoriSandwich

/-! # One actual norm-kernel level for all specified positive generators -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme BruhatTits.SpecialCompact BruhatTits.DynamicUnipotentContainment
open Langlands.AlgebraicGeometry.PointTopology

variable {F : Type u} [Field F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of F))}
    {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}

/-- A standard radical is contained in the minimal standard radical. This uses
actual root signs, without a standard-parabolic order premise. -/
theorem unipotent_le_minimal_of_standard
    [LocallyOfFiniteType G.X.hom]
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hRoots : letI := hi.isSplitSubtorus.mono; HasRelativeRootSystem i) (I : Finset (SimpleRoot i ν))
    {ζ : cocharacterLattice T} (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ) :
    unipotent i ν I ≤ unipotent i ν ∅ := by
  have := hi.isSplitSubtorus.mono
  intro g hg
  apply (mem_standardUnipotent i ν).mpr
  intro eta heta
  have hle := Dynamic.unipotent_le_of_positive_rootSigns hi.isSplitSubtorus.1 i ζ eta
    (fun α hα hpos =>
      (heta.root_pairing_implications_of_subset i ν hν
        (fun _ hβ => hRoots.neg_mem_relativeRoots i hi.isSplitSubtorus.1 hβ) hζ
        (by simp) hα).2.2 hpos)
  exact hle _ (standardUnipotent_le_dynamicUnipotent i ν hζ _ hg)

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- The literal opposite standard radical inside the actual common norm kernel. -/
def normKernelStandardOpposite (I : Finset (SimpleRoot i ν)) :
    Subgroup (Plancherel.rationalCommonNormKernel G) :=
  (standardOppositeUnipotentPoints i ν (rootSet i ν I)).comap
    (Plancherel.rationalCommonNormKernel G).subtype

local instance compressionLevelPointTopology : TopologicalSpace (RationalPoint F G.X) :=
  pointTopology

variable [Fintype (SimpleRoot i ν)]

/-- A common level retains the specified generators and all positive-orthant
conjugation bounds needed by compression and residual Iwahori multiplication. -/
structure NormKernelCompressionLevel (d : NormKernelFundamentalCocharacters i ν)
    (K0 : Subgroup (RationalPoint F G.X))
    (U : OpenSubgroup (Plancherel.rationalCommonNormKernel G)) where
  level : OpenSubgroup (Plancherel.rationalCommonNormKernel G)
  compact : IsCompact (level : Set (Plancherel.rationalCommonNormKernel G))
  le_prescribed : level.toSubgroup ≤ U.toSubgroup
  normalized : K0.comap (Plancherel.rationalCommonNormKernel G).subtype ≤
    Subgroup.normalizer (level.toSubgroup : Set (Plancherel.rationalCommonNormKernel G))
  generator_contraction : ∀ α, Jacquet.IsIwahoriContraction level
    (normKernelUnipotent i ν (fundamentalRootFace i ν α))
    (normKernelLevi i ν (fundamentalRootFace i ν α))
    (normKernelStandardOpposite (fundamentalRootFace i ν α)) (d.generator α)
  upper : ∀ I n, ∀ x ∈ level.toSubgroup ⊓ normKernelUnipotent i ν I,
    d.orthantHom (.ofAdd n) * x * (d.orthantHom (.ofAdd n))⁻¹ ∈ level
  factor : ∀ k ∈ level,
    ∃ l ∈ level.toSubgroup ⊓ normKernelStandardOpposite (i := i) (ν := ν) ∅,
    ∃ m ∈ level.toSubgroup ⊓ normKernelLevi i ν ∅,
    ∃ x ∈ level.toSubgroup ⊓ normKernelUnipotent i ν ∅, k = l * m * x
  positive : ∀ n, d.orthantHom (.ofAdd n) ∈
    Hecke.iwahoriPositiveMonoid level.toSubgroup (normKernelUnipotent i ν ∅)
      (normKernelLevi i ν ∅) (normKernelStandardOpposite (i := i) (ν := ν) ∅)
  forward_levi : ∀ n, ∀ m ∈ level.toSubgroup ⊓ normKernelLevi i ν ∅,
    d.orthantHom (.ofAdd n) * m * (d.orthantHom (.ofAdd n))⁻¹ ∈ level

/-- One supplied simultaneous ambient basis gives a common compression level
below every prescribed open subgroup of the actual norm kernel. Existence of
that geometric basis remains a separate obligation. -/
theorem nonempty_normKernelCompressionLevel
    [LocallyCompactSpace (RationalPoint F G.X)]
    [NonarchimedeanGroup (RationalPoint F G.X)]
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hStandard : StandardCocharacterStatement.{u})
    (hRoots : letI := hi.isSplitSubtorus.mono; HasRelativeRootSystem i)
    (d : NormKernelFundamentalCocharacters i ν)
    (K0 : Subgroup (RationalPoint F G.X))
    (hBasis : SimultaneousStandardBasisAt i ν K0)
    (U : OpenSubgroup (Plancherel.rationalCommonNormKernel G)) :
    Nonempty (NormKernelCompressionLevel d K0 U) := by
  classical
  have := hG.smooth
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hi.isSplitSubtorus.mono
  let H := Plancherel.rationalCommonNormKernel G
  have hH : IsOpen (H : Set (RationalPoint F G.X)) :=
    Plancherel.isOpen_rationalCommonNormKernelConditional G
  have hfinite := hi.isSplitSubtorus.1.finite_simpleRelativeRoots i ν
  have hexists : ∀ I : Finset (SimpleRoot i ν),
      ∃ ζ, IsStandardCocharacter i ν (rootSet i ν I) ζ := fun I =>
    (hStandard F G hG T i hi ν hν _ (rootSet_subset i ν I)).1
  obtain ⟨B, hB, hBJ⟩ := hBasis
  obtain ⟨K, hKB, hKU⟩ := hB.2.mem_iff.mp
    (Jacquet.ambientOpenSubgroup H hH U).mem_nhds_one
  have hKH : K ≤ H := by
    intro k hk
    obtain ⟨x, _, rfl⟩ := hKU hk
    exact x.property
  let Ka : OpenSubgroup (RationalPoint F G.X) := ⟨K, (hB.1 K hKB).2.2.1⟩
  let L := Ka.comap H.subtype continuous_subtype_val
  have hLc : IsCompact (L : Set H) := by
    rw [Subtype.isCompact_iff]
    have heq : (Subtype.val : H → RationalPoint F G.X) '' (L : Set H) = K := by
      ext k
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hx
      · intro hk
        exact ⟨⟨k, hKH hk⟩, hk, rfl⟩
    rw [heq]
    exact (hB.1 K hKB).2.2.2
  have hLU : L.toSubgroup ≤ U.toSubgroup := by
    intro x hx
    obtain ⟨y, hy, heq⟩ := hKU hx
    exact (Subtype.ext heq : y = x) ▸ hy
  have hnormal : K0.comap H.subtype ≤ Subgroup.normalizer (L.toSubgroup : Set H) :=
    Jacquet.normalizer_comap_subtype H K K0
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (hB.1 K hKB).1).mp
        (hB.1 K hKB).2.1)
  have hcon : ∀ α, Jacquet.IsIwahoriContraction L
      (normKernelUnipotent i ν (fundamentalRootFace i ν α))
      (normKernelLevi i ν (fundamentalRootFace i ν α))
      (normKernelStandardOpposite (fundamentalRootFace i ν α)) (d.generator α) := by
    intro α
    let I := fundamentalRootFace i ν α
    obtain ⟨-, A, q, hA, hmem⟩ := hBJ (rootSet i ν I) (rootSet_subset i ν I)
    have hzero : ∀ β ∈ I, simpleRootPairing i ν β (d.cocharacter α) = 0 := by
      intro β hβ
      exact d.pair_eq_zero α β ((mem_fundamentalRootFace i ν α β).mp hβ)
    have hnonneg : ∀ β, 0 ≤ simpleRootPairing i ν β (d.cocharacter α) := by
      intro β
      by_cases h : β = α
      · subst β
        exact (d.pair_pos α).le
      · exact (d.pair_eq_zero α β h).ge
    have hpos : ∀ β, β ∉ I → 0 < simpleRootPairing i ν β (d.cocharacter α) := by
      intro β hβ
      have heq : β = α := by simpa [I] using hβ
      subst β
      exact d.pair_pos α
    have hch := RationalCoefficientDecay.uniformizer_mem_chambers i ν hi hfinite I
      (hexists I) hA (d.cocharacter α) hzero hnonneg
    have hg : (d.generator α).val = uniformizerPowers i (.ofAdd (d.cocharacter α)) := by
      rw [d.generator_val, cocharPoint_comp_eq_map_cocharacterPoints]
      rfl
    apply Jacquet.IsIwahoriContraction.comap_of_le H hH hKH (d.generator α)
    rw [hg]
    exact isIwahoriContraction_of_contractionAndCofinality Ka.isOpen
      (hmem K hKB).1 (hmem K hKB).2
      (uniformizerPowers_mem_levi i ν I (d.cocharacter α))
      hch.1 hch.2.1 (hch.2.2 hpos)
  obtain ⟨-, A0, q0, hA0, hmem0⟩ := hBJ (rootSet i ν ∅) (rootSet_subset i ν ∅)
  have hmember := hmem0 K hKB
  have hch : ∀ n, (d.orthantHom (.ofAdd n)).val ∈ standardComponentCA i q0 ∧
      (d.orthantHom (.ofAdd n)).val ∈ standardComponentCAplus i ν (rootSet i ν ∅) q0 := by
    intro n
    have hnonneg : ∀ β, 0 ≤ simpleRootPairing i ν β (d.orthantCocharacter n) := by
      intro β
      change 0 ≤ latticePairing T β.val (d.orthantCocharacter n)
      rw [d.pair_orthantCocharacter]
      exact mul_nonneg (Int.natCast_nonneg _) (d.pair_pos β).le
    have hc := RationalCoefficientDecay.uniformizer_mem_chambers i ν hi hfinite ∅
      (hexists ∅) hA0 (d.orthantCocharacter n) (by simp) hnonneg
    exact ⟨hc.1, hc.2.1⟩
  have hup : ∀ n x, x ∈ K ⊓ unipotent i ν ∅ →
      (d.orthantHom (.ofAdd n)).val * x * ((d.orthantHom (.ofAdd n)).val)⁻¹ ∈
        K ⊓ unipotent i ν ∅ := by
    intro n x hx
    exact (hmember.2.2.1 _ (hch n).2).1 ⟨x, hx, rfl⟩
  have hlow : ∀ n l, l ∈ K ⊓ standardOppositeUnipotentPoints i ν (rootSet i ν ∅) →
      ((d.orthantHom (.ofAdd n)).val)⁻¹ * l * (d.orthantHom (.ofAdd n)).val ∈
        K ⊓ standardOppositeUnipotentPoints i ν (rootSet i ν ∅) := by
    intro n l hl
    simpa only [inv_inv, SetLike.mem_coe] using (hmember.2.2.1 _ (hch n).2).2 ⟨l, hl, rfl⟩
  have hmid : ∀ n m, m ∈ K ⊓ levi i ν ∅ →
      ((d.orthantHom (.ofAdd n)).val)⁻¹ * m * (d.orthantHom (.ofAdd n)).val ∈
        K ⊓ levi i ν ∅ := by
    intro n m hm
    have hm' : m ∈ ambientConjugate (d.orthantHom (.ofAdd n)).val
        ((K ⊓ levi i ν ∅ : Subgroup (RationalPoint F G.X)) : Set _) := by
      rw [hmember.2.1 _ (hch n).1]
      exact hm
    obtain ⟨y, hy, heq⟩ := hm'
    have heq' : ((d.orthantHom (.ofAdd n)).val)⁻¹ * m *
        (d.orthantHom (.ofAdd n)).val = y := by rw [← heq]; group
    rwa [heq']
  refine ⟨⟨L, hLc, hLU, hnormal, hcon, ?_, ?_, ?_, ?_⟩⟩
  · intro I n x hx
    have hle := unipotent_le_minimal_of_standard hi hν hRoots I (hexists I).choose_spec
    exact (hup n x.val ⟨hx.1, hle hx.2⟩).1
  · intro k hk
    obtain ⟨⟨l, m, x⟩, heq⟩ := hmember.1.2 ⟨k.val, hk⟩
    refine ⟨⟨l, hKH l.property.1⟩, l.property,
      ⟨m, hKH m.property.1⟩, m.property,
      ⟨x, hKH x.property.1⟩, x.property, ?_⟩
    exact Subtype.ext (congrArg Subtype.val heq).symm
  · intro n
    exact ⟨fun x hx => hup n x.val hx, fun l hl => hlow n l.val hl,
      fun m hm => hmid n m.val hm⟩
  · intro n m hm
    have hmem : (d.orthantHom (.ofAdd n)).val * m.val *
        ((d.orthantHom (.ofAdd n)).val)⁻¹ ∈
        ambientConjugate (d.orthantHom (.ofAdd n)).val
          ((K ⊓ levi i ν ∅ : Subgroup (RationalPoint F G.X)) : Set _) :=
      ⟨m.val, hm, rfl⟩
    rw [hmember.2.1 _ (hch n).1] at hmem
    exact hmem.1

end Langlands.Aubert.General.RationalPointFamily
