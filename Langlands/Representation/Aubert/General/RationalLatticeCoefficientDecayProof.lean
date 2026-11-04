import Langlands.Representation.Aubert.General.RationalLatticeCoefficientDecayStatement
import Langlands.Representation.Aubert.General.RationalLatticeStrictExponentProof
import Langlands.Representation.Exponents.HaarNormalizedLatticeCoefficientBoundProof
import Langlands.BruhatTits.SpecialCompact.JacquetAdapterProof

/-! # Coefficient decay on the actual rational uniformizer lattice -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal BigOperators

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme BruhatTits.SpecialCompact
open Langlands.AlgebraicGeometry.PointTopology

namespace RationalCoefficientDecay

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/-- Orthogonal integral cocharacters lift through the compatible split component. -/
theorem exists_component_lift (hi : IsMaximalSplitTorus i)
    (hfinite : (simpleRelativeRoots i ν).Finite)
    (J : Finset (SimpleRoot i ν))
    (hexists : ∃ ζ, IsStandardCocharacter i ν (rootSet i ν J) ζ)
    {A : CommGroupScheme (Spec (CommRingCat.of k))} {q : A.toGrp ⟶ T.toGrp}
    (hA : IsCompatibleStandardSplitComponent i ν (rootSet i ν J) A q)
    (y : cocharacterLattice T)
    (hy : ∀ β ∈ J, simpleRootPairing i ν β y = 0) :
    ∃ c : cocharacterLattice A,
      RealTorusSpace.cocharacterMapInt (Additive.ofMul q : A ⟶ T) c = y := by
  obtain ⟨-, M, jM, a, hjM, hjMc, hMred, ha, haq⟩ := hA
  have : IsAffineHom M.X.hom := hMred.isAffineHom
  let t := standardLeviTorusFactor i ν (rootSet i ν J) hjM
  have : Mono t.hom.hom.left :=
    (hi.isMaximalSplitTorus_standardLeviTorusFactor i ν _ hjM hjMc).isSplitSubtorus.mono
  have hf : CommGroupScheme.groupHom (Additive.ofMul q : A ⟶ T) ≫ t = a := by
    have : Mono jM.hom.hom := hjM.1
    apply Grp.hom_ext
    apply (cancel_mono jM.hom.hom).mp
    rw [← Grp.comp_hom_hom, ← Grp.comp_hom_hom, Category.assoc,
      standardLeviTorusFactor_comp, haq]
    rfl
  have hyc : y ∈ centralCocharacters t :=
    isCentral_standardLeviTorusFactor_of_annihilates i ν (rootSet i ν J) hjM hfinite
      hexists y (by rintro α ⟨β, hβ, rfl⟩; exact hy β hβ)
  rw [← ha.range_cocharacterMapInt_eq_centralCocharacters _ hf] at hyc
  exact hyc

/-- The same actual uniformizer power lies in the component and its weak chamber;
strict outside-root pairings also place it in the strict chamber. -/
theorem uniformizer_mem_chambers (hi : IsMaximalSplitTorus i)
    (hfinite : (simpleRelativeRoots i ν).Finite)
    (J : Finset (SimpleRoot i ν))
    (hexists : ∃ ζ, IsStandardCocharacter i ν (rootSet i ν J) ζ)
    {A : CommGroupScheme (Spec (CommRingCat.of k))} {q : A.toGrp ⟶ T.toGrp}
    (hA : IsCompatibleStandardSplitComponent i ν (rootSet i ν J) A q)
    (y : cocharacterLattice T)
    (hy : ∀ β ∈ J, simpleRootPairing i ν β y = 0)
    (hnonneg : ∀ β, 0 ≤ simpleRootPairing i ν β y) :
    uniformizerPowers i (.ofAdd y) ∈ standardComponentCA i q ∧
      uniformizerPowers i (.ofAdd y) ∈ standardComponentCAplus i ν (rootSet i ν J) q ∧
      ((∀ β, β ∉ J → 0 < simpleRootPairing i ν β y) →
        uniformizerPowers i (.ofAdd y) ∈
          standardComponentCAstrict i ν (rootSet i ν J) q) := by
  obtain ⟨c, rfl⟩ := exists_component_lift i ν hi hfinite J hexists hA y hy
  let p := CocharacterUniformizer.latticeSection k A (.ofAdd c)
  have hp : p ∈ CocharacterUniformizer.CA k A := ⟨.ofAdd c, rfl⟩
  have heq : rationalPoints.map (q ≫ i) p =
      uniformizerPowers i (.ofAdd
        (RealTorusSpace.cocharacterMapInt (Additive.ofMul q : A ⟶ T) c)) := by
    change rationalPoints.map i (rationalPoints.map
      (CommGroupScheme.groupHom (Additive.ofMul q : A ⟶ T))
        (Plancherel.RenardCartan.uniformizerSection A (.ofAdd c))) = _
    rw [Plancherel.RenardCartan.uniformizerSection_naturality]
    rfl
  have hq : (1 : ℝ) < LocalField.residueCardinality k := by
    exact_mod_cast LocalField.residueCardinality_gt_one k
  refine ⟨⟨p, hp, heq⟩, ⟨p, ⟨hp, ?_⟩, heq⟩, fun hstrict =>
    ⟨p, ⟨hp, ?_⟩, heq⟩⟩
  · rintro _ ⟨β, ⟨hβ, -⟩, rfl⟩
    rw [characterNorm_latticeSection, latticePairing_componentCharacterRestriction]
    exact zpow_le_one_of_nonpos₀ hq.le (neg_nonpos.mpr (hnonneg ⟨β, hβ⟩))
  · rintro _ ⟨β, ⟨hβ, hβJ⟩, rfl⟩
    rw [characterNorm_latticeSection, latticePairing_componentCharacterRestriction]
    apply zpow_lt_one_of_neg₀ hq
    exact neg_neg_of_pos (hstrict ⟨β, hβ⟩
      (fun h => hβJ ((val_mem_rootSet i ν J ⟨β, hβ⟩).mpr h)))

end RationalCoefficientDecay

/-- A simultaneous actual standard basis and strict actual normalized Jacquet
exponents give the coefficient estimate on every finite noncentral ray lattice. -/
theorem rationalLatticeCoefficientDecay :
    RationalLatticeCoefficientDecayStatement.{u, v, w} := by
  intro k _ _ _ _ G hG T i hi
  have := hG.isAffineHom
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ ν hν hStandard hU A hA hstrict K0 hBasis
  classical
  have := hG.smooth
  have hfinite := hi.isSplitSubtorus.1.finite_simpleRelativeRoots i ν
  have hexists : ∀ J : Finset (SimpleRoot i ν),
      ∃ ζ, IsStandardCocharacter i ν (rootSet i ν J) ζ := fun J =>
    (hStandard k G hG T i hi ν hν (rootSet i ν J) (rootSet_subset i ν J)).1
  obtain ⟨B, hB, hBJ⟩ := hBasis
  refine ⟨B, hB, ?_⟩
  intro I _ _ J x hzero hpos hout
  have hnonneg : ∀ a β, 0 ≤ simpleRootPairing i ν β (x a) := by
    intro a β
    by_cases hβ : β ∈ J a
    · exact (hzero a β hβ).ge
    · exact (hpos a β hβ).le
  have hstandard : ∀ a, IsStandardCocharacter i ν (rootSet i ν (J a)) (x a) := by
    intro a
    refine ⟨rootSet_subset i ν (J a), ?_, ?_⟩
    · rintro β ⟨γ, hγ, rfl⟩
      exact hzero a γ hγ
    · intro β hβ hβJ
      exact hpos a ⟨β, hβ⟩
        (fun h => hβJ ((val_mem_rootSet i ν (J a) ⟨β, hβ⟩).mpr h))
  choose z hz hzstrict using fun a =>
    rationalLatticeStrictExponent k G hG T i hi ν hν hStandard hU A hstrict
      (J a) (x a) (hzero a) (hnonneg a) (by
        obtain ⟨β, hβ⟩ := hout a
        exact ⟨β, hpos a β hβ⟩)
  refine ⟨z, hz, ?_⟩
  intro K hKB v φ hφ
  let e : (I → ℕ) →+ cocharacterLattice T :=
    { toFun := fun n => ∑ a, n a • x a
      map_zero' := by simp
      map_add' := by
        intro m n
        simp only [Pi.add_apply, add_nsmul, Finset.sum_add_distrib] }
  let τ : Multiplicative (I → ℕ) →* RationalPoint k G.X :=
    (uniformizerPowers i).comp e.toMultiplicative
  have hgen : ∀ a, τ (.ofAdd (Pi.single a 1)) =
      ((z a : levi i ν (J a)) : RationalPoint k G.X) := by
    intro a
    rw [hz a]
    simp [τ, e, Pi.single_apply]
  have hbasis : ∀ a, Jacquet.HasIwahoriContractionBasis
      (unipotent i ν (J a)) (levi i ν (J a))
      (standardOppositeUnipotentPoints i ν (rootSet i ν (J a))) := by
    intro a
    exact SimultaneousStandardBasisAt.hasIwahoriContractionBasis i ν hi
      (show SimultaneousStandardBasisAt i ν K0 from ⟨B, hB, hBJ⟩)
      (rootSet_subset i ν (J a)) (hstandard a)
  have hcon : ∀ a, Jacquet.IsIwahoriContraction K
      (unipotent i ν (J a)) (levi i ν (J a))
      (standardOppositeUnipotentPoints i ν (rootSet i ν (J a)))
      ((z a : levi i ν (J a)) : RationalPoint k G.X) := by
    intro a
    obtain ⟨-, A₁, q₁, hA₁, hmem₁⟩ :=
      hBJ (rootSet i ν (J a)) (rootSet_subset i ν (J a))
    have hch := RationalCoefficientDecay.uniformizer_mem_chambers i ν hi hfinite
      (J a) (hexists (J a)) hA₁ (x a) (hzero a) (hnonneg a)
    rw [hz a]
    exact isIwahoriContraction_of_contractionAndCofinality K.isOpen
      (hmem₁ K.toSubgroup hKB).1 (hmem₁ K.toSubgroup hKB).2
      (uniformizerPowers_mem_levi i ν (J a) (x a))
      hch.1 hch.2.1 (hch.2.2 (hpos a))
  obtain ⟨-, A₀, q₀, hA₀, hmem₀⟩ :=
    hBJ (rootSet i ν ∅) (rootSet_subset i ν ∅)
  have hmember := hmem₀ K.toSubgroup hKB
  have hfactor : ∀ k ∈ K,
      ∃ l ∈ K.toSubgroup ⊓ standardOppositeUnipotentPoints i ν (rootSet i ν ∅),
      ∃ m ∈ K.toSubgroup ⊓ levi i ν ∅,
      ∃ u ∈ K.toSubgroup ⊓ unipotent i ν ∅, k = l * m * u := by
    intro k hk
    obtain ⟨⟨l, m, u⟩, heq⟩ := hmember.1.2 ⟨k, hk⟩
    exact ⟨l, l.property, m, m.property, u, u.property,
      (congrArg Subtype.val heq).symm⟩
  have hch₀ : ∀ n : I → ℕ,
      τ (.ofAdd n) ∈ standardComponentCA i q₀ ∧
        τ (.ofAdd n) ∈ standardComponentCAplus i ν (rootSet i ν ∅) q₀ := by
    intro n
    have hnn : ∀ β, 0 ≤ simpleRootPairing i ν β (∑ a, n a • x a) := by
      intro β
      rw [map_sum]
      apply Finset.sum_nonneg
      intro a _
      rw [map_nsmul]
      exact nsmul_nonneg (hnonneg a β) _
    have hc := RationalCoefficientDecay.uniformizer_mem_chambers i ν hi hfinite
      ∅ (hexists ∅) hA₀ (∑ a, n a • x a) (by simp) hnn
    exact ⟨hc.1, hc.2.1⟩
  have hup : ∀ n u, u ∈ K.toSubgroup ⊓ unipotent i ν ∅ →
      τ (.ofAdd n) * u * (τ (.ofAdd n))⁻¹ ∈ K := by
    intro n u hu
    exact ((hmember.2.2.1 _ (hch₀ n).2).1 ⟨u, hu, rfl⟩).1
  have hlow : ∀ n l,
      l ∈ K.toSubgroup ⊓ standardOppositeUnipotentPoints i ν (rootSet i ν ∅) →
      (τ (.ofAdd n))⁻¹ * l * τ (.ofAdd n) ∈ K := by
    intro n l hl
    have h := (hmember.2.2.1 _ (hch₀ n).2).2 ⟨l, hl, rfl⟩
    have h' : (τ (.ofAdd n))⁻¹ * l * ((τ (.ofAdd n))⁻¹)⁻¹ ∈ K.toSubgroup := h.1
    rw [inv_inv] at h'
    exact h'
  have hmid : ∀ n m, m ∈ K.toSubgroup ⊓ levi i ν ∅ →
      (τ (.ofAdd n))⁻¹ * m * τ (.ofAdd n) ∈ K := by
    intro n m hm
    have hm' : m ∈ ambientConjugate (τ (.ofAdd n))
        ((K.toSubgroup ⊓ levi i ν ∅ : Subgroup (RationalPoint k G.X)) :
          Set (RationalPoint k G.X)) := by
      rw [hmember.2.1 _ (hch₀ n).1]
      exact hm
    obtain ⟨y, hy, heq⟩ := hm'
    have heq' : (τ (.ofAdd n))⁻¹ * m * τ (.ofAdd n) = y := by
      rw [← heq]
      group
    rw [heq']
    exact hy.1
  exact haarNormalizedLatticeCoefficientBound (RationalPoint k G.X) I A hA K
    (hB.1 K.toSubgroup hKB).2.2.2
    (unipotent i ν ∅) (levi i ν ∅)
    (standardOppositeUnipotentPoints i ν (rootSet i ν ∅))
    hfactor τ hup hlow hmid
    (fun a => unipotent i ν (J a)) (fun a => levi i ν (J a))
    (fun a => standardOppositeUnipotentPoints i ν (rootSet i ν (J a)))
    (fun a => hU (J a)) (fun a => levi_le_normalizer i ν (J a))
    hbasis z hgen hcon hzstrict v φ hφ

end Langlands.Aubert.General.RationalPointFamily
