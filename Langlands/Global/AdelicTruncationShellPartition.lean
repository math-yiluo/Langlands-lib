import Langlands.Global.AdelicTruncationShellBounds
import Langlands.Global.ArthurParabolicSpacesProof
import Langlands.Global.ArthurSiegelPartitionProof
import Langlands.Global.ArthurSiegelReductionProof

/-! # Arthur's characteristic partition in the adelic shell coordinates -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Set
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.ArthurTruncation

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
  ArthurParabolicSpaces AdelicGroupPoints AdelicSiegelFactors

variable {F : Type u} [Field F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]
  {ν : cocharacterLattice T}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (D : RelativeRootReflectionData i)

local notation "Δ" => simpleRelativeRoots i ν
local notation "Idx" => Langlands.Global.StandardIndex F G i ν

include hν in
/-- At a height in the closed lower chamber, the relative weight and root conditions
for the parabolic cells hold for some standard index. -/
theorem exists_mem_parabolicCharacteristicChamber {X T₀ Tp : V T}
    (hX : X ∈ D.realCorootSpan) (h₀ : ∀ α ∈ Δ, 0 ≤ eval T α (X - T₀)) :
    ∃ J : Idx, X ∈ parabolicCharacteristicChamber hG hi D J T₀ Tp := by
  classical
  let _ := ArthurRelative.finite_indivisibleRoots hG hi
  let b := ArthurRelative.base hG hi hν D
  let Δ' := ArthurRelative.standardIndex hG hi ν Δ
  obtain ⟨Θ, ⟨⟨_, hΘ⟩, hw, ht⟩, _⟩ := ArthurCombinatorics.existsUnique_weight_nonpos_tau b
    (Finset.empty_subset Δ') (ArthurRelative.standardIndex_subset_support hG hi D hν Δ)
    (ArthurRelative.toCorootSpan hG hi D (X - Tp))
  have hΘΔ (α : RelativeRoot.indivisibleRoots i) (hα : α ∈ Θ) : α.val ∈ Δ :=
    ((ArthurRelative.mem_standardIndex hG hi ν).mp (hΘ hα)).1
  let J : Idx := ⟨Subtype.val '' (Θ : Set (RelativeRoot.indivisibleRoots i)), by
    rintro _ ⟨α, hα, rfl⟩
    exact hΘΔ α hα⟩
  have hJ : ArthurRelative.standardIndex hG hi ν J.val = Θ :=
    ArthurRelative.standardIndex_image hG hi ν Θ hΘΔ
  refine ⟨J, hX, h₀, ?_, ?_⟩
  · rintro _ ⟨α, hα, rfl⟩
    rw [weight_eq_weightCoordinate hG hi D _ (hΘΔ α hα), hJ]
    exact hw α (Finset.mem_sdiff.mpr ⟨hα, Finset.notMem_empty _⟩)
  · have ht' : ArthurRelative.tau hG hi ν D J.val Δ (X - Tp) = 1 := by
      change ArthurCombinatorics.tau (ArthurRelative.rootPairing hG hi D)
        (ArthurRelative.standardIndex hG hi ν J.val) Δ'
        (ArthurRelative.toCorootSpan hG hi D (X - Tp)) = 1
      rwa [hJ]
    rw [ArthurRelative.tau_eq hG hi D _ (Subset.refl _) (X - Tp)] at ht'
    split at ht'
    · assumption
    · contradiction

variable [NumberField F] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
  (hρ : Function.Bijective (restrictToTorus F i ν ∅))
  (C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅))

local notation "H₀" => height hi hK hρ
local notation "Δ₀" => simpleFinset ν hG hi

/-- Representatives of the parabolic characteristic cell inside a common Siegel set.
The auxiliary open Siegel threshold `T₁` allows the characteristic chamber itself to use
the closed lower inequalities at `T₀`. -/
def parabolicCharacteristicSiegelSet (J : Idx) (T₁ T₀ Tp : V T) :
    Set (AdelicGroupPoints F G) :=
  siegelSet hi hK hρ C Δ₀ T₁ ∩ H₀ ⁻¹' parabolicCharacteristicChamber hG hi D J T₀ Tp

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
include hν in
/-- The cells cover the representatives in the common Siegel set whose height satisfies the
closed lower cut and lies in the relative coroot space. -/
theorem mem_iUnion_parabolicCharacteristicSiegelSet {T₁ T₀ Tp : V T}
    {x : AdelicGroupPoints F G} (hx : x ∈ siegelSet hi hK hρ C Δ₀ T₁)
    (hH : H₀ x ∈ D.realCorootSpan) (h₀ : ∀ α ∈ Δ, 0 ≤ eval T α (H₀ x - T₀)) :
    x ∈ ⋃ J : Idx, parabolicCharacteristicSiegelSet hG hi D hK hρ C J T₁ T₀ Tp := by
  obtain ⟨J, hJ⟩ := exists_mem_parabolicCharacteristicChamber hG hi hν D (Tp := Tp) hH h₀
  exact Set.mem_iUnion.mpr ⟨J, hx, hJ⟩

include hν in
/-- A rational identification between representatives of characteristic cells at a sufficiently
regular truncation parameter preserves the standard index and belongs to that parabolic.
This gives disjoint cell images and injectivity on each parabolic quotient image. -/
theorem exists_rational_cell_separation_threshold (hC : C.compactSubgroup = K) (T₁ : V T) :
    ∃ R > 0, ∀ {T₀ Tp : V T}, (∀ α ∈ Δ, R ≤ eval T α Tp) →
      ∀ {J J' : Idx} {x δ : AdelicGroupPoints F G}, δ ∈ rationalSubgroup F G →
        x ∈ parabolicCharacteristicSiegelSet hG hi D hK hρ C J T₁ T₀ Tp →
        δ * x ∈ parabolicCharacteristicSiegelSet hG hi D hK hρ C J' T₁ T₀ Tp →
        J = J' ∧ δ ∈ parabolicRationalImage (Standard.parabolicHom i ν J.val) := by
  classical
  have hred := iwasawaSiegelReduction F G T i ν hG hi hν K hK hρ
  obtain ⟨c, hc⟩ := hred C T₁ hC
  let bound : ℝ := |c| + ∑ α ∈ Δ₀, |eval T α T₁|
  have hbound : 0 ≤ bound := add_nonneg (abs_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  refine ⟨bound + 1, by linarith, ?_⟩
  intro T₀ Tp hTp J J' x δ hδ hx hy
  obtain ⟨hTp₁, hTp₂⟩ := regular_of_lt hG hi T₁ c
    (fun α hα => (lt_add_one bound).trans_le (hTp α hα))
  have hΔ : ((Δ₀ : Finset _) : Set (characterLattice T)) = Δ := coe_simpleFinset hG hi
  let liftIndex (J : Idx) := ((hi.isSplitSubtorus.1.finite_simpleRelativeRoots i ν).subset J.2).toFinset
  have hJ (J : Idx) : (liftIndex J : Set (characterLattice T)) = J.val := Set.Finite.coe_toFinset _
  have hle (J : Idx) : liftIndex J ⊆ Δ₀ := Finset.coe_subset.mp (by rw [hJ, hΔ]; exact J.2)
  have hind {y : AdelicGroupPoints F G} (Q : Idx)
      (hy : y ∈ parabolicCharacteristicSiegelSet hG hi D hK hρ C Q T₁ T₀ Tp) :
      siegelIndicator hG hi D hK hρ C (liftIndex Q) T₁ Tp y = 1 := by
    unfold siegelIndicator
    refine ite_eq_left ⟨1, Subgroup.one_mem _, ?_⟩
    rw [one_mul]
    refine ⟨siegelSet_mono hi hK hρ C (hle Q) T₁ hy.1, fun α hα => ?_⟩
    rw [hJ]
    exact hy.2.2.2.1 α (by rw [← hJ]; exact hα)
  have htau {y : AdelicGroupPoints F G} (Q : Idx)
      (hy : y ∈ parabolicCharacteristicSiegelSet hG hi D hK hρ C Q T₁ T₀ Tp) :
      ArthurRelative.tau hG hi ν D (liftIndex Q : Set (characterLattice T)) (Δ₀ : Set _)
        (H₀ y - Tp) = 1 := by
    rw [hJ, hΔ, ArthurRelative.tau_eq hG hi D _ (Subset.refl _) (H₀ y - Tp)]
    exact ite_eq_left hy.2.2.2.2
  have hΓ : (rationalSubgroup F G : Set (AdelicGroupPoints F G)) ⊆
      parabolicRationalImage (Standard.parabolicHom i ν (Δ₀ : Set (characterLattice T))) := by
    rw [hΔ]
    exact rationalSubgroup_le_parabolicRationalImage hG hi hν
  obtain ⟨heq, hmem⟩ := partition_term_unique parabolicSpacesComparison hG hi hν D hK hρ C hC
    T₁ Tp (subset_refl Δ₀) (hle J) (hle J') hTp₂
    (hc Tp hTp₁ Δ₀ (Finset.mem_powerset_self _)) (hΓ (Subgroup.one_mem _)) (hΓ hδ)
    (by simpa only [one_mul] using hind J hx)
    (by simpa only [one_mul] using htau J hx) (hind J' hy) (htau J' hy)
  have hSets := congrArg (fun s : Finset (characterLattice T) => (↑s : Set (characterLattice T))) heq
  refine ⟨Subtype.ext ((hJ J).symm.trans (hSets.trans (hJ J'))), ?_⟩
  rw [hJ J, inv_one, mul_one] at hmem
  exact hmem

/-- Images of norm-one characteristic Siegel representatives in the rational quotient. -/
def normOneCharacteristicSiegelRegion (J : Idx) (T₁ T₀ Tp : V T) :
    Set (NormOneRationalQuotient F G) :=
  LeftCosetSpace.mk (rationalNormOneSubgroup F G) ''
    (Subtype.val ⁻¹' parabolicCharacteristicSiegelSet hG hi D hK hρ C J T₁ T₀ Tp)

include hν in
/-- Distinct indices give disjoint images of the characteristic Siegel representatives
on the norm-one rational quotient. -/
theorem exists_pairwiseDisjoint_normOneCharacteristicSiegelRegion
    (hC : C.compactSubgroup = K) (T₁ : V T) :
    ∃ R > 0, ∀ {T₀ Tp : V T}, (∀ α ∈ Δ, R ≤ eval T α Tp) →
      Set.univ.PairwiseDisjoint
        (fun J : Idx => normOneCharacteristicSiegelRegion hG hi D hK hρ C J T₁ T₀ Tp) := by
  obtain ⟨R, hR, hsep⟩ := exists_rational_cell_separation_threshold hG hi hν D hK hρ C hC T₁
  refine ⟨R, hR, fun {T₀ Tp} hTp J _ J' _ hne => Set.disjoint_left.mpr ?_⟩
  rintro q ⟨x, hx, hxq⟩ ⟨y, hy, hyq⟩
  have hΓ := (LeftCosetSpace.mk_eq_mk_iff (rationalNormOneSubgroup F G) x y).mp (hxq.trans hyq.symm)
  let δ := (y : AdelicGroupPoints F G) * (x : AdelicGroupPoints F G)⁻¹
  have hδ : δ ∈ rationalSubgroup F G := (rationalNormOneSubgroupInclusion F G ⟨_, hΓ⟩).2
  have hxy : δ * (x : AdelicGroupPoints F G) = (y : AdelicGroupPoints F G) := by
    exact inv_mul_cancel_right _ _
  exact hne (hsep hTp hδ hx (hxy.symm ▸ hy)).1

end Langlands.Global.ArthurTruncation
