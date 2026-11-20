import Langlands.BruhatTits.Cartan.RenardLeviConePartitionStatement
import Langlands.Geometry.Building.CocharacterUniformizerProof
import Langlands.Geometry.Building.StandardLeviStrictUniformizerProof
import Langlands.GroupScheme.ClosedSubgroupMonomorphism
import Langlands.GroupScheme.Rational.CocharacterStandardFace
import Langlands.GroupScheme.Rational.LeviSplitComponentInclusionProof
import Langlands.GroupScheme.Rational.StandardParabolicOrderProof
import Langlands.Representation.LanglandsClassification.StandardParabolicDatum

/-! # Proof of the full split-component cone partition modulo the norm kernel -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.CocharacterUniformizer
  Langlands.GroupScheme.RealTorusSpace Langlands.Plancherel

namespace Langlands.BruhatTits.Cartan.RenardLeviCones

private theorem characterOrder_map
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {A B : CommGroupScheme (Spec (CommRingCat.of F))}
    (g : B ⟶ A) (χ : characterLattice A) (y : rationalPoints B.toGrp) :
    characterOrder A χ (rationalPoints.map (CommGroupScheme.groupHom g) y) =
      characterOrder B (g ≫ χ) y := by
  simp only [characterOrder, rationalCharacterValuation_apply]
  exact congrArg (fun v : Fˣ => (fieldOrderUnits F v).toAdd)
    (rationalCharacterEval_characterRestrict (CommGroupScheme.groupHom g)
      ((rationalCharacters.equivCharacterLattice A).symm χ) y).symm

/-- The strict split-component cones partition the nonnegative cone modulo the
common norm kernel for every standard base Levi. -/
theorem leviConePartition : LeviConePartitionStatement.{u} := by
  intro F _ _ _ _ G hG T i hi
  have := hG.isAffineHom
  have := hG.smooth
  have := hi.isSplitSubtorus.mono
  intro ν hν J hJ A a ha f hf q cone piece
  let order (c : rationalPoints A.toGrp ⧸ rationalCommonNormKernel A.toGrp)
      (χ : characterLattice A) : ℤ :=
    (rationalNormKernelQuotientEquiv A.toGrp c).val.toAdd
      ((rationalCharacters.equivCharacterLattice A).symm χ)
  have order_mk (x : rationalPoints A.toGrp) (χ : characterLattice A) :
      order (q x) χ = characterOrder A χ x := by
    change (rationalNormKernelQuotientEquiv A.toGrp (QuotientGroup.mk x)).val.toAdd _ = _
    rw [rationalNormKernelQuotientEquiv_mk]
    rfl
  have pieceOrder {K : Set (characterLattice T)} {c} (hc : c ∈ piece K)
      {α : characterLattice T} (hα : α ∈ simpleRelativeRoots i ν) :
      0 ≤ order c (f ≫ α) ∧ (order c (f ≫ α) = 0 ↔ α ∈ K) := by
    rcases hc with ⟨_, hK, B, b, hb, g, hg, y, hy, rfl⟩
    simp only [Function.comp_apply, order_mk, characterOrder_map, ← Category.assoc]
    by_cases hαK : α ∈ K
    · have hχ := selectedRoot_restrict_eq_zero_standardLevi dynamicLie i ν K hK
        (Standard.isClosedSubgroup_leviHom i ν K) (Standard.isRepresentedBy_leviHom i ν K)
        b hb.1 (g ≫ f) hg hαK
      have hzero : characterOrder B ((g ≫ f) ≫ α) y = 0 := by
        rw [hχ]
        simp only [characterOrder, map_zero]
      rw [hzero]
      simp [hαK]
    · have hpos := (mem_componentStrict_iff_order i ν K (g ≫ f)).mp hy
        ((g ≫ f) ≫ α) ⟨α, ⟨hα, hαK⟩, rfl⟩
      exact ⟨hpos.le, iff_of_false (ne_of_gt hpos) hαK⟩
  have pieceFace {K : Set (characterLattice T)} {c} (hc : c ∈ piece K) :
      K = {α | α ∈ simpleRelativeRoots i ν ∧ order c (f ≫ α) = 0} := by
    have hK : K ⊆ simpleRelativeRoots i ν := hc.2.1
    ext α
    constructor
    · intro hα
      exact ⟨hK hα, (pieceOrder hc (hK hα)).2.mpr hα⟩
    · rintro ⟨hα, hzero⟩
      exact (pieceOrder hc hα).2.mp hzero
  refine ⟨?_, ?_⟩
  · intro K c hc
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
    refine ⟨x, ?_, rfl⟩
    rw [mem_componentPlus_iff_order]
    rintro χ ⟨α, ⟨hα, _⟩, rfl⟩
    rw [← order_mk]
    exact (pieceOrder hc hα).1
  · rintro c ⟨x, hx, rfl⟩
    obtain ⟨ζ, hζ, _⟩ := (isUniformizerLatticeSection F A ha.1.1.1).2.2 x
    have hclass : q x = q (latticeSection F A ζ) :=
      QuotientGroup.eq_iff_div_mem.mpr (by simpa only [div_eq_mul_inv] using hζ)
    let ξ := cocharacterMapInt f ζ.toAdd
    have hval (α : characterLattice T) :
        latticePairing T α ξ = characterOrder A (f ≫ α) x := by
      change latticePairing T α (cocharacterMapInt f ζ.toAdd) = _
      rw [← RelativeRoot.latticePairing_restrict_cocharacterMapInt]
      exact ((mem_normKernel_mul_section_inv_iff F A x ζ).mp hζ (f ≫ α)).symm
    have hvanish (α : characterLattice T) (hα : α ∈ J) : latticePairing T α ξ = 0 :=
      latticePairing_cocharacterMapInt_standardLevi_eq_zero dynamicLie i ν J hJ
        (Standard.isClosedSubgroup_leviHom i ν J) (Standard.isRepresentedBy_leviHom i ν J)
        a ha.1 f hf ζ.toAdd hα
    have hnonneg (α : characterLattice T) (hα : α ∈ simpleRelativeRoots i ν) :
        0 ≤ latticePairing T α ξ := by
      by_cases hαJ : α ∈ J
      · rw [hvanish α hαJ]
      · rw [hval]
        exact (mem_componentPlus_iff_order i ν J f).mp hx (f ≫ α) ⟨α, ⟨hα, hαJ⟩, rfl⟩
    let K := simpleRootFace i ν ξ
    have hξ : IsStandardCocharacter i ν K ξ :=
      isStandardCocharacter_simpleRootFace i ν hnonneg
    have hJK : J ⊆ K := fun α hα => ⟨hJ hα, hvanish α hα⟩
    obtain ⟨_, B, b, _, hb, _⟩ := standardLeviSplitComponentStatement F G hG T i hi ν hν K hξ.1
    have hle : standardLevi i ν J ≤ standardLevi i ν K :=
      (((standardParabolicOrder F G hG T i hi ν hν).1 J K hJ hξ.1).2 hJK).1
    let m := (Standard.isRepresentedBy_leviHom i ν J).inclusionHom
      (Standard.isRepresentedBy_leviHom i ν K) hle
    have hm : m ≫ Standard.leviHom i ν K = Standard.leviHom i ν J :=
      SubgroupFunctor.IsRepresentedBy.inclusionHom_comp _ _ _
    have hP := Standard.parabolicStructure i ν hG hi hν J hJ
    have hQ := Standard.parabolicStructure i ν hG hi hν K hξ.1
    obtain ⟨g, hg⟩ := leviSplitComponentInclusion F G hG _ _ _ _
      (Standard.parabolicHom i ν J) (Standard.parabolicHom i ν K)
      (Standard.leviToParabolic i ν J) (Standard.leviToParabolic i ν K)
      m hP.1 hQ.1 hP.2.1 hQ.2.1 (by simpa only [Standard.leviToParabolic_comp] using hm)
      B A b a hb ha
    have hgf : CommGroupScheme.groupHom (g ≫ f) ≫ i = b ≫ Standard.leviHom i ν K := by
      change (CommGroupScheme.groupHom g ≫ CommGroupScheme.groupHom f) ≫ i = _
      calc
        _ = CommGroupScheme.groupHom g ≫ a ≫ Standard.leviHom i ν J := by
          rw [Category.assoc, hf]
        _ = (CommGroupScheme.groupHom g ≫ a ≫ m) ≫ Standard.leviHom i ν K := by
          simp only [Category.assoc, hm]
        _ = _ := by rw [hg]
    have hclosedK := Standard.isClosedSubgroup_leviHom i ν K
    have hrepK := Standard.isRepresentedBy_leviHom i ν K
    have himage := standardLeviStrictImage F G hG T i hi ν hν K hξ.1
      (Standard.leviScheme i ν K) (Standard.leviHom i ν K) hclosedK hrepK B b hb (g ≫ f) hgf
    have hmem : latticeSection F T (Multiplicative.ofAdd ξ) ∈
        (rationalPoints.map (CommGroupScheme.groupHom (g ≫ f))) ''
          CAstrict F B (restrictedSimpleCharacters i ν K (g ≫ f)) := by
      rw [himage]
      exact ⟨ξ, hξ, rfl⟩
    obtain ⟨y, hy, heq⟩ := hmem
    have hclosedf : IsClosedSubgroup (CommGroupScheme.groupHom f) := by
      apply IsClosedSubgroup.of_comp hi.isSplitSubtorus.2
      rw [hf]
      exact ha.1.1.2.comp (Standard.isClosedSubgroup_leviHom i ν J)
    have hpoint : rationalPoints.map (CommGroupScheme.groupHom g) y = latticeSection F A ζ := by
      have := hclosedf.mono_overHom
      apply (cancel_mono (CommGroupScheme.groupHom f).hom.hom).mp
      change (y ≫ (CommGroupScheme.groupHom g).hom.hom) ≫
          (CommGroupScheme.groupHom f).hom.hom =
        rationalPoints.map (CommGroupScheme.groupHom f) (latticeSection F A ζ)
      rw [Category.assoc]
      exact heq.trans (map_latticeSection f ζ.toAdd).symm
    have hcK : q x ∈ piece K :=
      ⟨hJK, hξ.1, B, b, hb, g, hgf, y, hy.2, by
        rw [Function.comp_apply, hpoint, ← hclass]⟩
    exact ⟨K, hcK, fun L hcL => (pieceFace hcL).trans (pieceFace hcK).symm⟩

end Langlands.BruhatTits.Cartan.RenardLeviCones
