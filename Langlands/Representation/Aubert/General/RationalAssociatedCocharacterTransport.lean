import Langlands.Representation.Aubert.General.RationalLeviCentralCharacterSigns
import Langlands.Representation.Aubert.General.RationalAssociatedLeviConjugation
import Langlands.GroupScheme.Rational.StandardAssociatedOppositeTransportReduction

/-! # Associated-opposite cocharacters under the specified point-root laws -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme Group.RelativeWeylIndexing

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  (ν : cocharacterLattice T)
  (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
  [Fintype (SimpleRoot i ν)] [Fintype (Weyl i)]
  {CM : CoxeterMatrix (SimpleRoot i ν)}
  (cs : ActualCoxeterSystem (torusPoints i) CM)
  (hLength : RootLengthComparison i ν hN hZ cs)
  (hSimple : PositiveSimpleReflectionComparison i ν hN hZ cs)
  (hMin : minimalityLengthCriterion cs) (hAssoc : associatedSubsetLaws cs)

include hLength hSimple hMin hAssoc in
/-- The target's point-root comparisons suffice to transport a standard
cocharacter to the associated opposite face, for every specified lift. -/
theorem isStandardCocharacter_associatedOpposite_of_pointRootSigns
    (hT : IsSplitTorus T.toGrp) (hRoots : HasRelativeRootSystem i)
    (hν : IsGenericCocharacter i ν)
    (J : Finset (SimpleRoot i ν))
    (n : Group.RelativeWeyl.normalizer (torusPoints i))
    (hn : QuotientGroup.mk n = longestRep cs J)
    {ζ : cocharacterLattice T}
    (hζ : IsStandardCocharacter i ν (rootSet i ν J) ζ) :
    IsStandardCocharacter i ν (rootSet i ν (associatedSubset cs J))
      (associatedOppositeCocharacter i ((normalizerEquiv i hN).symm n) ζ) := by
  let ns := (normalizerEquiv i hN).symm n
  have haction : weylAction i ns =
      weylCharacterAction i hN hZ (longestRep cs J) := by
    rw [← weylCharacterAction_point_mk i hN hZ n, hn]
  have hK : weylAction i ns '' rootSet i ν (associatedSubset cs J) =
      rootSet i ν J := by
    rw [haction, rootSet_associatedSubset i ν hN hZ cs hLength hSimple hMin hAssoc,
      Set.image_image]
    have hc : (fun α => weylCharacterAction i hN hZ (longestRep cs J)
        (weylCharacterAction i hN hZ (longestRep cs J)⁻¹ α)) = id := by
      funext α
      change (weylCharacterAction i hN hZ (longestRep cs J) *
        weylCharacterAction i hN hZ (longestRep cs J)⁻¹) α = α
      rw [← map_mul, mul_inv_cancel, map_one]
      rfl
    rw [hc, Set.image_id]
  refine ⟨rootSet_subset i ν _, fun α hα => ?_, fun α hα hαK => ?_⟩
  · rw [latticePairing_associatedOppositeCocharacter,
      hζ.2.1 _ (hK ▸ Set.mem_image_of_mem _ hα), neg_zero]
  · rw [latticePairing_associatedOppositeCocharacter, Left.neg_pos_iff]
    let a : SimpleRoot i ν := ⟨α, hα⟩
    have ha : a ∉ associatedSubset cs J := fun ha =>
      hαK ((val_mem_rootSet i ν _ a).2 ha)
    have hroot : weylAction i ns α ∈ relativeRoots i :=
      weylAction_mapsTo_relativeRoots i ns hα.1.1
    have hnotpos : weylAction i ns α ∉ positiveRelativeRoots i ν := by
      intro hpos
      apply ha
      rw [← positiveSimpleSet_longestRep cs J, mem_positiveSimpleSet]
      apply (hLength _ a).mpr
      rwa [haction] at hpos
    have hν' : latticePairing T (weylAction i ns α) ν < 0 :=
      lt_of_le_of_ne (not_lt.mp fun hlt => hnotpos ⟨hroot, hlt⟩) (hν _ hroot)
    have hpos : -weylAction i ns α ∈ positiveRelativeRoots i ν :=
      ⟨hRoots.neg_mem_relativeRoots i hT hroot, by simpa using neg_pos.mpr hν'⟩
    have hnot : -weylAction i ns α ∉ AddSubmonoid.closure (rootSet i ν J) := by
      intro hmem
      have key : ∀ x ∈ AddSubmonoid.closure (rootSet i ν J),
          0 ≤ latticePairing T ((weylAction i ns).symm x) ν := by
        intro x hx
        induction hx using AddSubmonoid.closure_induction with
        | mem x hx =>
          rw [← hK] at hx
          obtain ⟨y, hy, rfl⟩ := hx
          rw [LinearEquiv.symm_apply_apply]
          exact (rootSet_subset i ν _ hy).1.2.le
        | zero => simp
        | add x y _ _ hx hy =>
          rw [map_add, map_add]
          exact add_nonneg hx hy
      have hle := key _ hmem
      rw [map_neg, LinearEquiv.symm_apply_apply, map_neg] at hle
      have hαν := hα.1.2
      simp only [LinearMap.neg_apply] at hle
      omega
    have hlt := (hζ.pairing_pos_iff_not_mem_closure i ν hpos).mpr hnot
    simpa using hlt

 /-- The actual associated-opposite cocharacter, retaining its standardness
 certificate for the associated simple-root subset. -/
def associatedOppositeStandardCocharacter
    (hT : IsSplitTorus T.toGrp) (hRoots : HasRelativeRootSystem i)
    (hν : IsGenericCocharacter i ν)
    (J : Finset (SimpleRoot i ν))
    (n : Group.RelativeWeyl.normalizer (torusPoints i))
    (hn : QuotientGroup.mk n = longestRep cs J)
    (ζ : {ζ : cocharacterLattice T // IsStandardCocharacter i ν (rootSet i ν J) ζ}) :
    {ξ : cocharacterLattice T //
      IsStandardCocharacter i ν (rootSet i ν (associatedSubset cs J)) ξ} :=
  ⟨associatedOppositeCocharacter i ((normalizerEquiv i hN).symm n) ζ.val,
    isStandardCocharacter_associatedOpposite_of_pointRootSigns i ν hN hZ cs
      hLength hSimple hMin hAssoc hT hRoots hν J n hn ζ.property⟩

section Uniformizer

omit [Mono i.hom.hom.left] [IsAffineHom G.X.hom] [Fintype (Weyl i)]

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/-- Evaluation at the common uniformizer respects actual normalizer
conjugation of cocharacters. -/
theorem uniformizerPowers_cocharacterAut (n : normalizerPoints i)
    (ζ : cocharacterLattice T) :
    uniformizerPowers i (.ofAdd (cocharacterAut (normalizingAut i n) ζ)) =
      (n : rationalPoints G) * uniformizerPowers i (.ofAdd ζ) *
        (n : rationalPoints G)⁻¹ := by
  have heq := groupHom_cocharacterAut_comp i n ζ
  have hp := congrArg (fun f => GroupScheme.rationalPoints.map f
    ((Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of k)))).symm
      (SplitTorusValuation.uniformizerUnit k))) heq
  change
    (Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of k)))).symm
        (SplitTorusValuation.uniformizerUnit k) ≫
        (CommGroupScheme.groupHom (cocharacterAut (normalizingAut i n) ζ)).hom.hom ≫
        i.hom.hom =
      (n : rationalPoints G) *
        ((Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of k)))).symm
          (SplitTorusValuation.uniformizerUnit k) ≫
          (CommGroupScheme.groupHom ζ).hom.hom ≫ i.hom.hom) *
        (n : rationalPoints G)⁻¹
  simp only [GroupScheme.rationalPoints.map_apply, Grp.comp_hom_hom] at hp
  simp only [← Category.assoc] at hp
  rw [comp_innerIso_hom, constantPoint_self] at hp
  simpa only [← Category.assoc] using hp

/-- Longest conjugation sends the associated-opposite uniformizer point
to the inverse original uniformizer point. -/
theorem uniformizerPowers_associatedOpposite_conj (n : normalizerPoints i)
    (ζ : cocharacterLattice T) :
    (n : rationalPoints G) *
        uniformizerPowers i (.ofAdd (associatedOppositeCocharacter i n ζ)) *
          (n : rationalPoints G)⁻¹ =
      (uniformizerPowers i (.ofAdd ζ))⁻¹ := by
  rw [← uniformizerPowers_cocharacterAut,
    associatedOppositeCocharacter, LinearEquiv.apply_symm_apply]
  rw [ofAdd_neg, map_inv]

end Uniformizer

end Langlands.Aubert.General.RationalPointFamily
