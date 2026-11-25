import Langlands.Global.AdelicEisensteinRootSigns
import Langlands.Global.AdelicDynamicDeterminantHeight
import Langlands.GroupScheme.Dynamic.RootSystemDeterminantRestriction
import Langlands.GroupScheme.Dynamic.AdjointDeterminantCentralizerRestrictionProof

/-! # Bounds on the adelic Iwasawa evaluations of positive-weight characters -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.Dynamic.Affine

variable {F : Type u} [Field F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (ζ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)

/-- The adjoint determinant of the canonical represented dynamic parabolic. -/
def adjointDeterminant : rationalCharacters (parabolicScheme ζ) :=
  let : IsAffineHom (unipotentScheme ζ).X.hom := (isClosedSubgroup_unipotentHom ζ).isAffineHom
  let : LocallyOfFiniteType (unipotentScheme ζ).X.hom :=
    (isClosedSubgroup_unipotentHom ζ).locallyOfFiniteType
  let : IsAffineHom (parabolicScheme ζ).X.hom := (isClosedSubgroup_parabolicHom ζ).isAffineHom
  let : IsAffine (parabolicScheme ζ).X.left := isAffine_of_isAffineHom (parabolicScheme ζ).X.hom
  Dynamic.adjointDeterminantCharacter (isRepresentedBy_parabolicHom ζ)
    (isRepresentedBy_unipotentHom ζ) (Lie.finiteCoordinates _)

end Langlands.GroupScheme.Dynamic.Affine

namespace Langlands.GroupScheme.ParabolicRootPresentation

open Langlands.Plancherel

variable {F : Type u} [Field F] {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G P M : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M} (r : ParabolicRootPresentation p l a)
  [LocallyOfFiniteType G.X.hom]

include r in
/-- Opposite split-component weights have the same multiplicity by the ambient
Weyl reflections and the decomposition of each restriction fiber. -/
theorem finrank_weightSpace_neg_splitComponent (hG : IsConnectedReductive G)
    (α : characterLattice A) :
    Module.finrank F (weightSpace (a ≫ l ≫ p) (-α)) =
      Module.finrank F (weightSpace (a ≫ l ≫ p) α) := by
  classical
  by_cases h0 : α = 0
  · subst α
    rw [neg_zero]
  let := r.isCompatible.maximalSplit.isSplitSubtorus.mono
  have hA := r.isCompatible.splitComponent.1.isSplitSubtorus.1
  have hT := r.isCompatible.maximalSplit.isSplitSubtorus.1
  have hroot := relativeRootSystem F G hG r.data.T r.data.i r.isCompatible.maximalSplit
  let S := (hT.finite_relativeRoots r.data.i).toFinset
  have hS (β : characterLattice r.data.T) : β ∈ S ↔ β ∈ relativeRoots r.data.i :=
    Set.Finite.mem_toFinset _
  rw [parabolic_finrank_weightSpace_eq_sum r hA hT S (fun β hβ => (hS β).2 hβ)
    (neg_ne_zero.mpr h0),
    parabolic_finrank_weightSpace_eq_sum r hA hT S (fun β hβ => (hS β).2 hβ) h0]
  have hn (b : characterLattice r.data.T) (theta : characterLattice A)
      (hb : b ∈ S.filter (fun ψ => r.data.f ≫ ψ = theta)) :
      -b ∈ S.filter (fun ψ => r.data.f ≫ ψ = -theta) := by
    obtain ⟨hbroot, hbres⟩ := Finset.mem_filter.mp hb
    exact Finset.mem_filter.mpr ⟨(hS _).2 (hroot.neg_mem_relativeRoots r.data.i hT
      ((hS _).1 hbroot)), by rw [Preadditive.comp_neg, hbres]⟩
  refine Finset.sum_bij' (fun β _ => -β) (fun β _ => -β) ?_ ?_ ?_ ?_ ?_
  · intro β hβ
    simpa only [neg_neg] using hn β (-α) hβ
  · intro β hβ
    exact hn β α hβ
  · intro β _
    exact neg_neg β
  · intro β _
    exact neg_neg β
  · intro β _
    exact (hroot.finrank_weightSpace_neg hT β).symm

include r in
/-- The positive-weight sums of opposite split-component cocharacters are opposite. -/
theorem positiveWeightCharacter_neg_splitComponent (hG : IsConnectedReductive G)
    (mu : cocharacterLattice A) :
    positiveWeightCharacter (a ≫ l ≫ p) (-mu) =
      -positiveWeightCharacter (a ≫ l ≫ p) mu := by
  unfold positiveWeightCharacter
  rw [← finsum_comp_equiv (Equiv.neg (characterLattice A)), ← finsum_neg_distrib]
  apply finsum_congr
  intro α
  simp only [Equiv.neg_apply, AddEquiv.map_neg, LinearMap.map_neg, LinearMap.neg_apply, neg_neg,
    smul_neg]
  rw [show (Equiv.neg (characterLattice A)) α = -α from rfl,
    r.finrank_weightSpace_neg_splitComponent hG]

variable [IsAffine G.X.left]

/-- The negative adjoint determinant of the parabolic containing `P`, pulled
back to `P`, for a cocharacter admissible on the full opposite radical. -/
def oppositeAdmissibleWeightCharacter (hG : IsConnectedReductive G) (mu : cocharacterLattice A)
    (hmu : IsOppositeIntersectionAdmissible (a ≫ l ≫ p)
      r.splitComponentCocharacter (-r.splitComponentCocharacter) mu) : rationalCharacters P :=
  -characterRestrict (r.oppositeAdmissibleParabolicFactor hG mu hmu)
    (Dynamic.Affine.adjointDeterminant (CommGroupScheme.groupHom (-mu) ≫ a ≫ l ≫ p))

/-- On the actual split component the pulled-back character is the full
positive-weight sum of the original admissible cocharacter. -/
theorem characterRestrict_oppositeAdmissibleWeightCharacter (hG : IsConnectedReductive G)
    (mu : cocharacterLattice A)
    (hmu : IsOppositeIntersectionAdmissible (a ≫ l ≫ p)
      r.splitComponentCocharacter (-r.splitComponentCocharacter) mu) :
    characterRestrict (a ≫ l) (r.oppositeAdmissibleWeightCharacter hG mu hmu) =
      positiveWeightCharacter (a ≫ l ≫ p) mu := by
  let ζ := CommGroupScheme.groupHom (-mu) ≫ a ≫ l ≫ p
  let hQ := Dynamic.Affine.isRepresentedBy_parabolicHom ζ
  let hU := Dynamic.Affine.isRepresentedBy_unipotentHom ζ
  let hZ := Dynamic.Affine.isRepresentedBy_centralizerHom ζ
  let : IsAffineHom (Dynamic.Affine.parabolicScheme ζ).X.hom :=
    (Dynamic.Affine.isClosedSubgroup_parabolicHom ζ).isAffineHom
  let : IsAffine (Dynamic.Affine.parabolicScheme ζ).X.left :=
    isAffine_of_isAffineHom (Dynamic.Affine.parabolicScheme ζ).X.hom
  let : IsAffineHom (Dynamic.Affine.unipotentScheme ζ).X.hom :=
    (Dynamic.Affine.isClosedSubgroup_unipotentHom ζ).isAffineHom
  let : LocallyOfFiniteType (Dynamic.Affine.unipotentScheme ζ).X.hom :=
    (Dynamic.Affine.isClosedSubgroup_unipotentHom ζ).locallyOfFiniteType
  let : IsAffineHom (Dynamic.Affine.centralizerScheme ζ).X.hom :=
    (Dynamic.Affine.isClosedSubgroup_centralizerHom ζ).isAffineHom
  let : IsAffine (Dynamic.Affine.centralizerScheme ζ).X.left :=
    isAffine_of_isAffineHom (Dynamic.Affine.centralizerScheme ζ).X.hom
  let c := Lie.finiteCoordinates (Dynamic.Affine.unipotentScheme ζ)
  have hcent : SubgroupFunctor.range (a ≫ l ≫ p) ≤ Dynamic.centralizer ζ :=
    range_le_centralizer_groupHom_comp (a ≫ l ≫ p) (-mu)
  let j := hZ.factorHom (a ≫ l ≫ p) hcent
  have hj : j ≫ Dynamic.Affine.centralizerHom ζ = a ≫ l ≫ p := hZ.factorHom_comp _ _
  let f := r.oppositeAdmissibleParabolicFactor hG mu hmu
  have hf : f ≫ Dynamic.Affine.parabolicHom ζ = p :=
    r.oppositeAdmissibleParabolicFactor_comp hG mu hmu
  have hcomp : (a ≫ l) ≫ f = j ≫ Dynamic.centralizerToParabolic hQ hZ := by
    apply hQ.hom_ext
    simp only [Category.assoc, hf, Dynamic.centralizerToParabolic_comp, hj]
  have hdet : characterRestrict j ((Dynamic.centralizerAdjointAction hZ hU).determinantCharacter c) =
      positiveWeightCharacter (a ≫ l ≫ p) (-mu) :=
    characterRestrict_centralizerAdjointDeterminant
      r.isCompatible.splitComponent.1.isSplitSubtorus.1 (a ≫ l ≫ p) (-mu) hZ hU j hj c
  change characterRestrict (a ≫ l) (-characterRestrict f
    (Dynamic.adjointDeterminantCharacter hQ hU c)) = _
  rw [map_neg, ← AddMonoidHom.comp_apply, ← characterRestrict_comp, hcomp,
    characterRestrict_comp, AddMonoidHom.comp_apply,
    Dynamic.adjointDeterminantCentralizerRestriction ζ hQ hZ hU c, hdet,
    r.positiveWeightCharacter_neg_splitComponent hG, neg_neg]

end Langlands.GroupScheme.ParabolicRootPresentation

namespace Langlands.Global.RepresentationGrowth

open Langlands.GroupScheme AdelicGroupPoints

private theorem height_eval_neg_characterRestrict
    {F : Type u} [Field F] [NumberField F]
    {G P Q : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffine G.X.left] [IsAffine P.X.left] [IsAffine Q.X.left]
    {p : P ⟶ G} {q : Q ⟶ G}
    [IsClosedImmersion p.hom.hom.left] [IsClosedImmersion q.hom.hom.left]
    {K : Subgroup (AdelicGroupPoints F G)}
    (hP : IsIwasawaCompact p K) (hQ : IsIwasawaCompact q K)
    (f : P ⟶ Q) (hf : f ≫ q = p) (χ : rationalCharacters Q)
    (x : AdelicGroupPoints F G) :
    hP.height x (-characterRestrict f χ) = -hQ.height x χ := by
  obtain ⟨y, k, hk, hy⟩ := hP.exists_eq x
  have hyQ : map F Q G q (map F P Q f y) * k = x := by
    rw [← map_comp_apply_of_hom, hf, hy]
  rw [hP.height_eq hk hy, hQ.height_eq hk hyQ, characterLog_map]
  let L : rationalCharacters P →+ ℝ := characterLog F P y
  change L (-characterRestrict f χ) = -L (characterRestrict f χ)
  exact L.map_neg _

variable {F : Type u} [Field F] [NumberField F] {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G P M : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [IsAffine G.X.left] [IsAffine P.X.left] [LocallyOfFiniteType G.X.hom]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a) {K : Subgroup (AdelicGroupPoints F G)}

set_option maxHeartbeats 600000 in
/-- Every opposite-admissible positive-weight character has a uniform lower
Iwasawa bound on the rational points. -/
theorem exists_le_height_oppositeAdmissibleWeightCharacter
    (hK : IsIwasawaCompact p K) (hG : IsConnectedReductive G) (mu : cocharacterLattice A)
    (hmu : IsOppositeIntersectionAdmissible (a ≫ l ≫ p)
      r.splitComponentCocharacter (-r.splitComponentCocharacter) mu) :
    ∃ D : ℝ, ∀ x : RationalGroupPoints F G, -D ≤
      hK.height (rational F G x) (r.oppositeAdmissibleWeightCharacter hG mu hmu) := by
  let ζ := CommGroupScheme.groupHom (-mu) ≫ a ≫ l ≫ p
  let Q := Dynamic.Affine.parabolicScheme ζ
  let q := Dynamic.Affine.parabolicHom ζ
  let f := r.oppositeAdmissibleParabolicFactor hG mu hmu
  have hf : f ≫ q = p := r.oppositeAdmissibleParabolicFactor_comp hG mu hmu
  let hQ := Dynamic.Affine.isRepresentedBy_parabolicHom ζ
  let hU := Dynamic.Affine.isRepresentedBy_unipotentHom ζ
  let : IsClosedImmersion q.hom.hom.left := Dynamic.Affine.isClosedSubgroup_parabolicHom ζ
  let : IsAffineHom Q.X.hom := (Dynamic.Affine.isClosedSubgroup_parabolicHom ζ).isAffineHom
  let : IsAffine Q.X.left := isAffine_of_isAffineHom Q.X.hom
  let : IsAffineHom (Dynamic.Affine.unipotentScheme ζ).X.hom :=
    (Dynamic.Affine.isClosedSubgroup_unipotentHom ζ).isAffineHom
  let : LocallyOfFiniteType (Dynamic.Affine.unipotentScheme ζ).X.hom :=
    (Dynamic.Affine.isClosedSubgroup_unipotentHom ζ).locallyOfFiniteType
  have hK' : IsIwasawaCompact (f ≫ q) K := by rw [hf]; exact hK
  have hKQ := IsIwasawaCompact.of_comp f hK'
  let det := Dynamic.Affine.adjointDeterminant ζ
  have hbound : ∃ D : ℝ, ∀ x : RationalGroupPoints F G, hKQ.height (rational F G x) det ≤ D :=
    exists_height_adjointDeterminant_le (Lie.finiteCoordinates G)
      (Lie.finiteCoordinates (Dynamic.Affine.unipotentScheme ζ)) hKQ hQ hU
  obtain ⟨D, hD⟩ := hbound
  refine ⟨D, fun x => ?_⟩
  change -D ≤ hK.height (rational F G x) (-characterRestrict f det)
  rw [height_eval_neg_characterRestrict hK hKQ f hf]
  exact neg_le_neg (hD x)

end Langlands.Global.RepresentationGrowth
