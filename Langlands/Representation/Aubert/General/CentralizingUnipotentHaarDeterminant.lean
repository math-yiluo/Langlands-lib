import Langlands.GroupScheme.Dynamic.CommonCentralizerDeterminantBalance
import Langlands.GroupScheme.Dynamic.AdjointDeterminantFunctorialityProof
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.Representation.Aubert.General.DynamicUnipotentHaarDeterminantProof

/-! # Haar determinants for homomorphisms into a dynamic centralizer -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.Dynamic

section Actions

variable {S : Scheme.{u}} {G Z M U : GroupScheme S}
  (chi : (Gm S).toGrp ⟶ G) (iZ : Z ⟶ G)
  {iM : M ⟶ G} {iU : U ⟶ G}
  (hZ : SubgroupFunctor.range iZ ≤ centralizer chi)
  (hM : (centralizer chi).IsRepresentedBy iM)
  (hU : (unipotent chi).IsRepresentedBy iU)
  (f : Z ⟶ M) (hf : f ≫ iM = iZ)

include hf

/-- The actual action of a centralizing homomorphism is the restriction of
the action of any represented full centralizer through its factorization. -/
theorem centralizerAdjointAction_restrict_eq_centralizingUnipotentAction :
    (centralizerAdjointAction hM hU).restrict f =
      centralizingUnipotentAction chi iZ hZ hU := by
  have : Mono iU.hom.hom := hU.1
  apply AutomorphicAction.ext_act
  intro X z x
  apply (cancel_mono iU.hom.hom).mp
  rw [AutomorphicAction.restrict_act, centralizerAdjointAction_act_comp,
    centralizingUnipotentAction_act_comp, Category.assoc, ← Grp.comp_hom_hom, hf]

end Actions

section Determinants

variable {R : CommRingCat.{u}} {G Z M U : GroupScheme (Spec R)}
  [IsAffine Z.X.left] [IsAffine M.X.left] [IsAffineHom U.X.hom]
  (chi : (Gm (Spec R)).toGrp ⟶ G) (iZ : Z ⟶ G)
  {iM : M ⟶ G} {iU : U ⟶ G}
  (hZ : SubgroupFunctor.range iZ ≤ centralizer chi)
  (hM : (centralizer chi).IsRepresentedBy iM)
  (hU : (unipotent chi).IsRepresentedBy iU)
  (f : Z ⟶ M) (hf : f ≫ iM = iZ)

include hf

/-- The full-centralizer determinant restricts to the actual smaller-group
determinant in the same finite Lie coordinates. -/
theorem characterRestrict_centralizerAdjointDeterminant_eq_centralizing
    {d : ℕ} (c : Lie.FiniteCoordinates U d) :
    characterRestrict f ((centralizerAdjointAction hM hU).determinantCharacter c) =
      (centralizingUnipotentAction chi iZ hZ hU).determinantCharacter c := by
  rw [AutomorphicAction.determinantCharacter_restrict,
    centralizerAdjointAction_restrict_eq_centralizingUnipotentAction
      chi iZ hZ hM hU f hf]

end Determinants

section RationalPoints

variable {k : Type u} [Field k] {G Z : GroupScheme (Spec (CommRingCat.of k))}
  (chi : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) (iZ : Z ⟶ G)
  (hZ : SubgroupFunctor.range iZ ≤ centralizer chi)

/-- The actual rational-point map of a centralizing homomorphism, with
codomain restricted to the normalizer of the dynamic unipotent subgroup. -/
def centralizingUnipotentNormalizerHom :
    rationalPoints Z →*
      Subgroup.normalizer ((unipotent chi).carrier (Over.mk (𝟙 _)) : Set (rationalPoints G)) :=
  (rationalPoints.map iZ).codRestrict _
    (fun z => centralizer_le_normalizer_unipotent chi _ (hZ _ ⟨z, rfl⟩))

theorem centralizingUnipotentNormalizerHom_coe (z : rationalPoints Z) :
    (centralizingUnipotentNormalizerHom chi iZ hZ z : rationalPoints G) =
      z ≫ iZ.hom.hom := rfl

end RationalPoints

end Langlands.GroupScheme.Dynamic

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsConnectedReductive G)

/-- The exact Haar determinant formula remains valid when the acting
homomorphism only has range contained in the dynamic centralizer. -/
theorem centralizingUnipotentHaarDeterminant :
    haveI := hG.isAffineHom
    letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
    ∀ [LocallyCompactSpace (RationalPoint k G.X)]
      [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
      (chi : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
      {Z U : GroupScheme (Spec (CommRingCat.of k))} (iZ : Z ⟶ G) {iU : U ⟶ G}
      (hZ : SubgroupFunctor.range iZ ≤ Dynamic.centralizer chi)
      (hU : (Dynamic.unipotent chi).IsRepresentedBy iU)
      [IsAffine Z.X.left] [IsAffineHom U.X.hom]
      {d : ℕ} (c : Lie.FiniteCoordinates U d)
      (hUc : IsClosed ((Dynamic.unipotent chi).carrier (Over.mk (𝟙 _)) :
        Set (RationalPoint k G.X)))
      (m : rationalPoints Z),
      (HaarModulus.closedNormalizerCharacter _ hUc
        (Dynamic.centralizingUnipotentNormalizerHom chi iZ hZ m) : ℝ≥0) =
      MeasureTheory.distribHaarChar k
        (rationalCharacterEval
          ((Dynamic.centralizingUnipotentAction chi iZ hZ hU).determinantCharacter c) m) := by
  intro _ _ _ chi Z U iZ iU hZ hU _ _ d c hUc m
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let _ : TopologicalSpace (RationalPoint k G.X) := pointTopology
  let M := Dynamic.Affine.centralizerScheme chi
  let iM := Dynamic.Affine.centralizerHom chi
  have hM : (Dynamic.centralizer chi).IsRepresentedBy iM :=
    Dynamic.Affine.isRepresentedBy_centralizerHom chi
  have : IsClosedImmersion iM.hom.hom.left :=
    Dynamic.Affine.isClosedSubgroup_centralizerHom chi
  have : IsAffine M.X.left := isAffine_of_isAffineHom iM.hom.hom.left
  let f : Z ⟶ M := hM.factorHom iZ hZ
  have hf : f ≫ iM = iZ := hM.factorHom_comp iZ hZ
  have hm : rationalPoints.map f m ≫ iM.hom.hom = m ≫ iZ.hom.hom := by
    change (m ≫ f.hom.hom) ≫ iM.hom.hom = _
    rw [Category.assoc, ← Grp.comp_hom_hom, hf]
  have hmn : rationalPoints.map f m ≫ iM.hom.hom ∈
      Subgroup.normalizer ((Dynamic.unipotent chi).carrier (Over.mk (𝟙 _)) :
        Set (RationalPoint k G.X)) := by
    rw [hm]
    exact (Dynamic.centralizingUnipotentNormalizerHom chi iZ hZ m).property
  have h := dynamicUnipotentHaarDeterminant k G hG chi hM hU c hUc
    (rationalPoints.map f m) hmn
  rw [← rationalCharacterEval_characterRestrict,
    Dynamic.characterRestrict_centralizerAdjointDeterminant_eq_centralizing
      chi iZ hZ hM hU f hf] at h
  have heq : (⟨rationalPoints.map f m ≫ iM.hom.hom, hmn⟩ :
      Subgroup.normalizer ((Dynamic.unipotent chi).carrier (Over.mk (𝟙 _)) :
        Set (RationalPoint k G.X))) =
      Dynamic.centralizingUnipotentNormalizerHom chi iZ hZ m := by
    apply Subtype.ext
    exact hm
  rw [heq] at h
  exact h

end Langlands.Aubert.General.RationalPointFamily
