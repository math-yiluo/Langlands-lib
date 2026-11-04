import Langlands.GroupScheme.Rational.ParabolicRootRadicals
import Langlands.GroupScheme.Rational.RelativeTitsNondegeneracy
import Langlands.Representation.Aubert.General.RationalOppositeParabolic

/-! # Opposite dynamic models with the specified Levi and full root support -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.ParabolicRootPresentation

variable {k : Type u} [Field k]
  {A : CommGroupScheme (Spec (CommRingCat.of k))}
  {G M P : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

/-- Parameter reversal preserves the exact specified Levi image. -/
theorem levi_eq_neg_splitComponentCocharacter :
    SubgroupFunctor.range (l ≫ p) =
      Dynamic.centralizer
        (CommGroupScheme.groupHom (-r.splitComponentCocharacter) ≫ a ≫ l ≫ p) := by
  rw [groupHom_neg_comp_eq_oppositeCocharacter]
  change SubgroupFunctor.range (l ≫ p) =
    Dynamic.centralizer (Dynamic.inverseCocharacter
      (CommGroupScheme.groupHom r.splitComponentCocharacter ≫ a ≫ l ≫ p))
  rw [Dynamic.centralizer_inverseCocharacter]
  exact r.levi_eq_splitComponentCocharacter

/-- The negative dynamic parabolic and radical with the literal supplied Levi.
Closedness and decomposition are intrinsic; algebraic parabolicity is separate. -/
def oppositeDecompositionModel :
    SubgroupFunctor.ClosedDecompositionModel
      (Dynamic.parabolic
        (CommGroupScheme.groupHom (-r.splitComponentCocharacter) ≫ a ≫ l ≫ p))
      (SubgroupFunctor.range (l ≫ p))
      (Dynamic.unipotent
        (CommGroupScheme.groupHom (-r.splitComponentCocharacter) ≫ a ≫ l ≫ p)) := by
  let χ := CommGroupScheme.groupHom (-r.splitComponentCocharacter) ≫ a ≫ l ≫ p
  let := (r.isCompatible.levi.isClosedSubgroup.comp
    r.isCompatible.parabolic.isClosedSubgroup).mono
  let hP := Dynamic.Affine.isRepresentedBy_parabolicHom χ
  let hZ : (Dynamic.centralizer χ).IsRepresentedBy (l ≫ p) :=
    ⟨Over.mono_of_mono_left _, r.levi_eq_neg_splitComponentCocharacter⟩
  let hU := Dynamic.Affine.isRepresentedBy_unipotentHom χ
  let ln := Dynamic.centralizerToParabolic hP hZ
  let un := Dynamic.unipotentToParabolic hP hU
  have hln : ln ≫ Dynamic.Affine.parabolicHom χ = l ≫ p :=
    Dynamic.centralizerToParabolic_comp hP hZ
  have hun : un ≫ Dynamic.Affine.parabolicHom χ = Dynamic.Affine.unipotentHom χ :=
    Dynamic.unipotentToParabolic_comp hP hU
  refine
    { parabolic := Dynamic.Affine.parabolicScheme χ
      levi := M
      unipotent := Dynamic.Affine.unipotentScheme χ
      parabolicHom := Dynamic.Affine.parabolicHom χ
      leviHom := ln
      unipotentHom := un
      parabolic_rep := hP
      levi_rep := ?_
      unipotent_rep := ?_
      parabolic_closed := Dynamic.Affine.isClosedSubgroup_parabolicHom χ
      levi_closed := ?_
      unipotent_closed := ?_
      multiplication_isIso := Dynamic.isIso_subgroupMultiplication hP hZ hU ln un hln hun
      pointwise := ?_ }
  · rw [hln]
    exact ⟨Over.mono_of_mono_left _, rfl⟩
  · rwa [hun]
  · apply IsClosedSubgroup.of_comp (Dynamic.Affine.isClosedSubgroup_parabolicHom χ)
    rw [hln]
    exact r.isCompatible.levi.isClosedSubgroup.comp r.isCompatible.parabolic.isClosedSubgroup
  · apply IsClosedSubgroup.of_comp (Dynamic.Affine.isClosedSubgroup_parabolicHom χ)
    rw [hun]
    exact Dynamic.Affine.isClosedSubgroup_unipotentHom χ
  · intro T
    rw [r.levi_eq_neg_splitComponentCocharacter]
    exact ⟨Dynamic.unipotent_le_parabolic χ T, Dynamic.centralizer_le_parabolic χ T,
      Dynamic.unipotent_subgroupOf_parabolic_normal χ T,
      Dynamic.isComplement'_unipotent_centralizer_of_isSeparated χ T,
      Dynamic.parabolic_eq_centralizer_mul_unipotent χ T⟩

/-- The model's Levi inclusion has exactly the original ambient composite. -/
theorem oppositeDecompositionModel_leviHom_comp :
    r.oppositeDecompositionModel.leviHom ≫ r.oppositeDecompositionModel.parabolicHom =
      l ≫ p := by
  exact Dynamic.centralizerToParabolic_comp _ _

section Smooth

variable [Smooth G.X.hom]

/-- Reductivity of the specified Levi identifies the actual negative dynamic
radical, without a universal centralizer theorem. -/
theorem isGeometricUnipotentRadical_oppositeModel :
    IsGeometricUnipotentRadical r.oppositeDecompositionModel.unipotentHom := by
  let := (r.isCompatible.levi.isClosedSubgroup.comp
    r.isCompatible.parabolic.isClosedSubgroup).mono
  exact Dynamic.isGeometricUnipotentRadical_of_centralizer
    _ (l ≫ p) r.oppositeDecompositionModel.parabolicHom
    r.oppositeDecompositionModel.unipotentHom
    r.oppositeDecompositionModel.parabolic_rep r.oppositeDecompositionModel.unipotent_rep
    ⟨Over.mono_of_mono_left _, r.levi_eq_neg_splitComponentCocharacter⟩
    r.isCompatible.levi.isConnectedReductive

/-- The model radical is greatest both over the ground field and over its
algebraic closure, in the rational-Levi interface. -/
theorem leviSubgroup_isGeometricUnipotentRadical_oppositeModel :
    LeviSubgroup.IsGeometricUnipotentRadical
      r.oppositeDecompositionModel.unipotentHom := by
  let : IsAffineHom r.oppositeDecompositionModel.parabolic.X.hom := by
    exact Dynamic.Affine.isClosedSubgroup_parabolicHom
      (CommGroupScheme.groupHom (-r.splitComponentCocharacter) ≫ a ≫ l ≫ p) |>.isAffineHom
  exact r.isGeometricUnipotentRadical_oppositeModel.leviSubgroup_of_unipotentFieldExtension
    unipotentFieldExtensionStatement

variable {Q V : GroupScheme (Spec (CommRingCat.of k))} {q : Q ⟶ G}

/-- Every supplied geometric radical of a representative of the negative
dynamic parabolic has the same full ambient image. -/
theorem range_comp_oppositeRadical_eq
    (hQ : (Dynamic.parabolic
      (CommGroupScheme.groupHom (-r.splitComponentCocharacter) ≫ a ≫ l ≫ p)).IsRepresentedBy q)
    {v : V ⟶ Q} (hv : LeviSubgroup.IsGeometricUnipotentRadical v) :
    SubgroupFunctor.range (v ≫ q) =
      Dynamic.unipotent
        (CommGroupScheme.groupHom (-r.splitComponentCocharacter) ≫ a ≫ l ≫ p) := by
  let := (r.isCompatible.levi.isClosedSubgroup.comp
    r.isCompatible.parabolic.isClosedSubgroup).mono
  exact Dynamic.range_comp_radical_eq_unipotent_of_reductive_centralizer
    _ hQ ⟨Over.mono_of_mono_left _, r.levi_eq_neg_splitComponentCocharacter⟩
    r.isCompatible.levi.isConnectedReductive hv

/-- The full support of every supplied negative radical is the negative
cocharacter's positive-root set. -/
theorem subgroupRelativeRoots_oppositeRadical
    (hQ : (Dynamic.parabolic
      (CommGroupScheme.groupHom (-r.splitComponentCocharacter) ≫ a ≫ l ≫ p)).IsRepresentedBy q)
    {v : V ⟶ Q} (hv : LeviSubgroup.IsGeometricUnipotentRadical v) :
    RelativeRoot.subgroupRelativeRoots (a ≫ l ≫ p) (SubgroupFunctor.range (v ≫ q)) =
      positiveRelativeRoots (a ≫ l ≫ p) (-r.splitComponentCocharacter) := by
  rw [r.range_comp_oppositeRadical_eq hQ hv]
  exact RelativeRoot.subgroupRelativeRoots_dynamicUnipotent _
    r.isCompatible.splitComponent.1.isSplitSubtorus.1 _

variable {P' U : GroupScheme (Spec (CommRingCat.of k))}
  {p' : P' ⟶ G} {l' : M ⟶ P'}
  (r' : ParabolicRootPresentation p' l' a)

/-- The complete actual root intersection for a common specified Levi, using
any supplied positive and negative geometric radicals. -/
theorem intertwiningRelativeRoots_commonLevi
    (hM : l ≫ p = l' ≫ p')
    {n : U ⟶ P} (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
    (hQ : (Dynamic.parabolic
      (CommGroupScheme.groupHom (-r'.splitComponentCocharacter) ≫ a ≫ l' ≫ p')).IsRepresentedBy q)
    {v : V ⟶ Q} (hv : LeviSubgroup.IsGeometricUnipotentRadical v) :
    RelativeRoot.intertwiningRelativeRoots (a ≫ l ≫ p)
        (SubgroupFunctor.range (n ≫ p)) (SubgroupFunctor.range (v ≫ q)) =
      {α | α ∈ relativeRoots (a ≫ l ≫ p) ∧
        0 < latticePairing A α r.splitComponentCocharacter ∧
        latticePairing A α r'.splitComponentCocharacter < 0} := by
  rw [r.range_comp_radical_eq hn, r'.range_comp_oppositeRadical_eq hQ hv, ← hM]
  exact RelativeRoot.intertwiningRelativeRoots_dynamic _
    r.isCompatible.splitComponent.1.isSplitSubtorus.1 _ _

end Smooth

end Langlands.GroupScheme.ParabolicRootPresentation
