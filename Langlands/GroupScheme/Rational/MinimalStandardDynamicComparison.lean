import Langlands.GroupScheme.Rational.EndpointReductions
import Langlands.GroupScheme.Rational.GenericCentralizerProof
import Langlands.GroupScheme.Rational.PositiveRootInduction
import Langlands.GroupScheme.Rational.RelativeRootSignInclusionsProof
import Langlands.GroupScheme.Rational.StandardRepresentability
import Langlands.GroupScheme.Dynamic.AffineRepresentability

/-! # The empty-index standard subgroups and a generic cocharacter -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- An empty-index standard cocharacter is positive on every positive relative
root, by induction on the original positive integer pairing. -/
theorem IsStandardCocharacter.pairing_pos_of_positive_empty
    {eta : cocharacterLattice T} (heta : IsStandardCocharacter i ν ∅ eta)
    {α : characterLattice T} (hα : α ∈ positiveRelativeRoots i ν) :
    0 < latticePairing T α eta := by
  apply positiveRelativeRoots_induction i ν
    (P := fun α => 0 < latticePairing T α eta) (hα := hα)
  · intro β hβ
    exact heta.2.2 β hβ (by simp)
  · intro β hβroot δ hδroot hβ hδ
    simpa using add_pos hβ hδ

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)

include hG hi hν

/-- For a generic cocharacter, the empty-index standard parabolic is its
dynamic parabolic on all test schemes. -/
theorem standardParabolic_empty_eq_dynamic_of_generic :
    standardParabolic i ν ∅ = Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) := by
  refine le_antisymm (standardParabolic_empty_le i ν) ?_
  intro U g hg
  rw [mem_standardParabolic]
  intro eta heta
  apply ((relativeRootSignInclusions k G hG T i hi ν eta).1.mpr ?_) U hg
  intro α hα hnonneg
  have hpositive : 0 < latticePairing T α ν := by
    have hne := hν α hα
    omega
  exact heta.pairing_nonneg_of_positive i ν ⟨hα, hpositive⟩

omit hν in
/-- The empty-index standard unipotent functor is the dynamic unipotent
functor of the cocharacter specifying positivity, on all test schemes. -/
theorem standardUnipotent_empty_eq_dynamic :
    standardUnipotent i ν ∅ = Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i) := by
  refine le_antisymm
    (standardUnipotent_le_dynamicUnipotent i ν (isStandardCocharacter_empty_self i ν)) ?_
  intro U g hg
  rw [mem_standardUnipotent]
  intro eta heta
  apply ((relativeRootSignInclusions k G hG T i hi ν eta).2 ?_) U hg
  intro α hα hpositive
  exact heta.pairing_pos_of_positive_empty i ν ⟨hα, hpositive⟩

/-- The empty-index standard Levi is the full centralizer of the maximal split
torus. This uses the published unconditional generic-centralizer theorem. -/
theorem standardLevi_empty_eq_torusCentralizer_of_generic :
    standardLevi i ν ∅ = torusCentralizer i :=
  standardLevi_empty_of_genericCentralizer i ν (genericCentralizer k G hG T i hi ν hν)

namespace Standard

variable [IsAffine G.X.left]

/-- The actual canonical standard parabolic is isomorphic, over the ambient
group, to the affine representative of the dynamic parabolic of `ν`. -/
def emptyParabolicDynamicIso :
    parabolicScheme i ν ∅ ≅
      Dynamic.Affine.parabolicScheme (CommGroupScheme.groupHom ν ≫ i) :=
  (isRepresentedBy_parabolicHom i ν ∅).isoOfIsRepresentedBy
    ((standardParabolic_empty_eq_dynamic_of_generic i ν hG hi hν).symm ▸
      Dynamic.Affine.isRepresentedBy_parabolicHom (CommGroupScheme.groupHom ν ≫ i))

@[simp] theorem emptyParabolicDynamicIso_hom_comp :
    (emptyParabolicDynamicIso i ν hG hi hν).hom ≫
        Dynamic.Affine.parabolicHom (CommGroupScheme.groupHom ν ≫ i) =
      parabolicHom i ν ∅ :=
  SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

omit hν in
/-- The actual canonical standard unipotent group is isomorphic, over the
ambient group, to the affine representative of the dynamic unipotent functor. -/
def emptyUnipotentDynamicIso :
    unipotentScheme i ν ∅ ≅
      Dynamic.Affine.unipotentScheme (CommGroupScheme.groupHom ν ≫ i) :=
  (isRepresentedBy_unipotentHom i ν ∅).isoOfIsRepresentedBy
    ((standardUnipotent_empty_eq_dynamic i ν hG hi).symm ▸
      Dynamic.Affine.isRepresentedBy_unipotentHom (CommGroupScheme.groupHom ν ≫ i))

omit hν in
@[simp] theorem emptyUnipotentDynamicIso_hom_comp :
    (emptyUnipotentDynamicIso i ν hG hi).hom ≫
        Dynamic.Affine.unipotentHom (CommGroupScheme.groupHom ν ≫ i) =
      unipotentHom i ν ∅ :=
  SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

end Standard

end Langlands.GroupScheme
