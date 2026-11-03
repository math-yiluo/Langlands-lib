import Langlands.GroupScheme.Rational.TorusWeightSmoothGeneral
import Langlands.GroupScheme.CorepresentedSmooth
import Langlands.GroupScheme.IdentityComponent
import Langlands.GroupScheme.Rational.TangentImage
import Langlands.GroupScheme.Lie.SmoothDifferential
import Langlands.GroupScheme.Dynamic.ParabolicLieCriterion

/-! # The connected representative of a coordinate weight subgroup -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

namespace RelativeRoot

variable {k : Type u} [Field k]
    {H G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [IsAffineHom G.X.hom]
    (j : H ⟶ G) [Mono j.hom.hom]

/-- Passing to the actual identity component of a smooth affine subgroup
preserves its intrinsic tangent image in the ambient group. -/
theorem tangentSubmodule_range_identityComponent_comp :
    tangentSubmodule (SubgroupFunctor.range (identityComponentι H ≫ j)) =
      tangentSubmodule (SubgroupFunctor.range j) := by
  apply le_antisymm
  · exact tangentSubmodule_mono (SubgroupFunctor.range_comp_le _ _)
  · intro X hX
    rw [tangentSubmodule_range j] at hX
    obtain ⟨Y, rfl⟩ := hX
    obtain ⟨Z, hZ⟩ := Lie.targetMapLinear_surjective_of_smooth
      (identityComponentι H) k (inferInstance : Smooth (identityComponentι H).hom.hom.left) Y
    refine ⟨Z.toMul.val, ?_⟩
    change Z.toMul.val ≫ (identityComponentι H ≫ j).hom.hom =
      Y.toMul.val ≫ j.hom.hom
    rw [Grp.comp_hom_hom, ← Category.assoc]
    exact congrArg (fun W : Additive (lieKernel H k) => W.toMul.val ≫ j.hom.hom) hZ

end RelativeRoot

namespace Corepresented

variable {k : Type u} [Field k]
    {F : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}}
    {B : CommAlgCat.{u} (CommRingCat.of k)}
    (e : (F ⋙ forget GrpCat).CorepresentableBy B)
    {I : Type u} [Fintype I] [DecidableEq I] (σ : TorusAction F I)
    [Algebra.FormallySmooth k B] [Algebra.FiniteType k B]
    (P : AddSubsemigroup (I → ℤ))

local instance : IsAffine (groupScheme F e).X.left :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of B)))

local instance : IsAffineHom (groupScheme F e).X.hom :=
  isAffineHom_of_isAffine _

local instance : IsAffine (cutGroupScheme (isCutOutBy_weightIdeal e σ P)).X.left :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of (B ⧸ weightIdeal e σ P))))

local instance : IsAffineHom (cutGroupScheme (isCutOutBy_weightIdeal e σ P)).X.hom :=
  isAffineHom_of_isAffine _

/-- The coordinate weight subgroup is smooth for every additive semigroup. -/
instance smooth_weightCutGroupScheme :
    Smooth (cutGroupScheme (isCutOutBy_weightIdeal e σ P)).X.hom := by
  let : Algebra.Smooth k (B ⧸ weightIdeal e σ P) := smooth_quotient_weightIdeal e σ P
  exact smooth_cutGroupScheme (isCutOutBy_weightIdeal e σ P)

/-- The actual identity component of the smooth affine coordinate weight
subgroup. Its quotient representative is the existing `cutGroupScheme`. -/
abbrev connectedWeightGroupScheme : GroupScheme (Spec (CommRingCat.of k)) :=
  identityComponent (cutGroupScheme (isCutOutBy_weightIdeal e σ P))

/-- The inclusion of the connected coordinate weight subgroup in the
original corepresented group scheme. -/
def connectedWeightHom : connectedWeightGroupScheme e σ P ⟶ groupScheme F e :=
  identityComponentι (cutGroupScheme (isCutOutBy_weightIdeal e σ P)) ≫
    cutHom (isCutOutBy_weightIdeal e σ P)

instance smooth_connectedWeightGroupScheme :
    Smooth (connectedWeightGroupScheme e σ P).X.hom := inferInstance

instance isAffineHom_connectedWeightGroupScheme :
    IsAffineHom (connectedWeightGroupScheme e σ P).X.hom := inferInstance

instance connectedSpace_connectedWeightGroupScheme :
    ConnectedSpace (connectedWeightGroupScheme e σ P).X.left := inferInstance

instance geometricallyConnected_connectedWeightGroupScheme :
    GeometricallyConnected (connectedWeightGroupScheme e σ P).X.hom := inferInstance

instance isClosedImmersion_connectedWeightHom :
    IsClosedImmersion (connectedWeightHom e σ P).hom.hom.left := by
  change IsClosedImmersion
    ((identityComponentι (cutGroupScheme (isCutOutBy_weightIdeal e σ P))).hom.hom.left ≫
      (cutHom (isCutOutBy_weightIdeal e σ P)).hom.hom.left)
  infer_instance

instance mono_connectedWeightHom : Mono (connectedWeightHom e σ P).hom.hom := by
  change Mono
    ((identityComponentι (cutGroupScheme (isCutOutBy_weightIdeal e σ P))).hom.hom ≫
      (cutHom (isCutOutBy_weightIdeal e σ P)).hom.hom)
  infer_instance

/-- The connected representative is a closed subgroup of the original group. -/
theorem isClosedSubgroup_connectedWeightHom : IsClosedSubgroup (connectedWeightHom e σ P) :=
  inferInstanceAs (IsClosedImmersion (connectedWeightHom e σ P).hom.hom.left)

/-- Its all-test range lies in the original coordinate weight subgroup. -/
theorem range_connectedWeightHom_le :
    SubgroupFunctor.range (connectedWeightHom e σ P) ≤
      cutSubgroupFunctor (isCutOutBy_weightIdeal e σ P) := by
  rw [← range_cutHom]
  exact SubgroupFunctor.range_comp_le _ _

/-- The all-test range is a smooth connected closed represented subgroup. -/
theorem isSmoothConnectedClosed_range_connectedWeightHom :
    RelativeRoot.IsSmoothConnectedClosed (SubgroupFunctor.range (connectedWeightHom e σ P)) :=
  ⟨connectedWeightGroupScheme e σ P, connectedWeightHom e σ P,
    ⟨inferInstance, rfl⟩, isClosedSubgroup_connectedWeightHom e σ P,
    inferInstance, inferInstance⟩

/-- The connected coordinate representative has exactly the tangent image
of the whole coordinate weight subgroup. -/
theorem tangentSubmodule_range_connectedWeightHom :
    RelativeRoot.tangentSubmodule (SubgroupFunctor.range (connectedWeightHom e σ P)) =
      RelativeRoot.tangentSubmodule (cutSubgroupFunctor (isCutOutBy_weightIdeal e σ P)) := by
  rw [← range_cutHom]
  exact RelativeRoot.tangentSubmodule_range_identityComponent_comp _

section Factor

variable {K : GroupScheme (Spec (CommRingCat.of k))} [ConnectedSpace K.X.left]
    (f : K ⟶ groupScheme F e)
    (hf : SubgroupFunctor.range f ≤ cutSubgroupFunctor (isCutOutBy_weightIdeal e σ P))

/-- Factor a homomorphism from a connected group scheme through the
connected coordinate weight subgroup when its all-test range lies in the
coordinate weight subgroup. -/
def connectedWeightFactor : K ⟶ connectedWeightGroupScheme e σ P :=
  IdentityComponent.factor _
    ((isRepresentedBy_cutHom (isCutOutBy_weightIdeal e σ P)).liftOfLE f hf)

@[reassoc (attr := simp)]
theorem connectedWeightFactor_comp :
    connectedWeightFactor e σ P f hf ≫ connectedWeightHom e σ P = f := by
  rw [connectedWeightHom, ← Category.assoc, connectedWeightFactor,
    IdentityComponent.factor_identityComponentι, SubgroupFunctor.IsRepresentedBy.liftOfLE_comp]

include hf

/-- Every connected subgroup with range in the coordinate weight subgroup
has range in its connected representative. -/
theorem range_le_connectedWeightHom :
    SubgroupFunctor.range f ≤ SubgroupFunctor.range (connectedWeightHom e σ P) := by
  rw [← connectedWeightFactor_comp e σ P f hf]
  exact SubgroupFunctor.range_comp_le _ _

/-- The factorization through the connected coordinate representative is unique. -/
theorem existsUnique_connectedWeightFactor :
    ∃! g : K ⟶ connectedWeightGroupScheme e σ P,
      g ≫ connectedWeightHom e σ P = f := by
  refine ⟨connectedWeightFactor e σ P f hf, connectedWeightFactor_comp e σ P f hf, ?_⟩
  intro g hg
  apply Grp.hom_ext
  apply (cancel_mono (connectedWeightHom e σ P).hom.hom).mp
  exact congrArg (fun h => h.hom.hom)
    (hg.trans (connectedWeightFactor_comp e σ P f hf).symm)

end Factor

end Corepresented
end Langlands.GroupScheme
