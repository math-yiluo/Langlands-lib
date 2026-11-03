import Langlands.GroupScheme.Rational.TorusActualWeightSubgroup
import Langlands.GroupScheme.Rational.TorusWeightRepresentative
import Langlands.GroupScheme.IdentityComponentAction

/-! # Connected coordinate weight subgroups in the original group -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.TorusActionCoordinates

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    [Smooth G.X.hom]
    {I : Type u} [Fintype I] [DecidableEq I]
    (b : AutomorphicAction S.toGrp G)
    (e : S.toGrp ≅ splitTorus (Spec (CommRingCat.of k)) I)

/-- Smoothness of the original group gives smoothness of its actual coordinate algebra. -/
theorem smooth_coordinateAlgebra : Algebra.Smooth k (Lie.coordinateAlgebra G) := by
  apply (Corepresented.smooth_groupScheme_iff (e := corepresentation G)).mp
  have : IsIso (groupSchemeIso G).hom.hom.hom.left :=
    (inferInstance : IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso
      (groupSchemeIso G))).hom)
  rw [← Over.w (groupSchemeIso G).hom.hom.hom]
  infer_instance

local instance : Algebra.Smooth k (Lie.coordinateAlgebra G) := smooth_coordinateAlgebra

local instance : Algebra.FiniteType k (Lie.coordinateAlgebra G) :=
  Lie.coordinateAlgebraFiniteType G

instance isAffine_weightGroupScheme (A : AddSubsemigroup (characterLattice S)) :
    IsAffine (weightGroupScheme b e A).X.left :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of
    (Lie.coordinateAlgebra G ⧸ Corepresented.weightIdeal (corepresentation G)
      (b.toCorepresentedTorusAction e) (exponentSemigroup e A)))))

instance isAffineHom_weightGroupScheme (A : AddSubsemigroup (characterLattice S)) :
    IsAffineHom (weightGroupScheme b e A).X.hom :=
  isAffineHom_of_isAffine _

instance smooth_weightGroupScheme (A : AddSubsemigroup (characterLattice S)) :
    Smooth (weightGroupScheme b e A).X.hom :=
  Corepresented.smooth_weightCutGroupScheme (corepresentation G)
    (b.toCorepresentedTorusAction e) (exponentSemigroup e A)

instance isClosedImmersion_weightHom (A : AddSubsemigroup (characterLattice S)) :
    IsClosedImmersion (weightHom b e A).hom.hom.left :=
  isClosedSubgroup_weightHom b e A

instance mono_weightHom (A : AddSubsemigroup (characterLattice S)) :
    Mono (weightHom b e A).hom.hom := Over.mono_of_mono_left _

/-- The actual identity component of the coordinate quotient subgroup. -/
abbrev connectedWeightGroupScheme (A : AddSubsemigroup (characterLattice S)) :
    GroupScheme (Spec (CommRingCat.of k)) :=
  identityComponent (weightGroupScheme b e A)

/-- Its inclusion in the original ambient group. -/
def connectedWeightHom (A : AddSubsemigroup (characterLattice S)) :
    connectedWeightGroupScheme b e A ⟶ G :=
  identityComponentι (weightGroupScheme b e A) ≫ weightHom b e A

instance smooth_connectedWeightGroupScheme (A : AddSubsemigroup (characterLattice S)) :
    Smooth (connectedWeightGroupScheme b e A).X.hom := inferInstance

instance isAffineHom_connectedWeightGroupScheme (A : AddSubsemigroup (characterLattice S)) :
    IsAffineHom (connectedWeightGroupScheme b e A).X.hom := inferInstance

instance connectedSpace_connectedWeightGroupScheme (A : AddSubsemigroup (characterLattice S)) :
    ConnectedSpace (connectedWeightGroupScheme b e A).X.left := inferInstance

instance geometricallyConnected_connectedWeightGroupScheme
    (A : AddSubsemigroup (characterLattice S)) :
    GeometricallyConnected (connectedWeightGroupScheme b e A).X.hom := inferInstance

instance isClosedImmersion_connectedWeightHom (A : AddSubsemigroup (characterLattice S)) :
    IsClosedImmersion (connectedWeightHom b e A).hom.hom.left := by
  change IsClosedImmersion
    ((identityComponentι (weightGroupScheme b e A)).hom.hom.left ≫
      (weightHom b e A).hom.hom.left)
  infer_instance

instance mono_connectedWeightHom (A : AddSubsemigroup (characterLattice S)) :
    Mono (connectedWeightHom b e A).hom.hom := Over.mono_of_mono_left _

theorem isClosedSubgroup_connectedWeightHom (A : AddSubsemigroup (characterLattice S)) :
    IsClosedSubgroup (connectedWeightHom b e A) :=
  inferInstanceAs (IsClosedImmersion (connectedWeightHom b e A).hom.hom.left)

/-- This all-test range is a smooth connected closed represented subgroup. -/
theorem isSmoothConnectedClosed_range_connectedWeightHom
    (A : AddSubsemigroup (characterLattice S)) :
    RelativeRoot.IsSmoothConnectedClosed (SubgroupFunctor.range (connectedWeightHom b e A)) :=
  ⟨connectedWeightGroupScheme b e A, connectedWeightHom b e A,
    ⟨inferInstance, rfl⟩, isClosedSubgroup_connectedWeightHom b e A,
    inferInstance, inferInstance⟩

/-- The connected inclusion has the tangent image of the full coordinate subgroup. -/
theorem tangentSubmodule_range_connectedWeightHom
    (A : AddSubsemigroup (characterLattice S)) :
    RelativeRoot.tangentSubmodule (SubgroupFunctor.range (connectedWeightHom b e A)) =
      RelativeRoot.tangentSubmodule (SubgroupFunctor.range (weightHom b e A)) :=
  RelativeRoot.tangentSubmodule_range_identityComponent_comp _

/-- The connected coordinate subgroup is stable under the original actual action. -/
theorem isStable_range_connectedWeightHom (A : AddSubsemigroup (characterLattice S)) :
    b.IsStable (SubgroupFunctor.range (connectedWeightHom b e A)) :=
  b.isStable_range_identityComponent_comp (weightHom b e A)
    ⟨inferInstance, rfl⟩ (isStable_range_weightHom b e A)

/-- The original action restricted to the connected coordinate subgroup. -/
def onConnectedWeightGroupScheme (A : AddSubsemigroup (characterLattice S)) :
    AutomorphicAction S.toGrp (connectedWeightGroupScheme b e A) :=
  b.onRepresentedIdentityComponent (weightHom b e A)
    ⟨inferInstance, rfl⟩ (isStable_range_weightHom b e A)

theorem onConnectedWeightGroupScheme_act_comp (A : AddSubsemigroup (characterLattice S))
    {T : Over (Spec (CommRingCat.of k))} (s : T ⟶ S.X)
    (x : T ⟶ (connectedWeightGroupScheme b e A).X) :
    (onConnectedWeightGroupScheme b e A).act s x ≫ (connectedWeightHom b e A).hom.hom =
      b.act s (x ≫ (connectedWeightHom b e A).hom.hom) :=
  b.onRepresentedIdentityComponent_act_comp _ ⟨inferInstance, rfl⟩
    (isStable_range_weightHom b e A) s x

/-- The connected coordinate subgroup lies in the full coordinate subgroup on every test. -/
theorem range_connectedWeightHom_le (A : AddSubsemigroup (characterLattice S)) :
    SubgroupFunctor.range (connectedWeightHom b e A) ≤
      SubgroupFunctor.range (weightHom b e A) :=
  SubgroupFunctor.range_comp_le _ _

section Factor

variable (A : AddSubsemigroup (characterLattice S))
    {H : GroupScheme (Spec (CommRingCat.of k))} [ConnectedSpace H.X.left]
    (f : H ⟶ G) (hf : SubgroupFunctor.range f ≤ SubgroupFunctor.range (weightHom b e A))

/-- Connected sources whose points satisfy the coordinate condition factor through this subgroup. -/
def connectedWeightFactor : H ⟶ connectedWeightGroupScheme b e A :=
  IdentityComponent.factor _
    ((show (SubgroupFunctor.range (weightHom b e A)).IsRepresentedBy (weightHom b e A)
      from ⟨inferInstance, rfl⟩).liftOfLE f hf)

@[reassoc (attr := simp)]
theorem connectedWeightFactor_comp :
    connectedWeightFactor b e A f hf ≫ connectedWeightHom b e A = f := by
  rw [connectedWeightHom, ← Category.assoc, connectedWeightFactor,
    IdentityComponent.factor_identityComponentι, SubgroupFunctor.IsRepresentedBy.liftOfLE_comp]

include hf in
theorem range_le_connectedWeightHom :
    SubgroupFunctor.range f ≤ SubgroupFunctor.range (connectedWeightHom b e A) := by
  rw [← connectedWeightFactor_comp b e A f hf]
  exact SubgroupFunctor.range_comp_le _ _

include hf in
/-- Monicity makes the connected-source factorization unique. -/
theorem existsUnique_connectedWeightFactor :
    ∃! g : H ⟶ connectedWeightGroupScheme b e A, g ≫ connectedWeightHom b e A = f := by
  refine ⟨connectedWeightFactor b e A f hf, connectedWeightFactor_comp b e A f hf, ?_⟩
  intro g hg
  apply Grp.hom_ext
  apply (cancel_mono (connectedWeightHom b e A).hom.hom).mp
  exact congrArg (fun h => h.hom.hom) (hg.trans (connectedWeightFactor_comp b e A f hf).symm)

end Factor

end Langlands.GroupScheme.TorusActionCoordinates
