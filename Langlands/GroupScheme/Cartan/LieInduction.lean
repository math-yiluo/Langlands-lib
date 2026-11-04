import Langlands.GroupScheme.Cartan.Induction
import Langlands.GroupScheme.Lie.SubgroupTangent
import Langlands.GroupScheme.Lie.DimensionInduction
import Langlands.GroupScheme.Rational.RootKernelIdentityWeights

/-! # Tangent images and dimension decrease for Cartan induction -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {G C H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth C.X.hom] [IsAffineHom C.X.hom]

/-- Every maximal torus in the source remains maximal in the ambient group. -/
def PreservesMaximalTori (j : C ⟶ G) : Prop :=
  ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (t : T.toGrp ⟶ C),
    IsMaximalTorus t → IsMaximalTorus (t ≫ j)

local instance (A : Type u) [CommRing A] [Algebra k A] :
    CommGroup (lieKernel (identityComponent C) A) :=
  lieKernelCommGroup (identityComponent C)

local instance (A : Type u) [CommRing A] [Algebra k A] :
    Module A (Additive (lieKernel (identityComponent C) A)) :=
  lieKernelModule (identityComponent C)

namespace SubgroupFunctor.IsRepresentedBy

/-- The tangent submodule of a smoothly represented subgroup is also the image
of the actual identity component of its representative. -/
theorem lie_eq_range_identityComponent {F : SubgroupFunctor G} {j : C ⟶ G}
    (hrep : F.IsRepresentedBy j)
    (A : Type u) [CommRing A] [Algebra k A] :
    F.lie A = LinearMap.range (Lie.targetMapLinear (identityComponentι C ≫ j) A) := by
  rw [IdentityComponent.range_targetMapLinear_comp, F.lie_eq_range A j hrep]

end SubgroupFunctor.IsRepresentedBy

namespace Lie

/-- A smooth closed representative with proper tangent image has an identity
component of strictly smaller Lie dimension than the connected ambient group. -/
theorem dimension_identityComponent_lt_of_lie_ne_top
    [Smooth G.X.hom] [ConnectedSpace G.X.left]
    {F : SubgroupFunctor G} {j : C ⟶ G}
    (hrep : F.IsRepresentedBy j) (hj : IsClosedSubgroup j)
    (hproper : F.lie k ≠ ⊤) :
    dimension (identityComponent C) < dimension G := by
  have hclosed : IsClosedSubgroup (identityComponentι C ≫ j) :=
    (IdentityComponent.isClosedSubgroup_identityComponentι C).comp hj
  apply dimension_lt_of_proper_closedSubgroup (identityComponentι C ≫ j) hclosed
  intro hiso
  let := hiso
  have : IsIso (identityComponentι C ≫ j).hom.hom :=
    (Grp.forget _).map_isIso (identityComponentι C ≫ j)
  have : IsIso (identityComponentι C ≫ j).hom.hom.left :=
    (Over.forget _).map_isIso (identityComponentι C ≫ j).hom.hom
  apply hproper
  rw [hrep.lie_eq_range_identityComponent k]
  exact LinearMap.range_eq_top.mpr
    (targetMapLinear_surjective_of_smooth (identityComponentι C ≫ j) k inferInstance)

end Lie

/-- Inductive generation of the identity component of a smooth represented
subgroup puts its full tangent image in every closed competitor containing all
ambient Cartans, if its maximal tori remain maximal in the ambient group. -/
theorem IsGeneratedByCartanSubgroups.lie_le_of_maximalTori
    {F : SubgroupFunctor G} {j : C ⟶ G}
    (hrep : F.IsRepresentedBy j) (hj : IsClosedSubgroup j)
    (hgen : IsGeneratedByCartanSubgroups (identityComponent C))
    (htori : PreservesMaximalTori (identityComponentι C ≫ j))
    (i : H ⟶ G) (hi : IsClosedSubgroup i)
    (hcartan : ∀ (D : GroupScheme (Spec (CommRingCat.of k))) (d : D ⟶ G),
      IsCartanSubgroup d → FactorsThrough d.hom.hom i) :
    F.lie k ≤ (SubgroupFunctor.range i).lie k := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hclosed : IsClosedSubgroup (identityComponentι C ≫ j) :=
    (IdentityComponent.isClosedSubgroup_identityComponentι C).comp hj
  have hle := hgen.range_le_of_maximalTori (identityComponentι C ≫ j) hclosed
    htori i hi hcartan
  have hmono := SubgroupFunctor.lie_mono k hle
  have hrep' : (SubgroupFunctor.range (identityComponentι C ≫ j)).IsRepresentedBy
      (identityComponentι C ≫ j) := by
    have : IsClosedImmersion (identityComponentι C ≫ j).hom.hom.left := hclosed
    exact ⟨Over.mono_of_mono_left _, rfl⟩
  rw [(SubgroupFunctor.range (identityComponentι C ≫ j)).lie_eq_range k _ hrep',
    ← hrep.lie_eq_range_identityComponent k] at hmono
  exact hmono

end Langlands.GroupScheme
