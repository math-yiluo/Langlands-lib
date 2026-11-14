import Langlands.GroupScheme.Lie.SmoothScalarExtension
import Langlands.GroupScheme.Lie.BaseChange
import Langlands.GroupScheme.Lie.DimensionInduction
import Langlands.GroupScheme.HomImageEmbedding
import Langlands.GroupScheme.Rational.SubgroupIntersectionBaseChangeProperties
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-! # Lie ranks of smooth affine groups at field-valued points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Lie

attribute [local instance] Module.finitePresentation_of_projective

/-- The actual Lie dimension at a field-valued point of a smooth affine group
is the rank of its relative Lie module at that point. -/
def SmoothFibreRankStatement : Prop :=
  ∀ (R : CommRingCat.{u}) (G : GroupScheme (Spec R))
    [Smooth G.X.hom] [IsAffineHom G.X.hom],
    ∀ (K : Type u) [Field K] [Algebra R K],
      Module.finrank K (Additive (lieKernel G K)) =
        Module.rankAtStalk (R := R) (Additive (lieKernel G R))
          ((IsLocalRing.closedPoint K).comap (algebraMap R K))

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R))
  [Smooth G.X.hom] [IsAffineHom G.X.hom]

/-- The dimension of the actual Lie kernel at a field-valued point is the
rank of the finite projective relative Lie module at its image. -/
theorem finrank_lieKernel_eq_rankAtStalk
    (K : Type u) [Field K] [Algebra R K] :
    Module.finrank K (Additive (lieKernel G K)) =
      Module.rankAtStalk (R := R) (Additive (lieKernel G R))
        ((IsLocalRing.closedPoint K).comap (algebraMap R K)) := by
  calc
    _ = Module.finrank K (K ⊗[R] Additive (lieKernel G R)) :=
      (smoothKernelScalarExtension G K).finrank_eq.symm
    _ = Module.rankAtStalk (R := K) (K ⊗[R] Additive (lieKernel G R))
        (IsLocalRing.closedPoint K) := by
      rw [Module.rankAtStalk_eq_finrank_of_free]
      rfl
    _ = _ := Module.rankAtStalk_baseChange (M := Additive (lieKernel G R)) _

/-- The rank comparison follows from smooth scalar extension. -/
theorem smoothFibreRank : SmoothFibreRankStatement.{u} := by
  intro R G _ _ K _ _
  exact finrank_lieKernel_eq_rankAtStalk G K

local instance affine_baseChange {K : Type u} [CommRing K] [Algebra R K] :
    IsAffineHom ((baseChange (algebraBaseMap R K)).obj G).X.hom :=
  inferInstanceAs (IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap R K)))

/-- The Lie dimension of the actual scheme fibre agrees with the relative
Lie rank at the field-valued base point. -/
theorem dimension_baseChange_eq_rankAtStalk
    (K : Type u) [Field K] [Algebra R K] :
    dimension ((baseChange (algebraBaseMap R K)).obj G) =
      Module.rankAtStalk (R := R) (Additive (lieKernel G R))
        ((IsLocalRing.closedPoint K).comap (algebraMap R K)) := by
  change Module.finrank K
    (Additive (lieKernel ((baseChange (algebraBaseMap R K)).obj G) K)) = _
  rw [(kernelBaseChangeLinearEquiv R K G K).finrank_eq]
  exact finrank_lieKernel_eq_rankAtStalk G K

/-- Relative Lie rank is locally constant without any condition on the base ring. -/
theorem isLocallyConstant_lieRank :
    IsLocallyConstant (Module.rankAtStalk (R := R) (Additive (lieKernel G R))) :=
  Module.isLocallyConstant_rankAtStalk

section Field

variable {k : Type u} [Field k]
  {H G : GroupScheme (Spec (CommRingCat.of k))}
  [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left]
  [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]

/-- A monic homomorphism of smooth connected affine groups with equal Lie
dimensions is an isomorphism. -/
theorem isIso_of_mono_of_dimension_eq (f : H ⟶ G) [Mono f.hom.hom]
    (hdim : dimension H = dimension G) : IsIso f := by
  apply isIso_of_surjective_targetMapLinear f (HomImage.isClosedSubgroup_of_mono f)
  exact (LinearEquiv.ofInjectiveOfFinrankEq (targetMapLinear f k)
    (targetMapLinear_injective f k) hdim).surjective

end Field

end Langlands.GroupScheme.Lie
