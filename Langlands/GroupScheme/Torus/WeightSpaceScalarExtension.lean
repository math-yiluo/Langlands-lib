import Langlands.GroupScheme.Torus.WeightBaseChangeComparison
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.Dimension.Free

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct
namespace Langlands.GroupScheme
set_option backward.isDefEq.respectTransparency false

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
local notation "b" => algebraBaseMap k K
local notation "G_K" => Functor.obj (GroupScheme.baseChange b) G
local instance weightSpaceScalarExtensionAffine :
    IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom b)
  infer_instance

theorem map_weightSpace_baseChange (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) (χ : characterLattice T) :
    ((weightSpace i χ).baseChange K).map
        (Lie.schemeScalarExtension (K := K) G).toLinearMap =
      weightSpace ((GroupScheme.baseChange b).map i)
        (characterLattice.baseChange b T χ) := by
  rw [weightSpace_baseChange_eq_extendedWeightSpace hT i χ]
  simp only [Submodule.baseChange_eq_span, Submodule.map_span,
    Submodule.map_coe, Set.image_image, extendedWeightSpace]
  rfl

def weightSpaceBaseChangeEquiv (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) (χ : characterLattice T) :
    K ⊗[k] weightSpace i χ ≃ₗ[K]
      weightSpace ((GroupScheme.baseChange b).map i)
        (characterLattice.baseChange b T χ) :=
  (Submodule.toBaseChange.toLinearEquiv K (weightSpace i χ)).trans
    ((Submodule.equivMapOfInjective
      (Lie.schemeScalarExtension (K := K) G).toLinearMap
      (Lie.schemeScalarExtension (K := K) G).injective
      ((weightSpace i χ).baseChange K)).trans
        (LinearEquiv.ofEq _ _ (map_weightSpace_baseChange hT i χ)))

@[simp] theorem weightSpaceBaseChangeEquiv_tmul (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) (χ : characterLattice T) (a : K)
    (X : weightSpace i χ) :
    (weightSpaceBaseChangeEquiv (K := K) hT i χ (a ⊗ₜ[k] X) :
      Additive (lieKernel G_K K)) =
      Lie.schemeScalarExtension (K := K) G
        (a ⊗ₜ[k] (X : Additive (lieKernel G k))) := by
  rfl

theorem finrank_weightSpace_baseChange (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) (χ : characterLattice T) :
    Module.finrank K (weightSpace ((GroupScheme.baseChange b).map i)
      (characterLattice.baseChange b T χ)) =
      Module.finrank k (weightSpace i χ) := by
  rw [← (weightSpaceBaseChangeEquiv (K := K) hT i χ).finrank_eq,
    Module.finrank_baseChange]

theorem weightSpace_line_baseChange_iff (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) (χ : characterLattice T) :
    Nonempty (K ≃ₗ[K] weightSpace ((GroupScheme.baseChange b).map i)
      (characterLattice.baseChange b T χ)) ↔
      Nonempty (k ≃ₗ[k] weightSpace i χ) := by
  let : Module.Free K (weightSpace ((GroupScheme.baseChange b).map i)
      (characterLattice.baseChange b T χ)) := Module.Free.of_divisionRing K _
  let : Module.Free k (weightSpace i χ) := Module.Free.of_divisionRing k _
  rw [Module.nonempty_linearEquiv_iff_finrank_eq_one,
    Module.nonempty_linearEquiv_iff_finrank_eq_one,
    finrank_weightSpace_baseChange hT i χ]

end Langlands.GroupScheme
