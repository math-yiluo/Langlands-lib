import Langlands.GroupScheme.Rational.TangentImage
import Langlands.GroupScheme.Lie.SmoothIsogenyDimension
import Langlands.GroupScheme.QuotientCell

/-! # Tangent dimension bounds from subgroup cells in actual quotients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Order
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {G U : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom U.X.hom]

namespace RelativeRoot

/-- The actual Lie module of a representative is the intrinsic tangent
submodule of its all-test subgroup functor. -/
def representedTangentLinearEquiv (F : SubgroupFunctor G) (j : U ⟶ G)
    (hj : F.IsRepresentedBy j) :
    Additive (lieKernel U k) ≃ₗ[k] tangentSubmodule F := by
  have : Mono j.hom.hom := hj.1
  exact (LinearEquiv.ofInjective (Lie.targetMapLinear j k)
    (Lie.targetMapLinear_injective j k)).trans
      (LinearEquiv.ofEq _ _
        ((hasLieImage_iff_tangentSubmodule_eq _ _).mp
          (hasLieImage_of_isRepresentedBy j hj)).symm)

/-- Representability identifies the intrinsic tangent finrank with the
actual Lie finrank of the representative. -/
theorem finrank_tangentSubmodule_eq_of_isRepresentedBy
    (F : SubgroupFunctor G) (j : U ⟶ G) (hj : F.IsRepresentedBy j) :
    Module.finrank k (tangentSubmodule F) =
      Module.finrank k (Additive (lieKernel U k)) :=
  (representedTangentLinearEquiv F j hj).finrank_eq.symm

end RelativeRoot

namespace Lie

/-- A smooth affine group's actual Lie dimension is bounded by the
topological Krull dimension of its underlying scheme. -/
theorem finrank_kernel_cast_le_topologicalKrullDim
    (U : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom U.X.hom] [Smooth U.X.hom] :
    (Module.finrank k (Additive (lieKernel U k)) : WithBot ℕ∞) ≤
      topologicalKrullDim U.X.left := by
  rw [finrank_kernel_cast_eq_ringKrullDim U, ringKrullDim_stalk_eq_coheight,
    topologicalKrullDim]
  rw [← coheight_orderIso (irreducibleSetEquivPoints (α := U.X.left)).symm]
  exact coheight_le_krullDim _

end Lie

namespace RelativeRoot

/-- An open cell of a smooth represented subgroup bounds its intrinsic
tangent dimension by the dimension of the target scheme. -/
theorem finrank_tangentSubmodule_cast_le_of_openImmersion
    (F : SubgroupFunctor G) (j : U ⟶ G) (hj : F.IsRepresentedBy j)
    [Smooth U.X.hom] {X : Over (Spec (CommRingCat.of k))}
    (c : U.X ⟶ X) [IsOpenImmersion c.left] :
    (Module.finrank k (tangentSubmodule F) : WithBot ℕ∞) ≤
      topologicalKrullDim X.left := by
  rw [finrank_tangentSubmodule_eq_of_isRepresentedBy F j hj]
  exact (Lie.finrank_kernel_cast_le_topologicalKrullDim U).trans
    c.left.isOpenEmbedding.isInducing.topologicalKrullDim_le

/-- In particular, an open cell in a scheme of dimension at most one gives
an intrinsic tangent finrank at most one. -/
theorem finrank_tangentSubmodule_le_one_of_openImmersion
    (F : SubgroupFunctor G) (j : U ⟶ G) (hj : F.IsRepresentedBy j)
    [Smooth U.X.hom] {X : Over (Spec (CommRingCat.of k))}
    (c : U.X ⟶ X) [IsOpenImmersion c.left]
    (hX : topologicalKrullDim X.left ≤ 1) :
    Module.finrank k (tangentSubmodule F) ≤ 1 := by
  have h := (finrank_tangentSubmodule_cast_le_of_openImmersion F j hj c).trans hX
  exact_mod_cast h

end RelativeRoot

namespace QuotientCell

variable {P : GroupScheme (Spec (CommRingCat.of k))}

/-- An open multiplication cell in an actual fpqc subgroup quotient bounds
the intrinsic tangent dimension of a smooth represented cell subgroup. -/
theorem finrank_tangentSubmodule_cast_le
    (F : SubgroupFunctor G) (j : U ⟶ G) (hj : F.IsRepresentedBy j)
    [Smooth U.X.hom] (i : P ⟶ G) [Mono i.hom.hom]
    {Q : Over (Spec (CommRingCat.of k))} (q : G.X ⟶ Q)
    (hf : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T)
    [Surjective q.left] [Flat q.left] [QuasiCompact q.left]
    [IsOpenImmersion (multiplication i j.hom.hom).left] :
    (Module.finrank k (RelativeRoot.tangentSubmodule F) : WithBot ℕ∞) ≤
      topologicalKrullDim Q.left := by
  let := isOpenImmersion i j.hom.hom q hf
  exact RelativeRoot.finrank_tangentSubmodule_cast_le_of_openImmersion
    F j hj (j.hom.hom ≫ q)

end QuotientCell

end Langlands.GroupScheme
