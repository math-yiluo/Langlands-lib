import Langlands.GroupScheme.Lie.FieldExtension

/-! # Naturality of the linear Lie-kernel base-change comparison -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

variable (k K : Type u) [CommRing k] [CommRing K] [Algebra k K]
    {G Q : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom Q.X.hom]
    (A : Type u) [CommRing A] [Algebra k A] [Algebra K A]
    [IsScalarTower k K A]

local notation "b" => algebraBaseMap k K
local notation "G_K" => Functor.obj (GroupScheme.baseChange (algebraBaseMap k K)) G

local instance linearBaseChangeNaturality_source_isAffineHom : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom b)
  infer_instance

local instance linearBaseChangeNaturality_target_isAffineHom :
    IsAffineHom ((GroupScheme.baseChange b).obj Q).X.hom := by
  change IsAffineHom (pullback.snd Q.X.hom b)
  infer_instance

/-- The actual linear scheme-pullback comparison intertwines differentials. -/
theorem Lie.kernelBaseChangeLinearEquiv_target (q : G ⟶ Q)
    (X : Additive (lieKernel G_K A)) :
    Lie.kernelBaseChangeLinearEquiv k K Q A
        (Lie.targetMapLinear ((GroupScheme.baseChange b).map q) A X) =
      Lie.targetMapLinear q A (Lie.kernelBaseChangeLinearEquiv k K G A X) :=
  congrArg Additive.ofMul (Lie.kernelBaseChangeEquiv_target (k := k) (K := K) q X.toMul)

end Langlands.GroupScheme
