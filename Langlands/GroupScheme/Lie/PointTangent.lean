import Langlands.GroupScheme.Lie.AffineModule
import Langlands.AlgebraicGeometry.Picard.GroupObjectTangentAddition
import Langlands.AlgebraicGeometry.Picard.TangentSpaceStalkDerivation
import Langlands.AlgebraicGeometry.FieldPointTangentLocalRegularityProof

/-! # The actual Lie kernel and the tangent module at the identity -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Lie

open Langlands.AlgebraicGeometry.Picard

variable {k : Type u} [Field k]
  (G : GroupScheme (Spec (CommRingCat.of k)))


private lemma one_left :
    (1 : AffinePoints G k).left =
      (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X).left := by
  simp [CategoryTheory.Hom.one_def]
  exact Category.id_comp _

/-- Forgetting slice data identifies the actual identity kernel with rational tangent maps. -/
def kernelTangentEquiv :
    lieKernel G k ≃
      {t : Spec (CommRingCat.of (DualNumber k)) ⟶ G.X.left //
        IsTangentVectorAt G.X.hom
          (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X).left t} where
  toFun X := ⟨X.val.left, Over.w X.val, by
    have h := congrArg (fun p : AffinePoints G k => p.left) X.property
    exact h.trans (one_left G)⟩
  invFun t := ⟨Over.homMk t.val t.property.1, by
    apply Over.OverMorphism.ext
    exact t.property.2.trans (one_left G).symm⟩
  left_inv X := Subtype.ext (Over.OverMorphism.ext rfl)
  right_inv t := Subtype.ext rfl

/-- The actual identity kernel is the space of derivations of the identity stalk. -/
def kernelStalkDerivationEquiv :
    let e : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X := 1
    letI := stalkAlgebraOver G.X.hom (e.left (IsLocalRing.closedPoint k))
    letI := (rationalStalkAugmentation G.X.hom e.left (Over.w e)).toRingHom.toAlgebra
    lieKernel G k ≃
      Derivation k (G.X.left.presheaf.stalk (e.left (IsLocalRing.closedPoint k))) k := by
  let e : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X := 1
  letI := stalkAlgebraOver G.X.hom (e.left (IsLocalRing.closedPoint k))
  letI := (rationalStalkAugmentation G.X.hom e.left (Over.w e)).toRingHom.toAlgebra
  exact (kernelTangentEquiv G).trans
    (rationalStalkDerivationTangentEquiv G.X.hom e.left (Over.w e)).symm

private local instance kernelCommGroup [IsAffineHom G.X.hom] :
    CommGroup (lieKernel G k) := lieKernelCommGroup G

private local instance kernelSMul : SMul k (Additive (lieKernel G k)) := lieKernelSMul G

private local instance kernelModule [IsAffineHom G.X.hom] :
    Module k (Additive (lieKernel G k)) := lieKernelModule G

/-- Stalk derivations identify linearly with the actual Lie kernel module. -/
def stalkDerivationKernelLinearEquiv [IsAffineHom G.X.hom] :
    let e : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X := 1
    letI := stalkAlgebraOver G.X.hom (e.left (IsLocalRing.closedPoint k))
    letI := (rationalStalkAugmentation G.X.hom e.left (Over.w e)).toRingHom.toAlgebra
    Derivation k (G.X.left.presheaf.stalk (e.left (IsLocalRing.closedPoint k))) k ≃ₗ[k]
      Additive (lieKernel G k) := by
  let e : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X := 1
  letI := stalkAlgebraOver G.X.hom (e.left (IsLocalRing.closedPoint k))
  letI := (rationalStalkAugmentation G.X.hom e.left (Over.w e)).toRingHom.toAlgebra
  refine { toEquiv := (kernelStalkDerivationEquiv G).symm.trans Additive.ofMul
           map_add' := ?_
           map_smul' := ?_ }
  · intro D E
    apply Additive.toMul.injective
    apply Subtype.ext
    change rationalStalkDerivationPoint G.X e (D + E) =
      rationalStalkDerivationPoint G.X e D * rationalStalkDerivationPoint G.X e E
    exact rationalStalkDerivationPoint_add G.X D E
  · intro c D
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Over.OverMorphism.ext
    change (rationalStalkDerivationTangentEquiv G.X.hom e.left (Over.w e) (c • D)).val =
      Spec.map (CommRingCat.ofHom (GeneralLinear.DualNumber.epsilonScale c).toRingHom) ≫
        (rationalStalkDerivationTangentEquiv G.X.hom e.left (Over.w e) D).val
    exact rationalStalkDerivationTangentEquiv_smul G.X.hom e.left (Over.w e) c D

/-- The original dual-number Lie module is the tangent module at the identity. -/
def kernelPointTangentLinearEquiv [IsAffineHom G.X.hom] :
    Additive (lieKernel G k) ≃ₗ[k]
      Langlands.Scheme.tangentSpaceAtPoint G.X
        (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :=
  (stalkDerivationKernelLinearEquiv G).symm.trans
    (tangentSpaceAtPointDerivationEquiv G.X 1).symm

/-- The dimension of the actual Lie kernel is the cotangent dimension of the identity stalk. -/
theorem finrank_kernel_eq_cotangent [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] :
    let e : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X := 1
    let R := G.X.left.presheaf.stalk (e.left (IsLocalRing.closedPoint k))
    Module.finrank k (Additive (lieKernel G k)) =
      Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) :=
  (kernelPointTangentLinearEquiv G).finrank_eq.trans
    (Langlands.Scheme.fieldPointTangentLocalRegularity k G.X 1 inferInstance).2.1

end Langlands.GroupScheme.Lie
