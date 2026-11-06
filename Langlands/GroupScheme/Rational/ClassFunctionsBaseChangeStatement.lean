import Langlands.GroupScheme.Rational.ClassFunctions
import Langlands.GroupScheme.Descent.TensorCoordinates
import Langlands.GroupScheme.HopfMorphismBaseChange

/-! # Field base change for the canonical regular-class-function quotient -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.GroupScheme.ClassFunctions

/-- Field base change preserves the actual regular-class-function algebra and
its canonical quotient, compatibly with the coordinate presentation, the
invariant inclusion, relative Spec and the canonical map `rho`. -/
def FieldBaseChangeStatement : Prop :=
  ∀ (K F : Type u) [Field K] [Field F] [Algebra K F]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom],
    let b := Spec.map (CommRingCat.ofHom (algebraMap K F))
    let GF := (GroupScheme.baseChange b).obj G
    letI : IsAffineHom GF.X.hom := by
      change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
      infer_instance
    ∃ (e : (F ⊗[K] Coord G) ≃ₐ[F] Coord GF)
      (phi : (F ⊗[K] algebra G) ≃ₐ[F] algebra GF)
      (alpha : (Over.pullback b).obj (quotient G) ≅ quotient GF),
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫
          (Descent.TensorCoordinates.baseChangeIso K F (Coord G) G.X
            (Lie.coordinateIso G)).hom =
        (Lie.coordinateIso GF).hom.left ∧
      e.toAlgHom.comp
          (Algebra.TensorProduct.map (AlgHom.id F F) (inclusion G)) =
        (inclusion GF).comp phi.toAlgHom ∧
      alpha.hom.left =
        (HopfMorphismBaseChange.tensorSpecIso K F (algebra G)).hom ≫
          Spec.map (CommRingCat.ofHom phi.symm.toRingHom) ∧
      (Over.pullback b).map (rho G) ≫ alpha.hom = rho GF

end Langlands.GroupScheme.ClassFunctions
