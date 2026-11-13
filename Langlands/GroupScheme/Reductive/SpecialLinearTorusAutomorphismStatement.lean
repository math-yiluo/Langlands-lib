import Langlands.GroupScheme.SpecialLinear
import Langlands.GroupScheme.Reductive.GeometricRootDatumComparison
import Langlands.GroupScheme.Reductive.BasedRootDatumProjection

/-! # Matrix descriptions of torus-preserving special-linear automorphisms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A torus-preserving automorphism of the actual split special linear group is
conjugation by a matrix, with inverse transpose precisely in the nontrivial
based-root-action case. The formula holds on every test scheme. -/
def SpecialLinearTorusAutomorphismStatement : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ),
    haveI := SpecialLinear.isAffineHom_groupScheme (Fin (n + 1)) (CommRingCat.of k)
    ∀ (p : SplitPinning (SpecialLinear.groupScheme (Fin (n + 1)) (CommRingCat.of k)))
    (f : SpecialLinear.groupScheme (Fin (n + 1)) (CommRingCat.of k) ≅
      SpecialLinear.groupScheme (Fin (n + 1)) (CommRingCat.of k))
    (t : p.torus ≅ p.torus)
    (hsq : p.inclusion ≫ f.hom = CommGroupScheme.groupHom t.hom ≫ p.inclusion),
    let δ := rootDatumEquivOfTorusCompatibleIso
      p.isConnectedReductive p.isConnectedReductive
      p.isSplitTorus p.isSplitTorus p.isMaximalTorus p.isMaximalTorus
      f t hsq p.isRootDatum p.isRootDatum
    let θ := p.basedRootDatumProjection δ
    ∃ x : Matrix.GeneralLinearGroup (Fin (n + 1)) k,
      ∀ (Z : Over (Spec (CommRingCat.of k)))
        (g : Matrix.SpecialLinearGroup (Fin (n + 1)) Γ(Z.left, ⊤)),
        ((∀ v : p.base.support, θ.val.indexEquiv v.val = v.val) →
          (SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of k) Z
              (((SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of k) Z).symm g) ≫
                f.hom.hom.hom) :
            Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) =
            (Matrix.GeneralLinearGroup.map (scalarMap Z) x :
              Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) *
              (g : Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) *
              (Matrix.GeneralLinearGroup.map (scalarMap Z) x⁻¹ :
                Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤))) ∧
        ((∃ v : p.base.support, θ.val.indexEquiv v.val ≠ v.val) →
          (SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of k) Z
              (((SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of k) Z).symm g) ≫
                f.hom.hom.hom) :
            Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) =
            (Matrix.GeneralLinearGroup.map (scalarMap Z) x :
              Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) *
              ((g⁻¹ : Matrix.SpecialLinearGroup (Fin (n + 1)) Γ(Z.left, ⊤)) :
                Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)).transpose *
              (Matrix.GeneralLinearGroup.map (scalarMap Z) x⁻¹ :
                Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)))

end Langlands.GroupScheme
