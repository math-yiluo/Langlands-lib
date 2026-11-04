import Langlands.GroupScheme.AutomorphicAction
import Langlands.GroupScheme.VectorGroupQuotient
import Langlands.GroupScheme.Torus.Diagonalizable
import Langlands.GroupScheme.Reductive.Basic
import Langlands.AbelianScheme.Kernel
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Splitting of extensions of diagonalizable groups by linear closed additive subgroups -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Milne (2022), Theorem 15.34(d), with a diagonalizable quotient. Over an algebraically closed
field `k`, let `D` be the diagonalizable group of a finitely generated abelian group `Λ`, and let
`q : E ⟶ D` be an actual flat, surjective, locally finitely presented homomorphism from an affine
group scheme of finite type. Suppose that the actual kernel of `q` is a closed subgroup of `𝔾ₐ`
through `a`, and that `b` is an action of `D` on this kernel that is induced by conjugation in `E`
and is the restriction, along `a`, of the linear action of `D` on `𝔾ₐ` through the character
`χ`. Then `q` has a homomorphic section. -/
def LinearAdditiveExtensionSplittingStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (Λ : Type u) [AddCommGroup Λ] [AddGroup.FG Λ],
    let D := Diagonalizable.groupScheme (CommRingCat.of k) Λ
    ∀ (E : GroupScheme (Spec (CommRingCat.of k)))
      [LocallyOfFiniteType E.X.hom] [IsAffineHom E.X.hom] (q : E ⟶ D.toGrp),
      Flat q.hom.hom.left → Surjective q.hom.hom.left →
      LocallyOfFinitePresentation q.hom.hom.left →
      ∀ (a : kernel q ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1), IsClosedSubgroup a →
      ∀ (χ : characterLattice D) (b : AutomorphicAction D.toGrp (kernel q)),
        (∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ E.X) (x : T ⟶ (kernel q).X),
          b.act (g ≫ q.hom.hom) x ≫ (kernelι q).hom.hom =
            g * (x ≫ (kernelι q).hom.hom) * g⁻¹) →
        (∀ (T : Over (Spec (CommRingCat.of k))) (d : T ⟶ D.X) (x : T ⟶ (kernel q).X),
          b.act d x ≫ a.hom.hom =
            (VectorGroup.weightAction (n := 1) χ).act d (x ≫ a.hom.hom)) →
        ∃ s : D.toGrp ⟶ E, s ≫ q = 𝟙 D.toGrp

end Langlands.GroupScheme
