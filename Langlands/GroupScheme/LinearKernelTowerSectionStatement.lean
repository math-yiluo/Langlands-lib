import Langlands.GroupScheme.LinearKernelTower
import Langlands.GroupScheme.Torus.Diagonalizable

/-! # Homomorphic sections for finite character-linear kernel towers -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.LinearKernelTower

/-- Over every algebraically closed field, an actual homomorphism to the diagonalizable group
of any finitely generated abelian character group has a homomorphic section if it admits a
finite character-linear kernel tower. The tower already requires every stage to be affine
and locally of finite type. This proposition records the section-existence assertion;
its proof and the construction of towers are separate obligations. -/
def SectionExistenceStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (Λ : Type u) [AddCommGroup Λ] [AddGroup.FG Λ],
    let D := Diagonalizable.groupScheme (CommRingCat.of k) Λ
    ∀ (E : GroupScheme (Spec (CommRingCat.of k))) (q : E ⟶ D.toGrp),
      AdmitsTower D q → ∃ s : D.toGrp ⟶ E, s ≫ q = 𝟙 D.toGrp

end Langlands.GroupScheme.LinearKernelTower
