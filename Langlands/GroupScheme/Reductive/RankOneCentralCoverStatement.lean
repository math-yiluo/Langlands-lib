import Langlands.GroupScheme.Torus.Maximal
import Langlands.GroupScheme.Reductive.SpecialLinearTorus
import Langlands.GroupScheme.Torus.InducedProducts
import Langlands.GroupScheme.CentralIsogeny.Basic

/-! # An actual central cover in semisimple rank one -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A connected reductive group over an algebraically closed field with nonempty,
pairwise dependent actual roots admits a central isogeny from `SL₂` times a split
torus, together with an isogeny onto its prescribed maximal torus. -/
def RankOneCentralCoverStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus T.toGrp → ∀ i : T.toGrp ⟶ G, IsMaximalTorus i →
      haveI := hG.isAffineHom
      (∃ α, α ∈ roots i) →
      (∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β]) →
        ∃ (C : CommGroupScheme (Spec (CommRingCat.of k))),
          IsSplitTorus C.toGrp ∧
          ∃ (f : SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k) ⊗ C.toGrp ⟶ G)
            (t : CommGroupScheme.prod
              (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift (Fin 1))) C ⟶ T),
            IsCentralIsogeny f ∧
            IsIsogeny (CommGroupScheme.groupHom t) ∧
            (SpecialLinear.FinSucc.diagonalTorus 1 (CommRingCat.of k) ⊗ₘ 𝟙 C.toGrp) ≫ f =
              CommGroupScheme.groupHom t ≫ i

end Langlands.GroupScheme
