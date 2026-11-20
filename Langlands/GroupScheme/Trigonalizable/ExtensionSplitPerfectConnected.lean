import Langlands.GroupScheme.Trigonalizable.ExtensionSplitAlgClosed
import Langlands.GroupScheme.Trigonalizable.PerfectOneStep

/-! # Splitting of trigonalizable extensions with connected quotient over perfect fields -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.TrigonalizableExtensionSplit

variable {k : Type u} [Field k]
  {G U : GroupScheme (Spec (CommRingCat.of k))} [LocallyOfFiniteType G.X.hom]
  [IsAffineHom G.X.hom] (i : U ⟶ G) {Λ : Type u} [AddCommGroup Λ] [AddGroup.FG Λ]
  (q : G ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp)

/-- **Milne 16.26(c).** Over a perfect field, if `D(Λ)` is connected, the quotient map of an
extension of `D(Λ)` by a closed normal unipotent subgroup has a homomorphic section. -/
theorem exists_section_of_perfect_of_connected [PerfectField k]
    (hD : ConnectedSpace (Diagonalizable.groupScheme (CommRingCat.of k) Λ).X.left)
    (hi : IsClosedSubgroup i) (hU : IsUnipotent U) (hN : (SubgroupFunctor.range i).IsNormal)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q) :
    ∃ s : (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp ⟶ G, s ≫ q = 𝟙 _ :=
  exists_section_of_admitsTower' (oneStepSplitting_of_perfect Λ hD) (admitsTower i q hi hU hN hq)

end Langlands.GroupScheme.TrigonalizableExtensionSplit
