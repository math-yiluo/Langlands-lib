import Langlands.GroupScheme.CommutingFactorRetraction
import Langlands.GroupScheme.Reductive.NormalIsogenyComplementStatement
import Langlands.GroupScheme.SimplyConnected.Basic

/-! # Normal-factor retractions from the structural complement proposition -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
variable {G H : GroupScheme (Spec (CommRingCat.of k))}

/-- Conditional on the arbitrary-field structural complement proposition, a
smooth connected closed normal subgroup of a simply connected group is a
retract whose kernel centralizes the subgroup on every test scheme. -/
theorem IsSimplyConnected.exists_normalFactorRetraction_of_complement
    (hG : IsSimplyConnected G)
    (hComplement : SemisimpleNormalIsogenyComplementStatement.{u})
    (j : H ⟶ G) (hj : IsClosedSubgroup j)
    (hHs : Smooth H.X.hom) (hHc : ConnectedSpace H.X.left)
    (hHn : (SubgroupFunctor.range j).IsNormal) :
    ∃ p : G ⟶ H, j ≫ p = 𝟙 H ∧
      ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X) (g : T ⟶ G.X),
        g ≫ p.hom.hom = 1 → Commute (h ≫ j.hom.hom) g := by
  obtain ⟨_, K, i, _, _, _, hHK, hc, hμ⟩ :=
    hComplement k G H hG.isSemisimple j hj hHs hHc hHn
  let : IsIso (commutingSubgroupMultiplicationHom j i hc) :=
    hG.central_isogeny_isIso (H ⊗ K) _ hHK hμ
  refine ⟨commutingFactorRetraction j i hc,
    comp_commutingFactorRetraction j i hc, ?_⟩
  intro T h g hg
  exact commute_of_comp_commutingFactorRetraction_eq_one j i hc h g hg

/-- An actual chosen normal-factor projection under the explicitly supplied
structural complement proposition. -/
def IsSimplyConnected.normalFactorRetraction
    (hG : IsSimplyConnected G)
    (hComplement : SemisimpleNormalIsogenyComplementStatement.{u})
    (j : H ⟶ G) (hj : IsClosedSubgroup j)
    (hHs : Smooth H.X.hom) (hHc : ConnectedSpace H.X.left)
    (hHn : (SubgroupFunctor.range j).IsNormal) : G ⟶ H :=
  (hG.exists_normalFactorRetraction_of_complement hComplement j hj hHs hHc hHn).choose

/-- The prescribed inclusion is a section of the chosen projection. -/
@[simp]
theorem IsSimplyConnected.comp_normalFactorRetraction
    (hG : IsSimplyConnected G)
    (hComplement : SemisimpleNormalIsogenyComplementStatement.{u})
    (j : H ⟶ G) (hj : IsClosedSubgroup j)
    (hHs : Smooth H.X.hom) (hHc : ConnectedSpace H.X.left)
    (hHn : (SubgroupFunctor.range j).IsNormal) :
    j ≫ hG.normalFactorRetraction hComplement j hj hHs hHc hHn = 𝟙 H :=
  (hG.exists_normalFactorRetraction_of_complement
    hComplement j hj hHs hHc hHn).choose_spec.1

/-- Every kernel point of the chosen projection commutes with the prescribed
normal subgroup, on each test scheme. -/
theorem IsSimplyConnected.commute_of_comp_normalFactorRetraction_eq_one
    (hG : IsSimplyConnected G)
    (hComplement : SemisimpleNormalIsogenyComplementStatement.{u})
    (j : H ⟶ G) (hj : IsClosedSubgroup j)
    (hHs : Smooth H.X.hom) (hHc : ConnectedSpace H.X.left)
    (hHn : (SubgroupFunctor.range j).IsNormal)
    {T : Over (Spec (CommRingCat.of k))} (h : T ⟶ H.X) (g : T ⟶ G.X)
    (hg : g ≫ (hG.normalFactorRetraction hComplement j hj hHs hHc hHn).hom.hom = 1) :
    Commute (h ≫ j.hom.hom) g :=
  (hG.exists_normalFactorRetraction_of_complement
    hComplement j hj hHs hHc hHn).choose_spec.2 T h g hg

end Langlands.GroupScheme
