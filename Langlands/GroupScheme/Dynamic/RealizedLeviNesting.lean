import Langlands.GroupScheme.Dynamic.LeviParabolicExtension
import Langlands.GroupScheme.Dynamic.LeviCocharacterRealizationProof
import Langlands.GroupScheme.Dynamic.NestedDecomposition

/-! # Exact nesting supplied by simultaneous Levi realization -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

section Generic

variable {S : Scheme.{u}} {G L : GroupScheme S}
    (χ : (Gm S).toGrp ⟶ G) (j : L ⟶ G)
    (hj : (centralizer χ).IsRepresentedBy j)
    (ν : (Gm S).toGrp ⟶ L) (ψ : (Gm S).toGrp ⟶ G)

/-- An exactly extended source parabolic is contained in the outer parabolic. -/
theorem realized_parabolic_le
    (hP : parabolic ψ = extendFromCentralizer χ j hj (parabolic ν)) :
    parabolic ψ ≤ parabolic χ := by
  rw [hP]
  exact extendFromCentralizer_le_parabolic χ j hj _

include hj in
/-- The exactly realized source Levi is contained in the outer Levi. -/
theorem realized_centralizer_le
    (hZ : centralizer ψ = (centralizer ν).map j) :
    centralizer ψ ≤ centralizer χ := by
  rw [hZ, ← hj.2]
  exact SubgroupFunctor.map_le_range j _

/-- The outer radical is contained in the exactly extended source radical. -/
theorem unipotent_le_realized
    (hU : unipotent ψ = extendFromCentralizer χ j hj (unipotent ν)) :
    unipotent χ ≤ unipotent ψ := by
  rw [hU]
  exact unipotent_le_extendFromCentralizer χ j hj _

variable [IsSeparated G.X.hom]

/-- Simultaneous realization supplies the full all-test nested decomposition. -/
theorem nestedLeviDecomposition_of_realization
    (hReal :
      parabolic ψ = extendFromCentralizer χ j hj (parabolic ν) ∧
        centralizer ψ = (centralizer ν).map j ∧
        unipotent ψ = extendFromCentralizer χ j hj (unipotent ν)) :
    SubgroupFunctor.NestedLeviDecomposition
      (parabolic ψ) (centralizer ψ) (unipotent ψ) (centralizer χ) (unipotent χ) :=
  nestedLeviDecomposition_of_inclusions ψ χ
    (realized_parabolic_le χ j hj ν ψ hReal.1)
    (realized_centralizer_le χ j hj ν ψ hReal.2.1)
    (unipotent_le_realized χ j hj ν ψ hReal.2.2)

end Generic

/-- Every source cocharacter in a represented dynamic Levi admits an ambient
realization with all nested products on the original test schemes. -/
theorem exists_realization_with_nestedDecomposition
    {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (L : GroupScheme (Spec (CommRingCat.of k))) (j : L ⟶ G)
    (hjc : IsClosedSubgroup j) (hj : (centralizer χ).IsRepresentedBy j)
    (ν : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ L) :
    ∃ ψ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G,
      (parabolic ψ = extendFromCentralizer χ j hj (parabolic ν) ∧
        centralizer ψ = (centralizer ν).map j ∧
        unipotent ψ = extendFromCentralizer χ j hj (unipotent ν)) ∧
      NestedParabolicDecomposition ψ χ := by
  have := hG.isAffineHom
  obtain ⟨ψ, hP, hZ, hU⟩ :=
    dynamicLeviCocharacterRealization k G hG χ L j hjc hj ν
  exact ⟨ψ, ⟨hP, hZ, hU⟩,
    nestedLeviDecomposition_of_realization χ j hj ν ψ ⟨hP, hZ, hU⟩⟩

/-- A chosen ambient realization, carrying the exact identities and all-test
nested decomposition established by the preceding existence theorem. -/
def nestedRealization
    {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (L : GroupScheme (Spec (CommRingCat.of k))) (j : L ⟶ G)
    (hjc : IsClosedSubgroup j) (hj : (centralizer χ).IsRepresentedBy j)
    (ν : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ L) :
    {ψ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G //
      (parabolic ψ = extendFromCentralizer χ j hj (parabolic ν) ∧
        centralizer ψ = (centralizer ν).map j ∧
        unipotent ψ = extendFromCentralizer χ j hj (unipotent ν)) ∧
      NestedParabolicDecomposition ψ χ} :=
  ⟨Classical.choose (exists_realization_with_nestedDecomposition G hG χ L j hjc hj ν),
    Classical.choose_spec (exists_realization_with_nestedDecomposition G hG χ L j hjc hj ν)⟩

end Langlands.GroupScheme.Dynamic
