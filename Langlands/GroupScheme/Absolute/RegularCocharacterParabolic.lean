import Langlands.GroupScheme.Absolute.BorelStatement
import Langlands.GroupScheme.Absolute.RegularCocharacterWeights
import Langlands.GroupScheme.Dynamic.ParabolicLieCriterion

/-! # Dynamic parabolics of regular cocharacters (conditional on structure inputs) -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Let `G` be a smooth connected affine group over a field, `j : T ⟶ G` a homomorphism from a
split torus and `ν, ν'` regular cocharacters of `j`. Then `P(ν ≫ j) = P(ν' ≫ j)` exactly when
every root of `j` has the same sign on `ν` and on `ν'`. -/
theorem parabolic_comp_eq_iff_of_isRegular (hLie : DynamicLieStatement.{u})
    (hSm : DynamicSmoothStatement.{u}) (hCo : DynamicConnectedStatement.{u})
    (hEq : LieSubgroupEqualityStatement.{u}) [Smooth G.X.hom] [IsAffineHom G.X.hom]
    [ConnectedSpace G.X.left] (hT : IsSplitTorus T.toGrp) {j : T.toGrp ⟶ G}
    {ν ν' : cocharacterLattice T} (hν : IsRegularCocharacter j ν)
    (hν' : IsRegularCocharacter j ν') :
    Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ j) =
        Dynamic.parabolic (CommGroupScheme.groupHom ν' ≫ j) ↔
      ∀ α ∈ roots j, (0 < latticePairing T α ν ↔ 0 < latticePairing T α ν') :=
  (parabolic_comp_eq_iff_iSup_weightSpace_eq hLie hSm hCo hEq j ν ν').trans
    (iSup_nat_weightSpace_cocharacter_eq_iff hT hν hν')

/-- The second clause of `RegularCocharacterBorelStatement`, conditional on the structure
statements for dynamic parabolics and on the subgroup-equality criterion: for a connected
reductive `G` over a field and a homomorphism `j : T ⟶ G` from a split torus, regular
cocharacters `ν, ν'` of `j` have `P(ν ≫ j) = P(ν' ≫ j)` exactly when every root of `j` has the
same sign on `ν` and on `ν'`. -/
theorem regularCocharacterBorel_parabolic_eq_iff (hLie : DynamicLieStatement.{u})
    (hSm : DynamicSmoothStatement.{u}) (hCo : DynamicConnectedStatement.{u})
    (hEq : LieSubgroupEqualityStatement.{u}) (hG : IsConnectedReductive G)
    (j : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp) :
    haveI := hG.isAffineHom
    ∀ ν ν' : cocharacterLattice T, IsRegularCocharacter j ν → IsRegularCocharacter j ν' →
      (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ j) =
          Dynamic.parabolic (CommGroupScheme.groupHom ν' ≫ j) ↔
        ∀ α ∈ roots j, (0 < latticePairing T α ν ↔ 0 < latticePairing T α ν')) := by
  have := hG.isAffineHom
  have := hG.smooth
  have := hG.connectedSpace
  exact fun ν ν' hν hν' => parabolic_comp_eq_iff_of_isRegular hLie hSm hCo hEq hT hν hν'

end Langlands.GroupScheme
