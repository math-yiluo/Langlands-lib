import Langlands.Global.AdelicGroupNormOne
import Langlands.Global.NumberFieldAdeleTensorComparison
import Langlands.GroupScheme.AffineWeilRestrictionTopology

/-! # Canonical norm-one adelic comparison for Weil restriction -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.Global.AdelicWeilRestriction

open Langlands.GroupScheme AdelicGroupPoints

variable (F L : Type u) [Field F] [NumberField F] [Field L] [NumberField L]
  [Algebra F L]
  (G : GroupScheme (Spec (CommRingCat.of L)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- The canonical actual full-adele group equivalence for Weil restriction, obtained
from tensor-valued points and the proved canonical adelic tensor isomorphism. -/
def adelicPointsEquiv :
    AdelicGroupPoints F (AffineWeil.groupScheme F L G) ≃* AdelicGroupPoints L G :=
  (AffineWeil.pointsEquiv F L G (Adeles F)).trans
    (G.affinePointFunctor.mapIso
      (CommAlgCat.isoMk (numberFieldAdeleTensorEquiv F L))).groupIsoToMulEquiv

/-- The coefficient map in the equivalence is the original canonical tensor map. -/
theorem adelicPointsEquiv_apply
    (g : AdelicGroupPoints F (AffineWeil.groupScheme F L G)) :
    adelicPointsEquiv F L G g = G.affinePointMap
      (CommAlgCat.ofHom (numberFieldAdeleTensorMap F L))
      (AffineWeil.pointsEquiv F L G (Adeles F) g) := rfl

/-- The canonical equivalence of actual principal-point carriers. -/
abbrev rationalPointsEquiv :
    RationalGroupPoints F (AffineWeil.groupScheme F L G) ≃* RationalGroupPoints L G :=
  AffineWeil.basePointsEquiv F L G

omit G [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
/-- The canonical full adelic tensor map commutes with the principal coefficient maps
and the canonical tensor-unit map. -/
theorem tensorMap_comp_principal :
    (numberFieldAdeleTensorMap F L).comp
        (Algebra.TensorProduct.lTensor (S := L) L (Algebra.ofId F (Adeles F))) =
      (Algebra.ofId L (Adeles L)).comp (Algebra.TensorProduct.rid F L L).toAlgHom := by
  apply AlgHom.ext
  intro z
  induction z with
  | tmul a b =>
    change numberFieldAdeleTensorMap F L (a ⊗ₜ[F] algebraMap F (Adeles F) b) =
      algebraMap L (Adeles L) (b • a)
    rw [numberFieldAdeleTensorMap_tmul, AdelicFunctoriality.adeleInclusion_diagonal,
      Algebra.smul_def, map_mul, mul_comm]
  | add z w hz hw => simp only [map_add, hz, hw]

/-- The fixed canonical adelic Weil comparison commutes with every actual principal
point, without any topological or character-kernel comparison hypothesis. -/
@[simp] theorem adelicPointsEquiv_rational
    (q : RationalGroupPoints F (AffineWeil.groupScheme F L G)) :
    adelicPointsEquiv F L G (rational F _ q) =
      rational L G (rationalPointsEquiv F L G q) := by
  change G.affinePointMap (CommAlgCat.ofHom (numberFieldAdeleTensorMap F L))
      (AffineWeil.pointsEquiv F L G (Adeles F)
        ((AffineWeil.groupScheme F L G).affinePointMap
          (CommAlgCat.ofHom (Algebra.ofId F (Adeles F))) q)) =
    G.affinePointMap (CommAlgCat.ofHom (Algebra.ofId L (Adeles L)))
      (G.affinePointMap (CommAlgCat.ofHom (Algebra.TensorProduct.rid F L L).toAlgHom)
        (AffineWeil.pointsEquiv F L G F q))
  rw [AffineWeil.pointsEquiv_naturality]
  change ((G.affinePointMap (CommAlgCat.ofHom (numberFieldAdeleTensorMap F L))).comp
      (G.affinePointMap (CommAlgCat.ofHom
        (Algebra.TensorProduct.lTensor (S := L) L (Algebra.ofId F (Adeles F))))))
      (AffineWeil.pointsEquiv F L G F q) =
    ((G.affinePointMap (CommAlgCat.ofHom (Algebra.ofId L (Adeles L)))).comp
      (G.affinePointMap (CommAlgCat.ofHom (Algebra.TensorProduct.rid F L L).toAlgHom)))
      (AffineWeil.pointsEquiv F L G F q)
  rw [← G.affinePointMap_comp, ← G.affinePointMap_comp]
  congr 2
  exact CommAlgCat.hom_ext (tensorMap_comp_principal F L)

/-- The actual Weil-restriction comparison is a homeomorphism, commutes with principal
points, and identifies the full normalized-character norm-one subgroups. -/
def NormOneComparisonStatement : Prop :=
  ∀ (F L : Type u) [Field F] [NumberField F] [Field L] [NumberField L]
    [Algebra F L] (G : GroupScheme (Spec (CommRingCat.of L)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    IsHomeomorph (adelicPointsEquiv F L G) ∧
      (∀ q : RationalGroupPoints F (AffineWeil.groupScheme F L G),
        adelicPointsEquiv F L G (rational F _ q) =
          rational L G (rationalPointsEquiv F L G q)) ∧
      (normOneSubgroup F (AffineWeil.groupScheme F L G)).map
          (adelicPointsEquiv F L G).toMonoidHom = normOneSubgroup L G

end Langlands.Global.AdelicWeilRestriction
