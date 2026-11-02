import Langlands.AlgebraicGeometry.PointTopology.RationalPoints
import Langlands.GroupScheme.Dynamic.Basic
import Langlands.GroupScheme.Reductive.Basic
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.Topology.Algebra.OpenSubgroup

/-! # Compact-open containment in actual dynamic unipotent radicals -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits

/-- Every compact subset of the actual dynamic unipotent radical lies in a
compact open subgroup, with the canonical rational-point topology and the
inherited subgroup topology, over every nonarchimedean local field. -/
def DynamicUnipotentCompactOpenContainmentStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : Langlands.GroupScheme (Spec (CommRingCat.of F)))
    (hG : Langlands.GroupScheme.IsConnectedReductive G)
    (χ : (Langlands.GroupScheme.Gm (Spec (CommRingCat.of F))).toGrp ⟶ G),
    letI : IsAffineHom G.X.hom := hG.isAffineHom
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace
        (Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) :=
      Langlands.AlgebraicGeometry.PointTopology.rationalPointTopology F G.X
    let U := (Langlands.GroupScheme.Dynamic.unipotent χ).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of F))))
    ∀ C : Set U, IsCompact C →
      ∃ K : OpenSubgroup U, IsCompact (K : Set U) ∧ C ⊆ (K : Set U)

end Langlands.BruhatTits
