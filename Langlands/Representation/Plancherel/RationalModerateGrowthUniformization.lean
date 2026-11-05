import Langlands.Representation.Plancherel.CoefficientGrowthUniformizationProof
import Langlands.Representation.Plancherel.RationalModerateGrowthStatement
import Langlands.BruhatTits.Unipotent.RationalPointCompactOpen

/-! # The finite-length step on actual reductive rational points -/

noncomputable section

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

universe u uV

open GroupScheme MatrixRepresentation

/-- The canonical point topology has the compact-open cofinality used by smooth
contragredient duality. Affineness and finite type suffice. -/
theorem rationalPoint_compactOpenCofinal
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] :
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    CompactOpenCofinal (rationalPoints G) := by
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  intro K
  exact (Langlands.Topology.LocallyProfiniteProof.vanDantzig (rationalPoints G)).mp
    (BruhatTits.rationalPoint_isLocallyProfinite F G) |>.2
      (K : Set (rationalPoints G)) (K.isOpen.mem_nhds K.one_mem)

/-- Coefficientwise moderate growth implies the finite-length uniform exponent
for the actual residue-normalized matrix norm. -/
theorem rationalFiniteLengthModerateGrowth_of_coefficientGrowth
    (hcoeff : RationalCoefficientModerateGrowthStatement.{u, uV}) :
    RationalFiniteLengthModerateGrowthStatement.{u, uV} := by
  intro F _ _ _ _ G hG
  let := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let := hG.smooth
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  intro n _ _ _ ρ hρ π hπ hfinite
  exact finiteLengthCoefficientGrowthUniformization
    (rationalPoints G) (rationalPoint_compactOpenCofinal F G)
    (rationalMatrixNorm F ρ) (one_le_rationalMatrixNorm F ρ)
    (rationalMatrixNorm_mul_le F ρ) π hπ hfinite
    (hcoeff F G hG n ρ hρ π hπ)

end Langlands.Plancherel
