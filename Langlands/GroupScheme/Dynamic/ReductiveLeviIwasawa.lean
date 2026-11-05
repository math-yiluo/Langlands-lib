import Langlands.GroupScheme.Dynamic.RCLikeLeviIwasawa
import Langlands.GroupScheme.Reductive.SelfAdjointRealizationProof

/-! # Actual Levi-compatible Iwasawa for reductive dynamic pairs -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [RCLike k]
  {G P M : GroupScheme (Spec (CommRingCat.of k))}

/-- Reductivity supplies the ambient closed star realization over every
real or complex coefficient field. -/
theorem IsConnectedReductive.hasClosedStarRealization (hG : IsConnectedReductive G) :
    MatrixRepresentation.HasClosedStarRealization G :=
  SelfAdjointRealization.connectedReductiveSelfAdjointRealizationStatement k G hG

/-- A common dynamic cocharacter of a connected reductive group admits
compatible Hermitian realization without a supplied matrix representation. -/
theorem IsConnectedReductive.hasHermitianStarLeviRealization
    (hG : IsConnectedReductive G)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    {p : P ⟶ G} {m : M ⟶ G}
    (hp : (Dynamic.parabolic χ).IsRepresentedBy p)
    (hm : (Dynamic.centralizer χ).IsRepresentedBy m) :
    Dynamic.HasHermitianStarLeviRealization p m :=
  hG.hasClosedStarRealization.hasRCLikeHermitianStarLeviRealization χ hp hm

/-- Compatible diagonal data for an actual reductive dynamic pair. -/
theorem IsConnectedReductive.hasDiagonalStarLeviRealization
    (hG : IsConnectedReductive G)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    {p : P ⟶ G} {m : M ⟶ G}
    (hp : (Dynamic.parabolic χ).IsRepresentedBy p)
    (hm : (Dynamic.centralizer χ).IsRepresentedBy m) :
    Dynamic.HasDiagonalStarLeviRealization p m :=
  (hG.hasHermitianStarLeviRealization χ hp hm).hasDiagonalStarLeviRealization

local instance reductiveLeviIwasawaPointTopology
    (H : GroupScheme (Spec (CommRingCat.of k))) :
    TopologicalSpace (H.affinePoints (CommAlgCat.of k k)) :=
  H.affinePointsTopologicalSpace (CommAlgCat.of k k)

/-- All four actual-point conclusions for a reductive dynamic pair. The
only supplied structural data are reductivity and the common cocharacter. -/
theorem IsConnectedReductive.hasLeviCompatibleDecomposition
    (hG : IsConnectedReductive G)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    {p : P ⟶ G} {m : M ⟶ G}
    (hp : (Dynamic.parabolic χ).IsRepresentedBy p)
    (hm : (Dynamic.centralizer χ).IsRepresentedBy m) :
    CompactIwasawa.HasLeviCompatibleDecomposition
      (P.affinePointsTarget p (CommAlgCat.of k k))
      (M.affinePointsTarget m (CommAlgCat.of k k)) := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  exact (hG.hasDiagonalStarLeviRealization χ hp hm).hasLeviCompatibleDecomposition

namespace Dynamic

/-- A chosen compatible compact subgroup for the actual points of a
connected reductive group with a specified dynamic pair. -/
def reductiveLeviIwasawaCompact
    (hG : IsConnectedReductive G)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    {p : P ⟶ G} {m : M ⟶ G}
    (hp : (parabolic χ).IsRepresentedBy p)
    (hm : (centralizer χ).IsRepresentedBy m) :
    Subgroup (G.affinePoints (CommAlgCat.of k k)) :=
  Classical.choose (hG.hasLeviCompatibleDecomposition χ hp hm)

/-- The chosen subgroup has ambient maximal compactness, parabolic
coverage, the specified Levi intersection, and Levi maximal compactness. -/
theorem reductiveLeviIwasawaCompact_spec
    (hG : IsConnectedReductive G)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    {p : P ⟶ G} {m : M ⟶ G}
    (hp : (parabolic χ).IsRepresentedBy p)
    (hm : (centralizer χ).IsRepresentedBy m) :
    CompactIwasawa.IsLeviCompatibleDecomposition
      (P.affinePointsTarget p (CommAlgCat.of k k))
      (M.affinePointsTarget m (CommAlgCat.of k k))
      (reductiveLeviIwasawaCompact hG χ hp hm) :=
  Classical.choose_spec (hG.hasLeviCompatibleDecomposition χ hp hm)

end Dynamic

end Langlands.GroupScheme
