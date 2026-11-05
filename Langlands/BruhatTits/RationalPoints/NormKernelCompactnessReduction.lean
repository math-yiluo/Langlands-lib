import Langlands.BruhatTits.RationalPoints.OpenHomCompactness
import Langlands.Representation.Plancherel.RationalNormKernelCentralCover
import Langlands.Representation.Plancherel.RationalNormKernelTopology

/-! # Compactness of an actual norm kernel through a compact central quotient -/

noncomputable section

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel

namespace Langlands.BruhatTits.RationalPoints

universe u v

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
  {T : Type v} [Group T] [TopologicalSpace T]

/-- Compactness of the actual rational common norm kernel through an open
continuous homomorphism with central kernel and compact Hausdorff target. -/
def NormKernelCompactnessThroughCentralQuotientStatement
    [IsTopologicalGroup T] [T2Space T] [CompactSpace T] : Prop :=
    haveI := hG.isAffineHom
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    ∀ q : rationalPoints G →ₜ* T, IsOpenMap q →
      q.ker ≤ Subgroup.center (rationalPoints G) →
      IsCompact (rationalCommonNormKernel G : Set (rationalPoints G))

/-- An open continuous homomorphism with central kernel and compact Hausdorff
target makes the actual rational common norm kernel compact. -/
theorem isCompact_rationalCommonNormKernel_of_open_central_quotient
    [IsTopologicalGroup T] [T2Space T] [CompactSpace T] :
    NormKernelCompactnessThroughCentralQuotientStatement (T := T) G hG := by
  let := hG.isAffineHom
  let := hG.smooth
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  let : T2Space F := BruhatTits.localField_t2Space F
  let : LocallyCompactSpace (rationalPoints G) := rationalPoint_locallyCompactSpace F G
  intro q hq hker
  have hkerclosed : IsClosed (q.ker : Set (rationalPoints G)) :=
    (isClosed_singleton (x := (1 : T))).preimage q.continuous
  have hinter :
      ((rationalCommonNormKernel G ⊓ q.ker : Subgroup (rationalPoints G)) :
        Set (rationalPoints G)) =
      ((rationalCommonNormKernel G ⊓ Subgroup.center (rationalPoints G) :
        Subgroup (rationalPoints G)) : Set (rationalPoints G)) ∩ q.ker := by
    ext g
    constructor
    · rintro ⟨hg, hqg⟩
      exact ⟨⟨hg, hker hqg⟩, hqg⟩
    · rintro ⟨⟨hg, _⟩, hqg⟩
      exact ⟨hg, hqg⟩
  apply isCompact_subgroup_of_isOpenMap_of_isCompact_inf_ker q.toMonoidHom hq
    (rationalCommonNormKernel G) (Plancherel.isOpen_rationalCommonNormKernel G)
  rw [hinter]
  exact (Plancherel.isCompact_rationalCommonNormKernel_inf_center G hG).inter_right
    hkerclosed

end Langlands.BruhatTits.RationalPoints
