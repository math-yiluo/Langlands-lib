import Langlands.GroupScheme.Adjoint.SplitTorus
import Langlands.GroupScheme.Rational.RootAnnihilatorCentralityProof
import Langlands.GroupScheme.Rational.CentralRootRestriction
import Langlands.GroupScheme.Rational.RootAnnihilatorBaseChange
import Langlands.GroupScheme.Rational.RootSupportFiniteness

/-! # Root-annihilator kernels of the actual adjoint torus map -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme.RealTorusSpace

namespace Langlands.GroupScheme.IsAdjointSplitTorusImage

variable {k : Type u} [Field k]
  {G A : GroupScheme (Spec (CommRingCat.of k))}
  {T T_ad : CommGroupScheme (Spec (CommRingCat.of k))}
  {q : G ⟶ A} {i : T.toGrp ⟶ G} {j : T_ad.toGrp ⟶ A} {p : T ⟶ T_ad}
  (h : IsAdjointSplitTorusImage q i j p)

include h

/-- An actual cocharacter is killed by the adjoint torus map exactly when its
composite into the original group is central on every test scheme. -/
theorem cocharacter_comp_eq_zero_iff_isCentral (ν : cocharacterLattice T) :
    ν ≫ p = 0 ↔ IsCentral (CommGroupScheme.groupHom ν ≫ i) := by
  constructor
  · intro hν U x
    rw [Grp.comp_hom_hom, ← Category.assoc]
    apply (h.comp_eq_one_iff_mem_center U _).mp
    rw [← comp_groupHom_comp, hν, comp_groupHom_zero]
  · intro hc
    apply CommGroupScheme.hom_ext_points
    intro U x
    rw [comp_groupHom_zero, comp_groupHom_comp]
    apply (h.comp_eq_one_iff_mem_center U _).mpr
    simpa only [Grp.comp_hom_hom, Category.assoc] using hc U x

/-- The integral kernel is the simultaneous annihilator of the actual
relative roots; no claim about integral surjectivity is needed. -/
theorem ker_cocharacterMapInt_eq_rootAnnihilatorInt :
    haveI := h.isAdjointQuotient.isConnectedReductive.isAffineHom
    (cocharacterMapInt p).ker = rootAnnihilatorInt T (relativeRoots i) := by
  let := h.isAdjointQuotient.isConnectedReductive.isAffineHom
  let := h.isAdjointQuotient.isConnectedReductive.smooth
  let := h.isAdjointQuotient.isConnectedReductive.connectedSpace
  ext ν
  rw [LinearMap.mem_ker, mem_rootAnnihilatorInt]
  change ν ≫ p = 0 ↔ _
  rw [h.cocharacter_comp_eq_zero_iff_isCentral]
  constructor
  · intro hc α hα
    change gmEndEquiv k (ν ≫ α) = 0
    rw [root_restrict_eq_zero_of_isCentral i ν isSplitTorus_gm hc hα, map_zero]
  · exact rootAnnihilatorCentrality k G T h.sourceMaximal.1.1 i ν

/-- The full real kernel of the actual adjoint torus map is the published
common annihilator of all actual relative roots, including in rank zero. -/
theorem ker_cocharacterMapReal_eq_relativeCentralDirections :
    haveI := h.isAdjointQuotient.isConnectedReductive.isAffineHom
    (cocharacterMapReal p).ker = relativeCentralDirections i := by
  let := h.isAdjointQuotient.isConnectedReductive.isAffineHom
  let := h.isAdjointQuotient.isConnectedReductive.smooth
  let := (h.sourceMaximal.1.1.finite_relativeRoots i).fintype
  change (AlgebraTensorModule.lTensor ℝ ℝ (cocharacterMapInt p)).ker = _
  rw [Module.Flat.ker_lTensor_eq]
  change ((cocharacterMapInt p).ker).baseChange ℝ = _
  rw [h.ker_cocharacterMapInt_eq_rootAnnihilatorInt, rootAnnihilatorInt_baseChange]
  rfl

/-- The actual real adjoint-map kernel and the published relative central
subspace are identified by the identity on their ambient cocharacter vectors. -/
def realKernelEquivCentralDirections :
    haveI := h.isAdjointQuotient.isConnectedReductive.isAffineHom
    (cocharacterMapReal p).ker ≃ₗ[ℝ] relativeCentralDirections i := by
  let := h.isAdjointQuotient.isConnectedReductive.isAffineHom
  exact LinearEquiv.ofEq _ _ h.ker_cocharacterMapReal_eq_relativeCentralDirections

@[simp] theorem realKernelEquivCentralDirections_coe
    (v : (cocharacterMapReal p).ker) :
    haveI := h.isAdjointQuotient.isConnectedReductive.isAffineHom
    (h.realKernelEquivCentralDirections v : V T) = v := rfl

end Langlands.GroupScheme.IsAdjointSplitTorusImage
