import Langlands.GroupScheme.SpecialLinearCentralScalars
import Langlands.GroupScheme.CentralSimpleNormOneSplitting
import Langlands.GroupScheme.SimplyConnected.AnisotropicInnerTypeADivisionModel
import Langlands.Algebra.CentralSimple.SeparableClosureChart

/-! # Central points not fixed by inversion in actual norm-one models -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

/-- A special-linear group of degree greater than two has a central test point
not fixed by inversion, over every nontrivial commutative base ring. -/
theorem SpecialLinear.exists_central_inv_ne (n : ℕ) (R : CommRingCat.{u})
    [Nontrivial R] (hn : 2 < n) :
    ∃ (T : Over (Spec R)) (z : T ⟶ (SpecialLinear.groupScheme (Fin n) R).X),
      z ∈ (center (SpecialLinear.groupScheme (Fin n) R)).carrier T ∧ z⁻¹ ≠ z := by
  let f := Spec.map (CommRingCat.ofHom
    (algebraMap R (AdjoinRoot (MuAffinePresentation.equation R n))))
  let T : Over (Spec R) := Over.mk f
  let x : T ⟶ (mu (Spec R) n).X :=
    (mu.affinePointsEquiv n f).symm (MuAffinePresentation.coordinate R n (by omega))
  have hz : SpecialLinear.scalarRootPoints n R T x ∈
      (center (SpecialLinear.groupScheme (Fin n) R)).carrier T := by
    rw [← SpecialLinear.comp_scalarRootsOfUnityHom]
    exact SpecialLinear.isCentral_scalarRootsOfUnityHom n R T x
  refine ⟨T, SpecialLinear.scalarRootPoints n R T x, hz, fun h => ?_⟩
  have hx : x⁻¹ = x := SpecialLinear.scalarRootPoints_injective n R (by omega) T (by
    simpa only [map_inv] using h)
  have hu := congrArg (mu.affinePointsEquiv n f) hx
  rw [map_inv] at hu
  change ((mu.affinePointsEquiv n f)
      ((mu.affinePointsEquiv n f).symm
        (MuAffinePresentation.coordinate R n (by omega))))⁻¹ =
    (mu.affinePointsEquiv n f)
      ((mu.affinePointsEquiv n f).symm
        (MuAffinePresentation.coordinate R n (by omega))) at hu
  rw [MulEquiv.apply_symm_apply] at hu
  exact SpecialLinear.universalCoordinate_inv_ne n R hn hu

/-- An actual group-scheme isomorphism transports a central point moved by inversion. -/
theorem exists_central_inv_ne_of_iso {B : Scheme.{u}} {G H : GroupScheme B}
    (e : G ≅ H)
    (h : ∃ (T : Over B) (z : T ⟶ G.X), z ∈ (center G).carrier T ∧ z⁻¹ ≠ z) :
    ∃ (T : Over B) (z : T ⟶ H.X), z ∈ (center H).carrier T ∧ z⁻¹ ≠ z := by
  obtain ⟨T, z, hz, hne⟩ := h
  refine ⟨T, z ≫ e.hom.hom.hom, mem_center_comp_iso e hz, fun he => ?_⟩
  apply hne
  apply (cancel_mono e.hom.hom.hom).mp
  simpa only [GrpObj.inv_comp] using he

/-- The precise proposition implemented by `HasCentralDivisionNormOnePresentation.exists_geometric_central_inv_ne`. -/
def HasCentralDivisionNormOnePresentation.GeometricCentralNonInvolutionStatement : Prop :=
  ∀ {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    {n : ℕ} (_h : HasCentralDivisionNormOnePresentation G n) (_hn : 2 < n),
    ∃ (T : Over (Spec (CommRingCat.of (SeparableClosure k))))
      (z : T ⟶ ((GroupScheme.baseChange
        (algebraBaseMap k (SeparableClosure k))).obj G).X),
      z ∈ (center ((GroupScheme.baseChange
        (algebraBaseMap k (SeparableClosure k))).obj G)).carrier T ∧ z⁻¹ ≠ z

/-- Every actual central-division norm-one presentation of degree greater than
two has a geometric central test point not fixed by inversion. -/
theorem HasCentralDivisionNormOnePresentation.exists_geometric_central_inv_ne
    {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    {n : ℕ} (h : HasCentralDivisionNormOnePresentation G n) (hn : 2 < n) :
    ∃ (T : Over (Spec (CommRingCat.of (SeparableClosure k))))
      (z : T ⟶ ((GroupScheme.baseChange
        (algebraBaseMap k (SeparableClosure k))).obj G).X),
      z ∈ (center ((GroupScheme.baseChange
        (algebraBaseMap k (SeparableClosure k))).obj G)).carrier T ∧ z⁻¹ ≠ z := by
  obtain ⟨D, _, _, _, _, hdegree, ⟨e⟩⟩ := h
  let E := ((GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).mapIso e).trans
    (CentralSimpleUnits.Splitting.splittingIso k D
      (Langlands.CentralSimple.separableClosureChart k D))
  apply exists_central_inv_ne_of_iso E.symm
  exact SpecialLinear.exists_central_inv_ne (Langlands.CentralSimple.reducedDegree k D)
    (CommRingCat.of (SeparableClosure k)) (by rw [hdegree]; exact hn)

end Langlands.GroupScheme
