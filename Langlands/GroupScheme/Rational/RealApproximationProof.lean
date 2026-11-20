import Langlands.AlgebraicGeometry.PointTopology.AffineBaseChangeTopologyProof
import Langlands.AlgebraicGeometry.PointTopology.RationalPointGroups
import Langlands.GroupScheme.Rational.RealApproximationReductiveReductionProof
import Langlands.GroupScheme.Rational.RealMaximalTorusApproximation
import Langlands.GroupScheme.Rational.RealToralPoints
import Langlands.GroupScheme.Torus.RealTorusApproximation

/-! # Real approximation for connected affine groups over the rationals -/

noncomputable section

open CategoryTheory Topology
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

private theorem constantPoint_ringTest_eq {k : Type} [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (p : RingPoint k G.X k) :
    G.constantPoint ((rationalPointEquiv k G.X).symm p) (ringTest k k) = p := by
  apply RingPoint.ext
  change Spec.algebraMap k k ≫ ((rationalPointEquiv k G.X).symm p).left = p.left
  rw [rationalPointEquiv_symm_left]
  simp [Spec.algebraMap]

/-- The reductive case of real approximation, by local approximation of real maximal tori. -/
private theorem reductiveRealApproximation : ReductiveRealApproximationStatement := by
  intro G _ hG
  let b := algebraBaseMap ℚ ℝ
  let bc := GroupScheme.baseChange b
  let G_R := bc.obj G
  let : IsAffine G_R.X.left := ringBaseChange_isAffine ℚ ℝ G.X
  have hGR : IsConnectedReductive G_R := connectedReductiveFieldExtensionStatement ℚ ℝ G hG
  let : Smooth G_R.X.hom := hGR.smooth
  let : Group (RingPoint ℝ G_R.X ℝ) := inferInstanceAs (Group (ringTest ℝ ℝ ⟶ G_R.X))
  let : IsTopologicalGroup (RingPoint ℝ G_R.X ℝ) := affineGroupTopological_proof ℝ ℝ G_R
  let eG : RingPoint ℚ G.X ℝ ≃ RingPoint ℝ G_R.X ℝ := ringPointBaseChangeEquiv ℚ ℝ ℝ G.X
  have heG : IsHomeomorph eG := isHomeomorph_ringPointBaseChangeEquiv ℚ ℝ ℝ G.X
  apply dense_iff_inter_open.mpr
  intro W hW hnW
  let V := eG '' W
  have hV : IsOpen V := heG.isOpenMap W hW
  obtain ⟨p, hp, T, j, hj, t, ht⟩ :=
    (realToralPointsDense G_R hGR).inter_open_nonempty V hV (hnW.image eG)
  let U : Set (RingPoint ℝ G_R.X ℝ) := {a | a * p * a⁻¹ ∈ V}
  have hU : IsOpen U := hV.preimage ((continuous_id.mul continuous_const).mul continuous_inv)
  have h1 : rationalPointEquiv ℝ G_R.X (1 : RationalPoint ℝ G_R.X) ∈ U := by
    change rationalPointGroupEquiv ℝ G_R 1 * p * (rationalPointGroupEquiv ℝ G_R 1)⁻¹ ∈ V
    simpa only [map_one, one_mul, inv_one, mul_one] using hp
  obtain ⟨g, hg, P, i, hi, E, hE⟩ := realMaximalTorusApproximation G hG T j hj U hU h1
  let P_R := bc.obj P.toGrp
  let i_R := bc.map i
  let x : RingPoint ℝ P_R.X ℝ := t ≫ E.hom.hom.hom
  let g₀ := (rationalPointEquiv ℝ G_R.X).symm g
  have hE' : E.hom.hom.hom ≫ i_R.hom.hom = j.hom.hom ≫ (G_R.innerIso g₀).hom.hom.hom := by
    change (E.hom ≫ i_R).hom.hom = _
    rw [hE, Grp.comp_hom_hom]
  have hx : (x ≫ i_R.hom.hom) ∈ V := by
    change (t ≫ E.hom.hom.hom) ≫ i_R.hom.hom ∈ V
    rw [Category.assoc, hE', ← Category.assoc, ht, comp_innerIso_hom]
    let a : RingPoint ℝ G_R.X ℝ := G_R.constantPoint g₀ (ringTest ℝ ℝ)
    have ha : a = g := constantPoint_ringTest_eq G_R g
    change a * p * a⁻¹ ∈ V
    rwa [ha]
  let : IsAffine P.X.left := SplittingAssembly.isAffine_of_isTorus P.toGrp hi.1
  let q := (ringPointBaseChangeEquiv ℚ ℝ ℝ P.X).symm x
  have hqx : eG (q ≫ i.hom.hom) = x ≫ i_R.hom.hom := by
    change ringPointBaseChangeEquiv ℚ ℝ ℝ G.X (q ≫ i.hom.hom) = _
    rw [ringPointBaseChangeEquiv_natural]
    change ringPointBaseChangeEquiv ℚ ℝ ℝ P.X ((ringPointBaseChangeEquiv ℚ ℝ ℝ P.X).symm x) ≫
      i_R.hom.hom = _
    rw [Equiv.apply_symm_apply]
  have hq : (q ≫ i.hom.hom) ∈ W := by
    obtain ⟨y, hy, heq⟩ := hx
    exact (eG.injective (heq.trans hqx.symm)) ▸ hy
  let H : RingPoint ℚ P.X ℝ → RingPoint ℚ G.X ℝ := fun y => y ≫ i.hom.hom
  have hH : Continuous H := continuous_affineSchemePointMap ℚ ℝ i.hom.hom
  obtain ⟨r, hr⟩ := (torusRealApproximation P hi.1).exists_mem_open (hW.preimage hH) ⟨q, hq⟩
  let r_G : RingPoint ℚ G.X ℚ := r ≫ i.hom.hom
  refine ⟨r_G.changeRing (Algebra.ofId ℚ ℝ), ?_, ⟨r_G, rfl⟩⟩
  change ((r.changeRing (Algebra.ofId ℚ ℝ)) ≫ i.hom.hom : RingPoint ℚ G.X ℝ) ∈ W
  exact hr

/-- **Real approximation** (Milne, *Algebraic Groups*, Theorem 25.70). -/
theorem realApproximation : RealApproximationStatement :=
  realApproximationReductiveReduction reductiveRealApproximation

end Langlands.GroupScheme
