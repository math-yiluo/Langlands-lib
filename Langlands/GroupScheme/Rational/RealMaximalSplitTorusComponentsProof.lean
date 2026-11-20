import Langlands.GroupScheme.Rational.RealMaximalSplitTorusComponentsStatement
import Langlands.GroupScheme.Rational.RealReductiveSplitTorusComponentsProof
import Langlands.GroupScheme.Rational.RealPointTopology
import Langlands.GroupScheme.Reductive.CharacteristicZeroLeviProof
import Langlands.GroupScheme.Unipotent.PerfectFieldSplitProof
import Langlands.GroupScheme.Unipotent.SplitAffineSpaceProof
import Langlands.GroupScheme.Torus.UnipotentQuotientMaximalSplit
import Langlands.GroupScheme.FiniteFreeAlgebraUnitsQuotient
import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeMapProofs

/-! # Every real component meets a maximal split torus -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Topology
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.PointTopology

namespace RealMaximalSplitTorusComponents

open RealSplitTorusComponents

local instance ringPointGroupInst (H : GroupScheme (Spec (CommRingCat.of ℝ))) :
    Group (RingPoint ℝ H.X ℝ) := H.ringPointGroup (CommAlgCat.of ℝ ℝ)

/-- Left multiplication by a point of the identity component stays in the component. -/
theorem mul_mem_connectedComponent {X : Type*} [TopologicalSpace X] [Group X]
    [ContinuousMul X] {c : X} (hc : c ∈ connectedComponent (1 : X)) (y : X) :
    c * y ∈ connectedComponent y := by
  have hf : Continuous fun x : X => x * y := continuous_id.mul continuous_const
  have h := hf.image_connectedComponent_subset (1 : X) ⟨c, hc, rfl⟩
  change c * y ∈ connectedComponent (1 * y) at h
  rwa [one_mul] at h

/-- Right multiplication by a point of the identity component stays in the component. -/
theorem mul_mem_connectedComponent' {X : Type*} [TopologicalSpace X] [Group X]
    [ContinuousMul X] {c : X} (hc : c ∈ connectedComponent (1 : X)) (y : X) :
    y * c ∈ connectedComponent y := by
  have hf : Continuous fun x : X => y * x := continuous_const.mul continuous_id
  have h := hf.image_connectedComponent_subset (1 : X) ⟨c, hc, rfl⟩
  change y * c ∈ connectedComponent (y * 1) at h
  rwa [mul_one] at h

/-- The real points of a smooth connected unipotent affine group over `ℝ` form a connected
space: the group is split, hence isomorphic as a scheme to affine space. -/
theorem connectedSpace_of_isUnipotent (U : GroupScheme (Spec (CommRingCat.of ℝ)))
    [IsAffine U.X.left] [Smooth U.X.hom] (hUc : ConnectedSpace U.X.left)
    (hUu : IsUnipotent U) : ConnectedSpace (RingPoint ℝ U.X ℝ) := by
  obtain ⟨n, hn⟩ := perfectFieldUnipotentSplit ℝ U hUc hUu
  obtain ⟨e⟩ := splitUnipotentAffineSpaceStatement ℝ n U inferInstance hn
  let I := ULift.{0} (Fin n)
  let eA : Over.mk (𝔸(I; Spec (CommRingCat.of ℝ)) ↘ Spec (CommRingCat.of ℝ)) ≅
      ringTest ℝ (MvPolynomial I ℝ) :=
    (Over.isoMk (AffineSpace.SpecIso I (CommRingCat.of ℝ)).symm
      (AffineSpace.SpecIso_inv_over (n := I) (CommRingCat.of ℝ))).symm
  let h := ((affinePresentationPointHomeomorph ℝ ℝ (MvPolynomial I ℝ) (e ≪≫ eA)).trans
    (specPointHomeomorph ℝ (MvPolynomial I ℝ) ℝ)).trans
      (AlgPoint.polynomialPointHomeomorph I)
  exact h.connectedSpace_iff.mpr inferInstance

/-- If the real points of the kernel of `p` form a connected space, then every real point of
`G` killed by `p` lies in the identity component of `G(ℝ)`. -/
theorem mem_connectedComponent_one_of_comp_eq_one
    {G L : GroupScheme (Spec (CommRingCat.of ℝ))} [IsAffine G.X.left] [IsAffine L.X.left]
    (p : G ⟶ L) [IsAffine (kernel p).X.left] [ConnectedSpace (RingPoint ℝ (kernel p).X ℝ)]
    {a : RingPoint ℝ G.X ℝ} (ha : a ≫ p.hom.hom = 1) :
    a ∈ connectedComponent (1 : RingPoint ℝ G.X ℝ) := by
  let k : RingPoint ℝ (kernel p).X ℝ :=
    (kernel_isPullback p).lift a (toUnit (ringTest ℝ ℝ)) ha
  have hk : k ≫ (kernelι p).hom.hom = a := (kernel_isPullback p).lift_fst _ _ _
  have h1 : (1 : RingPoint ℝ (kernel p).X ℝ) ≫ (kernelι p).hom.hom = 1 := MonObj.one_comp _
  exact (isPreconnected_range (continuous_affineSchemePointMap ℝ ℝ (kernelι p).hom.hom))
    |>.subset_connectedComponent ⟨1, h1⟩ ⟨k, hk⟩

/-- **Reduction to the reductive case.** The characteristic-zero Levi decomposition reduces
`RealMaximalSplitTorusComponentsStatement` to connected reductive groups. -/
theorem of_reductive (hred : RealReductiveSplitTorusComponentsStatement) :
    RealMaximalSplitTorusComponentsStatement := by
  intro G _ _ _ S i hi g
  obtain ⟨L, p, j, hjp, hL, hUsm, hUc, hUu⟩ :=
    characteristicZeroLeviDecomposition ℝ G inferInstance inferInstance
  have : IsAffineHom L.X.hom := hL.isAffineHom
  have : IsAffine L.X.left := isAffine_of_isAffineHom L.X.hom
  have : Smooth L.X.hom := hL.smooth
  have : Smooth (kernel p).X.hom := hUsm
  have : ConnectedSpace (kernel p).X.left := hUc
  have : IsAffine (kernel p).X.left := IsAffine.of_isPullback (kernel_isPullback_scheme p)
  -- `i ≫ p` is a maximal split torus of the reductive quotient `L`.
  have hn : IsClosedSubgroup (kernelι p) :=
    inferInstanceAs (IsClosedImmersion (kernelι p).hom.hom.left)
  have hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (kernelι p)) p :=
    SectionQuotient.isFppfQuotient_of_section p j hjp
  have hip : IsMaximalSplitTorus (i ≫ p) :=
    (IsMaximalSplitTorus.comp_iff_of_perfect_field_unipotent_kernel (kernelι p) hn hUu p hq
      i).mpr hi
  -- The real points of the unipotent kernel are connected.
  have : ConnectedSpace (RingPoint ℝ (kernel p).X ℝ) :=
    connectedSpace_of_isUnipotent (kernel p) hUc hUu
  obtain ⟨t, ht⟩ := hred L hL S (i ≫ p) hip (g ≫ p.hom.hom)
  refine ⟨t, ?_⟩
  have hjp' : j.hom.hom ≫ p.hom.hom = 𝟙 L.X := congrArg (fun q => q.hom.hom) hjp
  -- `x = i(t)`, `y = j(p(g))` and `z = j(p(x))`.
  let x : RingPoint ℝ G.X ℝ := t ≫ i.hom.hom
  let y : RingPoint ℝ G.X ℝ := (g ≫ p.hom.hom) ≫ j.hom.hom
  let z : RingPoint ℝ G.X ℝ := (x ≫ p.hom.hom) ≫ j.hom.hom
  have hpy : ringPointHom p y = ringPointHom p g := by
    change ((g ≫ p.hom.hom) ≫ j.hom.hom) ≫ p.hom.hom = g ≫ p.hom.hom
    rw [Category.assoc, hjp', Category.comp_id]
  have hpz : ringPointHom p z = ringPointHom p x := by
    change ((x ≫ p.hom.hom) ≫ j.hom.hom) ≫ p.hom.hom = x ≫ p.hom.hom
    rw [Category.assoc, hjp', Category.comp_id]
  -- The images of `x` and `g` in `L(ℝ)` lie in one component, hence so do `z` and `y`.
  have hxl : ringPointHom p x ∈ connectedComponent (ringPointHom p g) := by
    have h := ConnectedComponents.coe_eq_coe'.mp ht
    change (t ≫ i.hom.hom) ≫ p.hom.hom ∈
      connectedComponent (α := RingPoint ℝ L.X ℝ) (g ≫ p.hom.hom)
    simpa only [Grp.comp_hom_hom, Over.comp_left, Category.assoc] using h
  have hj : z ∈ connectedComponent y :=
    (continuous_ringPointHom j).image_connectedComponent_subset _ ⟨_, hxl, rfl⟩
  -- The differences `g y⁻¹` and `x⁻¹ z` lie in the kernel, hence in the identity component.
  have ha : ringPointHom p (g * y⁻¹) = 1 := by
    rw [map_mul, map_inv, hpy, mul_inv_cancel]
  have hb : ringPointHom p (x⁻¹ * z) = 1 := by
    rw [map_mul, map_inv, hpz, inv_mul_cancel]
  have hg : g ∈ connectedComponent y := by
    have h := mul_mem_connectedComponent
      (mem_connectedComponent_one_of_comp_eq_one p (a := g * y⁻¹) ha) y
    rwa [inv_mul_cancel_right] at h
  have hx : z ∈ connectedComponent x := by
    have h := mul_mem_connectedComponent'
      (mem_connectedComponent_one_of_comp_eq_one p (a := x⁻¹ * z) hb) x
    rwa [mul_inv_cancel_left] at h
  exact ConnectedComponents.coe_eq_coe.mpr
    ((connectedComponent_eq hx).trans ((connectedComponent_eq hj).symm.trans
      (connectedComponent_eq hg)))

end RealMaximalSplitTorusComponents

/-- **Matsumoto's theorem** (Borel–Tits 1965, Theorem 14.4): for a smooth connected affine
group `G` over `ℝ` and a maximal split torus `i : S → G`, every connected component of `G(ℝ)`
contains a point of `i(S(ℝ))`. -/
theorem realMaximalSplitTorusComponents : RealMaximalSplitTorusComponentsStatement :=
  RealMaximalSplitTorusComponents.of_reductive realReductiveSplitTorusComponents

end Langlands.GroupScheme
