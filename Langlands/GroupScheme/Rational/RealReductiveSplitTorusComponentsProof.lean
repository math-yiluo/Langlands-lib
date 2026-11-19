import Langlands.GroupScheme.Rational.RealReductiveSplitTorusComponentsStatement
import Langlands.GroupScheme.Rational.RealPointTopology
import Langlands.GroupScheme.Rational.RealAnisotropicCompactConnectedProof
import Langlands.GroupScheme.Rational.RootGeneratedCentralizerCovering
import Langlands.GroupScheme.Rational.TorusCentralizerFactorization
import Langlands.GroupScheme.Rational.TorusNormalizer
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.BruhatTits.Cartan.ActualCentralizerStructureProof
import Langlands.BruhatTits.RationalPoints.CentralSplitQuotientCompactness
import Langlands.GroupScheme.Reductive.CentralQuotientReductiveProof
import Langlands.AlgebraicGeometry.PointTopology.CompleteFieldSmoothOpenProof
import Langlands.GroupScheme.SmoothAffinePointLieGroup
import Langlands.AlgebraicGeometry.SmoothConnectedRelativeDimensionProof

/-! # A maximal split torus meets every real component of a reductive group -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.PointTopology
open Langlands.AlgebraicGeometry.PointManifold

local instance ringPointGroupInst (H : GroupScheme (Spec (CommRingCat.of ℝ))) :
    Group (RingPoint ℝ H.X ℝ) := H.ringPointGroup (CommAlgCat.of ℝ ℝ)

namespace RealSplitTorusComponents

/-- Postcomposition with a homomorphism of group schemes, as a homomorphism of the groups of
real points. -/
def ringPointHom {H G : GroupScheme (Spec (CommRingCat.of ℝ))} (f : H ⟶ G) :
    RingPoint ℝ H.X ℝ →* RingPoint ℝ G.X ℝ :=
  ((G.affinePointsRingPointMulEquiv (CommAlgCat.of ℝ ℝ)).toMonoidHom.comp
    (H.affinePointsTarget f (CommAlgCat.of ℝ ℝ))).comp
    (H.affinePointsRingPointMulEquiv (CommAlgCat.of ℝ ℝ)).symm.toMonoidHom

theorem ringPointHom_apply {H G : GroupScheme (Spec (CommRingCat.of ℝ))} (f : H ⟶ G)
    (p : RingPoint ℝ H.X ℝ) : ringPointHom f p = p ≫ f.hom.hom :=
  rfl

theorem continuous_ringPointHom {H G : GroupScheme (Spec (CommRingCat.of ℝ))}
    [IsAffine H.X.left] [IsAffine G.X.left] (f : H ⟶ G) :
    Continuous (ringPointHom f) :=
  continuous_affineSchemePointMap ℝ ℝ f.hom.hom

/-- The identity component maps into the identity component. -/
theorem ringPointHom_mem_connectedComponent_one {H G : GroupScheme (Spec (CommRingCat.of ℝ))}
    [IsAffine H.X.left] [IsAffine G.X.left] (f : H ⟶ G) {c : RingPoint ℝ H.X ℝ}
    (hc : c ∈ connectedComponent (1 : RingPoint ℝ H.X ℝ)) :
    ringPointHom f c ∈ connectedComponent (1 : RingPoint ℝ G.X ℝ) := by
  have h := (continuous_ringPointHom f).image_connectedComponent_subset
    (1 : RingPoint ℝ H.X ℝ)
  rw [map_one] at h
  exact h ⟨c, hc, rfl⟩

/-- **Quotient step.** Let `q : Z → Q` be a smooth fppf quotient by the image of `s : S → Z`.
If `Z(ℝ)` is locally connected and `Q(ℝ)` is connected, then `Z(ℝ) = Z(ℝ)⁰ · s(S(ℝ))`. -/
theorem exists_mem_connectedComponent_one_mul
    {Z Q : GroupScheme (Spec (CommRingCat.of ℝ))} [IsAffine Z.X.left] [IsAffine Q.X.left]
    {S : CommGroupScheme (Spec (CommRingCat.of ℝ))} (s : S.toGrp ⟶ Z) (q : Z ⟶ Q)
    [LocallyConnectedSpace (RingPoint ℝ Z.X ℝ)] [ConnectedSpace (RingPoint ℝ Q.X ℝ)]
    [Smooth q.hom.hom.left]
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range s) q)
    (z : RingPoint ℝ Z.X ℝ) :
    ∃ c ∈ connectedComponent (1 : RingPoint ℝ Z.X ℝ), ∃ t : RingPoint ℝ S.X ℝ,
      z = c * (ringPointHom s t : RingPoint ℝ Z.X ℝ) := by
  let π := ringPointHom q
  have hπ : IsOpenMap π := isOpenMap_affineSmoothPointMap ℝ q.hom.hom
  let H₀ := Subgroup.connectedComponentOfOne (RingPoint ℝ Z.X ℝ)
  have hH₀ : IsOpen (H₀ : Set (RingPoint ℝ Z.X ℝ)) := isOpen_connectedComponent
  have hopen : IsOpen ((H₀.map π : Subgroup (RingPoint ℝ Q.X ℝ)) : Set (RingPoint ℝ Q.X ℝ)) := by
    rw [Subgroup.coe_map]
    exact hπ _ hH₀
  have htop : ((H₀.map π : Subgroup (RingPoint ℝ Q.X ℝ)) : Set (RingPoint ℝ Q.X ℝ)) =
      Set.univ :=
    IsClopen.eq_univ ⟨Subgroup.isClosed_of_isOpen _ hopen, hopen⟩ ⟨1, (H₀.map π).one_mem⟩
  have hz : π z ∈ (H₀.map π : Subgroup (RingPoint ℝ Q.X ℝ)) := by
    rw [← SetLike.mem_coe, htop]
    trivial
  obtain ⟨c, hc, hcz⟩ := Subgroup.mem_map.mp hz
  have hk : (c⁻¹ * z) ≫ q.hom.hom = 1 := by
    change π (c⁻¹ * z) = 1
    rw [map_mul, map_inv, hcz, inv_mul_cancel]
  have hmem := (mem_range_kernelι_iff q (c⁻¹ * z)).mpr hk
  rw [hq.2.2.2] at hmem
  obtain ⟨t, ht⟩ := SubgroupFunctor.mem_range.mp hmem
  have ht' : ringPointHom s t = c⁻¹ * z := ht
  refine ⟨c, hc, t, ?_⟩
  rw [ht', mul_inv_cancel_left]

end RealSplitTorusComponents

open RealSplitTorusComponents

set_option linter.defProp false in
/-- **Matsumoto's theorem for reductive groups** (Borel–Tits 1965, 14.4): for a connected
reductive group `G` over `ℝ` and a maximal split torus `i : S → G`, every connected component of
`G(ℝ)` contains a point of `i(S(ℝ))`. This is a proved definition: its type is the proposition
`RealReductiveSplitTorusComponentsStatement`. -/
def realReductiveSplitTorusComponents : RealReductiveSplitTorusComponentsStatement := by
  intro G _ hG S i hi g
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : Smooth G.X.hom := hG.smooth
  have : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
  -- The centralizer `Z` of the maximal split torus, with `S` central maximal split in it.
  obtain ⟨ν, hν⟩ := hi.isSplitSubtorus.1.exists_genericCocharacter i
  let χ := CommGroupScheme.groupHom ν ≫ i
  let Z := Dynamic.Affine.centralizerScheme χ
  let j : Z ⟶ G := Dynamic.Affine.centralizerHom χ
  have hjc : IsClosedSubgroup j := Dynamic.Affine.isClosedSubgroup_centralizerHom χ
  have hjrep : (torusCentralizer i).IsRepresentedBy j := by
    rw [← genericCentralizer ℝ G hG S i hi ν hν]
    exact Dynamic.Affine.isRepresentedBy_centralizerHom χ
  let s := torusCentralizerFactor i hjrep
  have hs : s ≫ j = i := torusCentralizerFactor_comp i hjrep
  obtain ⟨hZ, -⟩ :=
    BruhatTits.Cartan.actualCentralizerStructure ℝ G hG S i hi Z j hjc hjrep s hs
  have hsmax : IsMaximalSplitTorus s :=
    hi.isMaximalSplitTorus_torusCentralizerFactor hjrep hjc
  have hscen : IsCentral s := isCentral_torusCentralizerFactor i hjrep
  have : IsAffineHom Z.X.hom := hZ.isAffineHom
  have : Smooth Z.X.hom := hZ.smooth
  have : IsAffine Z.X.left := isAffine_of_isAffineHom Z.X.hom
  -- The anisotropic quotient `Q = Z / S`.
  obtain ⟨Q, q, hQs, hQa, hQan, hqs, hq⟩ :=
    BruhatTits.RationalPoints.exists_smooth_anisotropic_central_split_quotient Z hsmax hscen
  have : Smooth Q.X.hom := hQs
  have : IsAffineHom Q.X.hom := hQa
  have : IsAffine Q.X.left := isAffine_of_isAffineHom Q.X.hom
  have : Smooth q.hom.hom.left := hqs
  have hQ : IsConnectedReductive Q :=
    centralQuotientReductive ℝ Z Q q (SubgroupFunctor.range s) hZ hQa inferInstance
      ((isCentral_iff_range_le_center s).mp hscen) hq
  have : ConnectedSpace (RingPoint ℝ Q.X ℝ) := (realAnisotropicCompactConnected Q hQ hQan).2
  obtain ⟨n, hn⟩ := Langlands.AlgebraicGeometry.smoothConnectedRelativeDimension
    Z.X.left _ Z.X.hom hZ.smooth hZ.connectedSpace
  let := realSmoothAffineChartedSpace Z.X n hn
  have : LocallyConnectedSpace (RingPoint ℝ Z.X ℝ) :=
    ChartedSpace.locallyConnectedSpace (Fin n → ℝ) _
  -- `G(ℝ) = G(ℝ)⁺ · Z(ℝ)`.
  let φ := RealPointTopology.rationalRingPointMulEquiv G
  obtain ⟨h, hh, z, hz, hg⟩ := exists_relativeRootGenerated_mul_centralizer hG hi (φ.symm g)
  have hz' : z ∈ (torusCentralizer i).carrier (Over.mk (𝟙 _)) :=
    centralizerPoints_le_torusCentralizer i hz
  rw [← hjrep.2] at hz'
  obtain ⟨z', rfl⟩ := SubgroupFunctor.mem_range.mp hz'
  -- `Z(ℝ) = Z(ℝ)⁰ · S(ℝ)`.
  obtain ⟨c, hc, t, hct⟩ := exists_mem_connectedComponent_one_mul s q hq
    (RealPointTopology.rationalRingPointMulEquiv Z z')
  refine ⟨t, ?_⟩
  have hφh : φ h ∈ connectedComponent (1 : RingPoint ℝ G.X ℝ) :=
    RealPointTopology.rootGenerated_le_identityComponentPreimage G i hh
  have hjc' : ringPointHom j c ∈ connectedComponent (1 : RingPoint ℝ G.X ℝ) :=
    ringPointHom_mem_connectedComponent_one j hc
  have hφz : φ (z' ≫ j.hom.hom) =
      ringPointHom j (RealPointTopology.rationalRingPointMulEquiv Z z') :=
    rationalPointEquiv_natural ℝ j.hom.hom z'
  have hgt : g = (φ h * ringPointHom j c) * ringPointHom i t := by
    have hg' : g = φ h * φ (z' ≫ j.hom.hom) := by
      rw [← map_mul, ← hg, MulEquiv.apply_symm_apply]
    rw [hg', hφz, hct, map_mul, mul_assoc]
    congr 2
    change (t ≫ s.hom.hom) ≫ j.hom.hom = t ≫ i.hom.hom
    rw [Category.assoc, ← hs]
    rfl
  let H₀ := Subgroup.connectedComponentOfOne (RingPoint ℝ G.X ℝ)
  have hmem : φ h * ringPointHom j c ∈ H₀ := H₀.mul_mem hφh hjc'
  have hcont : Continuous fun x : RingPoint ℝ G.X ℝ => x * ringPointHom i t :=
    continuous_id.mul continuous_const
  have hsub := hcont.image_connectedComponent_subset (1 : RingPoint ℝ G.X ℝ)
  simp only [one_mul] at hsub
  change ConnectedComponents.mk (α := RingPoint ℝ G.X ℝ) (ringPointHom i t) = _
  refine (ConnectedComponents.coe_eq_coe'.mpr ?_).symm
  rw [hgt]
  exact hsub ⟨_, hmem, rfl⟩

end Langlands.GroupScheme
