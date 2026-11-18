import Langlands.GroupScheme.SimplyConnected.TypeE7RationalInversion
import Langlands.GroupScheme.SimplyConnected.KernelNormalizerAutomorphisms
import Langlands.GroupScheme.CenterInversionComparison
import Langlands.GroupScheme.Reductive.NormalCenterProof
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerProof

/-! # Actual E7 normalizer inversion on the full kernel centre -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.TitsIndexData

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G)

/-- The precise proposition implemented by `exists_normalizer_inverts_geometric_kernel_center_of_E7`. -/
def E7GeometricKernelCenterInversionStatement : Prop :=
  ∀ (_hsc : IsSimplyConnected G) (e : d.Vertex ≃ Fin 7)
    (_he : ∀ a b, d.cartan a b = CartanMatrix.E 7 (e a) (e b)),
    ∃ n : normalizerPoints d.splitInclusion,
      ∀ (U : Over (Spec (CommRingCat.of (SeparableClosure k))))
        (z : U ⟶ ((GroupScheme.baseChange
          (algebraBaseMap k (SeparableClosure k))).obj d.anisotropicKernelIndex.kernel).X),
        z ∈ (center ((GroupScheme.baseChange
          (algebraBaseMap k (SeparableClosure k))).obj d.anisotropicKernelIndex.kernel)).carrier U →
        z ≫ ((GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).map
          (d.anisotropicKernelIndex.normalizerKernelIso n).hom).hom.hom = z⁻¹

/-- An actual rational normalizer induces inversion on the entire geometric
centre of the actual anisotropic kernel, on every test scheme. -/
theorem exists_normalizer_inverts_geometric_kernel_center_of_E7
    (hsc : IsSimplyConnected G) (e : d.Vertex ≃ Fin 7)
    (he : ∀ a b, d.cartan a b = CartanMatrix.E 7 (e a) (e b)) :
    ∃ n : normalizerPoints d.splitInclusion,
      ∀ (U : Over (Spec (CommRingCat.of (SeparableClosure k))))
        (z : U ⟶ ((GroupScheme.baseChange
          (algebraBaseMap k (SeparableClosure k))).obj d.anisotropicKernelIndex.kernel).X),
        z ∈ (center ((GroupScheme.baseChange
          (algebraBaseMap k (SeparableClosure k))).obj d.anisotropicKernelIndex.kernel)).carrier U →
        z ≫ ((GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).map
          (d.anisotropicKernelIndex.normalizerKernelIso n).hom).hom.hom = z⁻¹ := by
  let b := algebraBaseMap k (SeparableClosure k)
  let F := GroupScheme.baseChange b
  let a := d.anisotropicKernelIndex
  let t := d.centralizerTorus a.represents
  obtain ⟨n, σ, m, hn, hσ, hm⟩ :=
    d.exists_rational_normalizer_and_geometric_inversion_of_E7 hsc e he
  dsimp only [GaloisPinningData.toSplitPinning] at m hm
  have hnK := hn.baseChangeBasePoint b
  rw [hσ] at hnK
  have hmS := hm.restrict_negIso ((CommGroupScheme.baseChange b).map d.torusMap)
  have hsquare : CommGroupScheme.groupHom ((CommGroupScheme.baseChange b).map d.torusMap) ≫
      F.map d.pinning.inclusion = F.map d.splitInclusion := by
    rw [← d.square, Functor.map_comp]
    rfl
  unfold IsNormalizingPoint at hmS
  rw [hsquare] at hmS
  have hC := d.centralizer_isConnectedReductive a.represents
  have hcenter : center a.kernel ≤ (center a.centralizer).comap a.derived :=
    normalReductiveCenter k a.centralizer a.kernel hC a.index.isSemisimple.isConnectedReductive
      a.derived a.isDerived.1 a.isDerived.isNormal
  have htorus : center a.centralizer ≤ SubgroupFunctor.range t := by
    rw [← maximalTorusCentralizer k a.centralizer hC d.pinning.torus t
      (d.isMaximalTorus_centralizerTorus a.represents)]
    exact center_le_torusCentralizer t
  have htorusK : center (F.obj a.centralizer) ≤ SubgroupFunctor.range (F.map t) := by
    rw [center_baseChange, SubgroupFunctor.range_baseChangeHom]
    exact SubgroupFunctor.baseChange_mono b htorus
  have hrepK : (torusCentralizer (T := (CommGroupScheme.baseChange b).obj d.splitTorus)
      (F.map d.splitInclusion)).IsRepresentedBy (F.map a.inclusion) := by
    rw [torusCentralizer_baseChange]
    exact a.represents.baseChange b
  have hmT : IsNormalizingPoint (T := (CommGroupScheme.baseChange b).obj d.pinning.torus)
      (F.map t ≫ F.map a.inclusion) m
      (SpecialLinearTorusAutomorphism.negIso ((CommGroupScheme.baseChange b).obj d.pinning.torus)) := by
    rw [← Functor.map_comp, centralizerTorus_comp]
    exact hm
  refine ⟨n, fun U z hz => ?_⟩
  have hinv := full_center_inversion_of_same_torus_action
    (B := Spec (CommRingCat.of (SeparableClosure k)))
    (T := (CommGroupScheme.baseChange b).obj d.pinning.torus)
    (A := (CommGroupScheme.baseChange b).obj d.splitTorus)
    (G := F.obj G) (C := F.obj a.centralizer) (D := F.obj a.kernel)
    (i := F.map d.splitInclusion) (j := F.map a.inclusion) (r := F.map a.derived)
    (F.map t) hrepK
    (center_le_comap_baseChange b a.derived hcenter) htorusK
    (n := baseChangeBasePoint b G n) (m := m)
    (σ := SpecialLinearTorusAutomorphism.negIso
      ((CommGroupScheme.baseChange b).obj d.splitTorus))
    hnK hmS hmT (U := U) (z := z) hz
  let : Mono a.derived.hom.hom := a.isDerived.isRepresentedBy.1
  let : Mono a.inclusion.hom.hom := a.represents.1
  have : Mono (F.map (a.derived ≫ a.inclusion)).hom.hom := by
    change Mono ((Over.pullback b).map (a.derived.hom.hom ≫ a.inclusion.hom.hom))
    infer_instance
  apply (cancel_mono (F.map (a.derived ≫ a.inclusion)).hom.hom).mp
  rw [GrpObj.inv_comp]
  have hsq := congrArg (fun f => F.map f) (a.normalizerKernelIso_hom_comp n)
  dsimp only [F] at hsq
  simp only [Functor.map_comp, baseChange_innerIso_hom] at hsq
  have hpt := congrArg (fun f => z ≫ f.hom.hom) hsq
  simp only [Grp.comp_hom_hom, ← Category.assoc] at hpt
  rw [comp_innerIso_hom] at hpt
  simpa only [Functor.map_comp, Grp.comp_hom_hom, ← Category.assoc] using hpt.trans hinv

end Langlands.GroupScheme.TitsIndexData
