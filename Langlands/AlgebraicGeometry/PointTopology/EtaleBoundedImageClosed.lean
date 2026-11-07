import Langlands.AlgebraicGeometry.PointTopology.AffineEtaleBoundedCluster
import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeMaps
import Langlands.AlgebraicGeometry.PointTopology.SchemePoints
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Étale maps are closed on locally bounded sets of rational points

Over a henselian ultrametric valued field `K`, let `p : W → V` be an étale morphism of
affine `K`-schemes. If a closed set `S` of rational points of `W` is locally bounded over
`V` (every global function of `W` is bounded on the points of `S` lying over a neighbourhood
of each rational point of `V`), then its image in `V(K)` is closed.
-/

noncomputable section

universe u

open CategoryTheory Filter Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {W V : Over (Spec (CommRingCat.of K))} [IsAffine W.left] [IsAffine V.left]

/-- **Étale images of locally bounded closed sets are closed.** -/
theorem isClosed_image_of_locallyBounded (hK : IsHenselianValuedField K) (p : W ⟶ V)
    (hp : Etale p.left) (S : Set (RingPoint K W K)) (hS : IsClosed S)
    (hloc : ∀ v : RingPoint K V K, ∃ N ∈ 𝓝 v, ∀ a : AffineCoordinateRing K W, ∃ C : ℝ,
      ∀ w ∈ S, (w ≫ p : RingPoint K V K) ∈ N → ‖affineSchemePointEquiv K W K w a‖ ≤ C) :
    IsClosed ((fun w : RingPoint K W K => (w ≫ p : RingPoint K V K)) '' S :
      Set (RingPoint K V K)) := by
  classical
  set g : RingPoint K W K → RingPoint K V K := fun w => w ≫ p with hg
  let eW := affineSchemePointHomeomorph K W K
  let eV := affineSchemePointHomeomorph K V K
  let Γp := affineCoordinatePullback K p
  have hnat : ∀ w : RingPoint K W K, eV (g w) = AlgPoint.precomp Γp (eW w) :=
    fun w => affineSchemePointEquiv_natural K K p w
  have hgcont : Continuous g := by
    have : g = eV.symm ∘ AlgPoint.precomp Γp ∘ eW := by
      funext w
      simp only [Function.comp_apply, ← hnat, Homeomorph.symm_apply_apply]
    rw [this]
    exact eV.symm.continuous.comp ((AlgPoint.continuous_precomp Γp).comp eW.continuous)
  let alg : Algebra (AffineCoordinateRing K V) (AffineCoordinateRing K W) :=
    Γp.toRingHom.toAlgebra
  have : IsScalarTower K (AffineCoordinateRing K V) (AffineCoordinateRing K W) :=
    IsScalarTower.of_algebraMap_eq fun c => (Γp.commutes c).symm
  have : Algebra.Etale (AffineCoordinateRing K V) (AffineCoordinateRing K W) := by
    have h := (HasRingHomProperty.iff_of_isAffine (P := @Etale) (f := p.left)).mp hp
    exact h
  refine isClosed_of_closure_subset fun v hv => ?_
  obtain ⟨N, hN, hNb⟩ := hloc v
  set l : Filter (RingPoint K W K) := comap g (𝓝 v) ⊓ 𝓟 S with hldef
  have hl : l.NeBot := by
    rw [hldef, Filter.inf_principal_neBot_iff]
    intro U hU
    obtain ⟨t, ht, htU⟩ := Filter.mem_comap.mp hU
    obtain ⟨_, htv, w, hwS, rfl⟩ := mem_closure_iff_nhds.mp hv t ht
    exact ⟨w, htU htv, hwS⟩
  have hlS : S ∈ l := Filter.mem_inf_of_right (Filter.mem_principal_self S)
  have hlN : g ⁻¹' N ∈ l := Filter.mem_inf_of_left (Filter.preimage_mem_comap hN)
  have hlg : Tendsto g l (𝓝 v) := tendsto_comap.mono_left inf_le_left
  let toHom : RingPoint K W K → (AffineCoordinateRing K W →ₐ[K] K) :=
    fun w => AlgPoint.toAlgHom (eW w)
  set L : Filter (AffineCoordinateRing K W →ₐ[K] K) := l.map toHom with hLdef
  have hL : L.NeBot := hl.map _
  have hbdd : ∀ a : AffineCoordinateRing K W, ∃ C : ℝ, ∀ᶠ φ in L, ‖φ a‖ ≤ C := by
    intro a
    obtain ⟨C, hC⟩ := hNb a
    refine ⟨C, Filter.eventually_map.mpr ?_⟩
    filter_upwards [hlS, hlN] with w hwS hwN
    exact hC w hwS hwN
  have hconv : ∀ r : AffineCoordinateRing K V,
      Tendsto (fun φ : AffineCoordinateRing K W →ₐ[K] K =>
        φ (algebraMap (AffineCoordinateRing K V) (AffineCoordinateRing K W) r)) L
          (𝓝 (AlgPoint.toAlgHom (eV v) r)) := by
    intro r
    rw [hLdef, tendsto_map'_iff]
    have : (fun φ : AffineCoordinateRing K W →ₐ[K] K =>
        φ (algebraMap (AffineCoordinateRing K V) (AffineCoordinateRing K W) r)) ∘ toHom =
          (fun q : AlgPoint K (AffineCoordinateRing K V) K => q r) ∘ eV ∘ g := by
      funext w
      simp only [Function.comp_apply, hnat]
      rfl
    rw [this]
    exact ((AlgPoint.continuous_eval r).comp eV.continuous).continuousAt.tendsto.comp hlg
  obtain ⟨φ₀, hres, L', hL'L, hL'ne, hφ₀⟩ :=
    EtaleBoundedCluster.exists_tendsto_of_bounded hK L hbdd (AlgPoint.toAlgHom (eV v)) hconv
  have htend : Tendsto (fun φ : AffineCoordinateRing K W →ₐ[K] K => AlgPoint.ofAlgHom φ) L'
      (𝓝 (AlgPoint.ofAlgHom φ₀)) := by
    rw [AlgPoint.isEmbedding_evaluation.tendsto_nhds_iff, tendsto_pi_nhds]
    exact hφ₀
  have hSc : IsClosed (eW '' S) := eW.isClosedMap S hS
  have hev : ∀ᶠ φ in L', AlgPoint.ofAlgHom φ ∈ eW '' S := by
    refine hL'L (Filter.mem_map.mpr ?_)
    filter_upwards [hlS] with w hw
    exact ⟨w, hw, rfl⟩
  obtain ⟨w₀, hw₀S, hw₀⟩ := hSc.mem_of_tendsto htend hev
  refine ⟨w₀, hw₀S, eV.injective ?_⟩
  apply AlgPoint.ext
  intro r
  rw [hnat, AlgPoint.precomp_apply, hw₀]
  exact hres r

end Langlands.AlgebraicGeometry.PointTopology
