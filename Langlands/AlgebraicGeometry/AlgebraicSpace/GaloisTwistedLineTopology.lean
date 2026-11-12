import Langlands.AlgebraicGeometry.AlgebraicSpace.GaloisTwistedLinePoints

/-!
# The image of `X(K)` in `X_{K'}(K')` is not closed

Let `K'/K` be an extension of nontrivially normed fields with a `QuadraticConj` structure, and
let `X` be the Galois-twisted line over `K`. The base change of the atlas `U → X` is an étale
chart of finite type of `X_{K'}`, so the points `a(u_s)`, `s ∈ K'`, depend continuously on `s`
for the étale-chart topology of `X_{K'}(K')`. For `c ∈ K` nonzero they lie in the image of
`X(K)`, and `a(u_0)` does not. Taking `c = p₀ⁿ` with `0 < ‖p₀‖ < 1` shows that the image is not
closed.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite Topology Polynomial Filter
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
  (RingPoint ringTest ringTestMap schemePointTopology schemePointTopology_eq_affine
    ringBaseChange ringPointBaseChangeEquiv schemeBaseChangeTopology_proof affineRingPointEquiv
    spectrumAlgebraPointHomeomorph AlgPoint)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace GaloisTwistedLine

open HenselianIntegralPointsNotClosed

variable {K K' : Type u} [NontriviallyNormedField K] [NontriviallyNormedField K']
  [NormedAlgebra K K']

/-- The algebra maps out of `A` are the points of `Spec A`. -/
theorem affineRingPointEquiv_ringTestMap' {R A T : Type u} [CommRing R] [CommRing A]
    [CommRing T] [Algebra R A] [Algebra R T] (φ : A →ₐ[R] T) :
    affineRingPointEquiv R A T (ringTestMap R φ) = φ := by
  apply AlgHom.coe_ringHom_injective
  change (Spec.preimage (Spec.map (CommRingCat.ofHom φ.toRingHom))).hom = φ.toRingHom
  rw [Spec.preimage_map]
  rfl

variable (K) in
/-- The point with coordinate `s`, as a point of the affine scheme `Spec K'[X]` over `K`. -/
def linePoint (s : K') : RingPoint K (ringTest K K'[X]) K' := linePt K s

/-- The points of the line depend continuously on the coordinate. -/
theorem continuous_linePoint :
    Continuous[_, schemePointTopology K (ringTest K K'[X]) K'] (linePoint K (K' := K')) := by
  rw [schemePointTopology_eq_affine]
  rw [← (spectrumAlgebraPointHomeomorph K K' K'[X]).comp_continuous_iff, AlgPoint.continuous_iff]
  intro q
  change Continuous fun s : K' =>
    affineRingPointEquiv K K'[X] K' (ringTestMap K ((aeval s).restrictScalars K)) q
  simp only [affineRingPointEquiv_ringTestMap', AlgHom.coe_restrictScalars']
  exact Polynomial.continuous_aeval q

variable (D : QuadraticConj K K') [Module.Finite K K']

/-- **The image of `X(K)` in `X_{K'}(K')` is not closed** for the Galois-twisted line. -/
theorem not_isClosed_range :
    ¬ @IsClosed _ (etaleChartTopology K' (baseChange (Spec.algebraMap K K') (space D)))
      (Set.range fun x : RingPoints K (space D) K =>
        (baseChangeRingPointsEquiv K K' K' (space D)).symm
          (RingPoints.changeRing (Algebra.ofId K K') x)) := by
  let X := space D
  let XK := baseChange (Spec.algebraMap K K') X
  let : TopologicalSpace (RingPoints K' XK K') := etaleChartTopology K' XK
  let U := ringTest K K'[X]
  have : LocallyOfFiniteType U.hom := locallyOfFiniteType_lineBase
  have : QuasiCompact U.hom := by
    change QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap K K'[X])))
    infer_instance
  let f : (schemeToSpace _).obj U ⟶ X := homMk (atlas D)
  have hf : IsEtale (hom f) := atlas_isEtale D
  let d := baseChangeChart K' U f hf
  let ι := fun x : RingPoints K X K =>
    (baseChangeRingPointsEquiv K K' K' X).symm (RingPoints.changeRing (Algebra.ofId K K') x)
  let Φ : K' → RingPoints K' XK K' := fun s =>
    d.pointMap (ringPointBaseChangeEquiv K K' K' U (linePoint K s))
  have hΦ : Continuous Φ := by
    have h₁ := d.continuous_pointMap
    have h₂ := @IsHomeomorph.continuous _ _ (schemePointTopology K U K')
      (schemePointTopology K' (ringBaseChange K K' U) K') _ (schemeBaseChangeTopology_proof K K' K' U)
    have h₃ := continuous_linePoint (K := K) (K' := K')
    exact @Continuous.comp _ _ _ _ (schemePointTopology K' d.scheme K') _ _ _ h₁
      (@Continuous.comp _ _ _ _ (schemePointTopology K U K') (schemePointTopology K' d.scheme K')
        _ _ h₂ h₃)
  have hΦeq : ∀ s : K', baseChangeRingPointsEquiv K K' K' X (Φ s) =
      (atlas D).app (op (ringTest K K')) ⟨linePt K s⟩ := by
    intro s
    rw [baseChangeRingPointsEquiv_baseChangeChart_pointMap, Equiv.symm_apply_apply]
    rfl
  have hnot : Φ 0 ∉ Set.range ι := by
    rintro ⟨x, hx⟩
    apply changeRing_ne_zero D x
    have := congrArg (baseChangeRingPointsEquiv K K' K' X) hx
    simp only [ι, Equiv.apply_symm_apply] at this
    rw [this, hΦeq]
  have hmem : ∀ c : K, c ≠ 0 → Φ (algebraMap K K' c) ∈ Set.range ι := by
    intro c hc
    obtain ⟨x, hx⟩ := exists_changeRing_eq D c hc
    refine ⟨x, (baseChangeRingPointsEquiv K K' K' X).injective ?_⟩
    simp only [ι, Equiv.apply_symm_apply]
    rw [hΦeq, hx]
  obtain ⟨p₀, hp₀, hp₁⟩ := NormedField.exists_norm_lt_one K
  have hp₀' : p₀ ≠ 0 := norm_pos_iff.mp hp₀
  have hs : Tendsto (fun n : ℕ => algebraMap K K' (p₀ ^ n)) atTop (𝓝 0) := by
    have h := ((continuous_algebraMap K K').tendsto 0).comp
      (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hp₁)
    rw [map_zero] at h
    exact h
  intro hclosed
  exact hnot (hclosed.mem_of_tendsto ((hΦ.tendsto 0).comp hs)
    (Eventually.of_forall fun n => hmem _ (pow_ne_zero n hp₀')))

end GaloisTwistedLine

end Langlands.AlgebraicGeometry.AlgebraicSpace
