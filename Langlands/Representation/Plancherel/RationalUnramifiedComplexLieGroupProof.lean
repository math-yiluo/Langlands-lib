import Langlands.Representation.Plancherel.RationalUnramifiedComplexTorusStatement

/-! # The complex Lie group of unramified characters

In the chart given by a valuation-image basis, multiplication is coordinatewise
multiplication and inversion is analytic because every coordinate is a complex unit.
-/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open Langlands.AlgebraicGeometry.PointTopology
open scoped Manifold ContDiff CategoryTheory.MonObj

namespace Langlands.Plancherel

/-- The basis chart makes the group of unramified characters a complex Lie group
(Renard V.3.20). -/
theorem rationalUnramifiedComplexLieGroup :
    RationalUnramifiedComplexLieGroupStatement.{u} := by
  intro F _ _ _ _ G hG
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : Smooth G.X.hom := hG.smooth
  let : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
  intro b
  let := rationalUnramifiedBasisChartedSpace G b
  let X := ↥(unramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul))
  let E := Fin (rationalImageRank G) → ℂ
  let coordinates : X → E := rationalUnramifiedBasisCoordinates G b
  let units := (rationalCanonicalImageUnramifiedContinuousEquiv G).symm.trans
    (rationalImageBasisUnitCoordinates G b)
  have coe_coordinates (χ : X) (i : Fin (rationalImageRank G)) :
      coordinates χ i = ((units χ i : ℂˣ) : ℂ) := rfl
  have hEmbedding : IsOpenEmbedding coordinates :=
    isOpenEmbedding_rationalUnramifiedBasisCoordinates G b
  have hCoordinates : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω coordinates :=
    contMDiff_isOpenEmbedding hEmbedding
  change LieGroup 𝓘(ℂ, E) ω X
  refine
    { toIsManifold := hEmbedding.isManifold_singleton
      contMDiff_mul := ?_
      contMDiff_inv := ?_ }
  · apply ContMDiff.of_comp_isOpenEmbedding hEmbedding
    have hmul : coordinates ∘ (fun p : X × X => p.1 * p.2) =
        (fun p : E × E => p.1 * p.2) ∘
          (fun p : X × X => (coordinates p.1, coordinates p.2)) := by
      funext p i
      change coordinates (p.1 * p.2) i = coordinates p.1 i * coordinates p.2 i
      simp only [coe_coordinates, map_mul, Pi.mul_apply, Units.val_mul]
    rw [hmul]
    exact (contDiff_mul (𝕜 := ℂ) (n := ω) (𝔸 := E)).contMDiff.comp
      ((hCoordinates.comp contMDiff_fst).prodMk_space (hCoordinates.comp contMDiff_snd))
  · apply ContMDiff.of_comp_isOpenEmbedding hEmbedding
    have hinv : coordinates ∘ (fun χ : X => χ⁻¹) =
        (fun z : E => fun i => (z i)⁻¹) ∘ coordinates := by
      funext χ i
      simp only [Function.comp_apply, coe_coordinates, map_inv, Pi.inv_apply,
        Units.val_inv_eq_inv_val]
    rw [hinv]
    intro χ
    refine ContMDiffAt.comp χ ?_ (hCoordinates χ)
    apply ContDiffAt.contMDiffAt
    refine contDiffAt_pi.mpr fun i => (contDiffAt_apply ℂ (fun _ ↦ ℂ) i (coordinates χ)).inv ?_
    rw [coe_coordinates]
    exact Units.ne_zero _

end Langlands.Plancherel
