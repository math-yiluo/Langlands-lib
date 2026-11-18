import Langlands.Representation.Plancherel.RationalUnramifiedBasisChartTransitionProof
import Langlands.Representation.Plancherel.RationalUnramifiedComplexTorusStatement
import Mathlib.Analysis.Analytic.Constructions

/-! # Independence of the complex chart on `X(G)` from the lattice basis

The transition between two lattice-basis charts is a Laurent monomial map in
each direction. Analyticity on the chart images gives a local biholomorphism.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Set Topology
open Langlands.AlgebraicGeometry.PointTopology
open scoped ContDiff Manifold CategoryTheory.MonObj

namespace Langlands.Plancherel

universe u

section CanonicalTopology

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance : TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

local notation "X" => unramifiedCharacters (fun psi => Additive.toMul (rationalNormCharacters G psi))
local notation "E" => Fin (rationalImageRank G) → ℂ
local notation "LatticeBasis" =>
  Module.Basis (Fin (rationalImageRank G)) ℤ (Additive (rationalDiscreteValuationImage G))

private def basisChart (b : LatticeBasis) : OpenPartialHomeomorph X E :=
  (isOpenEmbedding_rationalUnramifiedBasisCoordinates G b).toOpenPartialHomeomorph
    (rationalUnramifiedBasisCoordinates G b)

private theorem basisCoordinates_change (b b' : LatticeBasis) (χ : X) :
    rationalUnramifiedBasisCoordinates G b' χ =
      fun i => ∏ j, rationalUnramifiedBasisCoordinates G b χ j ^ (b.repr (b' i) j) := by
  let ξ := (rationalCanonicalImageUnramifiedContinuousEquiv G).symm χ
  let c := rationalImageBasisUnitCoordinates G b ξ
  have hξ : rationalImageBasisCharacter G b c = ξ :=
    (rationalImageBasisUnitCoordinates G b).symm_apply_apply ξ
  funext i
  change (ξ (b' i).toMul : ℂ) = ∏ j, (c j : ℂ) ^ (b.repr (b' i) j)
  calc
    (ξ (b' i).toMul : ℂ) = (rationalImageBasisCharacter G b c (b' i).toMul : ℂ) :=
      congrArg (fun (τ : rationalImageCharacters G) => (τ (b' i).toMul : ℂ)) hξ.symm
    _ = _ := by
      simp only [rationalImageBasisCharacter_apply, ofMul_toMul, Units.coe_prod,
        Units.val_zpow_eq_zpow_val]

private theorem contDiffOn_basisChart_transition (b b' : LatticeBasis) :
    ContDiffOn ℂ ω (basisChart G b' ∘ (basisChart G b).symm) (basisChart G b).target := by
  let monomial : E → E := fun z i => ∏ j, z j ^ (b.repr (b' i) j)
  have hmonomial : ContDiffOn ℂ ω monomial (basisChart G b).target := by
    intro z hz
    have hnonzero (j : Fin (rationalImageRank G)) : z j ≠ 0 := by
      rw [← (basisChart G b).right_inv hz]
      exact Units.ne_zero _
    have hanalytic : AnalyticAt ℂ monomial z := by
      refine AnalyticAt.pi fun i => Finset.univ.analyticAt_fun_prod fun j _ => ?_
      have hproj : AnalyticAt ℂ (fun w : E => w j) z :=
        (ContinuousLinearMap.proj (R := ℂ) j).analyticAt z
      exact hproj.fun_zpow (hnonzero j)
    exact hanalytic.contDiffAt.contDiffWithinAt
  refine hmonomial.congr fun z hz => ?_
  change rationalUnramifiedBasisCoordinates G b' ((basisChart G b).symm z) = monomial z
  rw [basisCoordinates_change G b b']
  exact congrArg monomial ((basisChart G b).right_inv hz)

private theorem basisCoordinates_isLocalDiffeomorph (b b' : LatticeBasis) :
    letI := rationalUnramifiedBasisChartedSpace G b
    IsLocalDiffeomorph 𝓘(ℂ, E) 𝓘(ℂ, E) ω (rationalUnramifiedBasisCoordinates G b') := by
  let _ := rationalUnramifiedBasisChartedSpace G b
  let e := basisChart G b
  let e' := basisChart G b'
  have hchart (χ : X) : chartAt E χ = e := rfl
  have hsource (c : LatticeBasis) : (basisChart G c).source = Set.univ :=
    (isOpenEmbedding_rationalUnramifiedBasisCoordinates G c).toOpenPartialHomeomorph_source _
  let diffeo : PartialDiffeomorph 𝓘(ℂ, E) 𝓘(ℂ, E) X E ω := {
    toPartialEquiv := e'.toPartialEquiv
    open_source := e'.open_source
    open_target := e'.open_target
    contMDiffOn_toFun := by
      intro χ hχ
      rw [contMDiffWithinAt_iff']
      refine ⟨e'.continuousOn_toFun χ hχ, ?_⟩
      have htarget : (extChartAt 𝓘(ℂ, E) χ).target = e.target := by
        rw [extChartAt_target, hchart]
        simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
          Set.preimage_id_eq, Set.range_id, Set.inter_univ, id_eq]
      exact (contDiffOn_basisChart_transition G b b' (e χ)
        (e.map_source ((hsource b).symm ▸ Set.mem_univ χ))).mono
          (by rw [htarget]; exact inter_subset_left)
    contMDiffOn_invFun := by
      intro z hz
      rw [contMDiffWithinAt_iff]
      refine ⟨e'.continuousOn_invFun z hz, ?_⟩
      change ContDiffWithinAt ℂ ω (e ∘ e'.symm)
        ((id : E → E) ⁻¹' e'.target ∩ Set.range (id : E → E)) z
      simpa only [Set.preimage_id_eq, Set.range_id, Set.inter_univ, id_eq] using
        contDiffOn_basisChart_transition G b' b z hz
  }
  intro χ
  exact ⟨diffeo, (hsource b').symm ▸ Set.mem_univ χ, fun _ _ => rfl⟩

end CanonicalTopology

/-- For the complex chart given by any lattice basis, the coordinates of every
other lattice basis are a local biholomorphism (Renard V.3.20). -/
theorem rationalUnramifiedBasisChartIndependence :
    RationalUnramifiedBasisChartIndependenceStatement.{u} := by
  intro F _ _ _ _ G hG
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : Smooth G.X.hom := hG.smooth
  let _ : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
  intro b b'
  exact basisCoordinates_isLocalDiffeomorph G b b'

end Langlands.Plancherel
