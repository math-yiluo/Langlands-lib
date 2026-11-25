import Langlands.Representation.Plancherel.RationalUnramifiedComplexTorusStatement
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-! # Basis independence of the complex chart on unramified characters

Both directions of a change of basis are Laurent monomials on the image of the chart.
-/

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry Topology
open Langlands.AlgebraicGeometry.PointTopology
open scoped BigOperators ContDiff Manifold CategoryTheory.MonObj

namespace Langlands.Plancherel

section BasisTransition

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
variable {κ : Type v} [Fintype κ]

private local instance : TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

/-- In the coordinates of `b`, evaluation at the basis `b'` is a Laurent monomial in each
coordinate and is analytic on the image of the chart. -/
private theorem contDiffOn_rationalUnramifiedBasisTransition
    (b b' : Module.Basis κ ℤ (Additive (rationalDiscreteValuationImage G))) :
    let e := (isOpenEmbedding_rationalUnramifiedBasisCoordinates G b).toOpenPartialHomeomorph
      (rationalUnramifiedBasisCoordinates G b)
    ContDiffOn ℂ ω (rationalUnramifiedBasisCoordinates G b' ∘ e.symm) e.target := by
  intro e
  have hcoords (z : κ → ℂ) (hz : z ∈ e.target) :
      rationalUnramifiedBasisCoordinates G b (e.symm z) = z :=
    e.right_inv hz
  refine ContDiffOn.congr (f := fun (z : κ → ℂ) i => ∏ j, z j ^ (b.repr (b' i) j)) ?_ ?_
  · intro z hz
    have hne (j : κ) : z j ≠ 0 := by
      rw [← hcoords z hz]
      exact Units.ne_zero _
    apply ContDiffAt.contDiffWithinAt
    apply contDiffAt_pi.mpr
    intro i
    apply contDiffAt_prod
    intro j _
    have hproj : ContDiffAt ℂ ω (fun w : κ → ℂ => w j) z := contDiffAt_apply ℂ (fun _ => ℂ) j z
    cases b.repr (b' i) j with
    | ofNat n => simpa only [Int.ofNat_eq_natCast, zpow_natCast] using hproj.pow n
    | negSucc n =>
      simpa only [zpow_negSucc] using (hproj.pow (n + 1)).fun_inv (pow_ne_zero _ (hne j))
  · intro z hz
    funext i
    let ξ := (rationalCanonicalImageUnramifiedContinuousEquiv G).symm (e.symm z)
    let c := rationalImageBasisUnitCoordinates G b ξ
    have hc (j : κ) : (↑(c j) : ℂ) = z j := congrFun (hcoords z hz) j
    have hξ : rationalImageBasisCharacter G b c = ξ :=
      (rationalImageBasisUnitCoordinates G b).symm_apply_apply ξ
    have hvalue := congrArg (fun ψ : rationalImageCharacters G => (↑(ψ (b' i).toMul) : ℂ))
      hξ.symm
    change (↑(ξ (b' i).toMul) : ℂ) = ∏ j, z j ^ (b.repr (b' i) j)
    simpa only [rationalImageBasisCharacter_apply, Units.coe_prod, Units.val_zpow_eq_zpow_val,
      ofMul_toMul, hc] using hvalue

end BasisTransition

/-- With the complex charted space given by `b`, the basis coordinates of any other integer
basis of the valuation image are a local biholomorphism. -/
theorem rationalUnramifiedBasisChartIndependence_of_basisTransition :
    RationalUnramifiedBasisChartIndependenceStatement.{u} := by
  intro F _ _ _ _ G hG
  let _ : IsAffineHom G.X.hom := hG.isAffineHom
  let _ : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let _ : Smooth G.X.hom := hG.smooth
  let _ : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
  intro b
  let _ := rationalUnramifiedBasisChartedSpace G b
  intro b' χ
  let E := Fin (rationalImageRank G) → ℂ
  let f := rationalUnramifiedBasisCoordinates G b
  let f' := rationalUnramifiedBasisCoordinates G b'
  let h := isOpenEmbedding_rationalUnramifiedBasisCoordinates G b
  let h' := isOpenEmbedding_rationalUnramifiedBasisCoordinates G b'
  let e := h.toOpenPartialHomeomorph f
  let e' := h'.toOpenPartialHomeomorph f'
  let _ : IsManifold 𝓘(ℂ, E) ω
      (unramifiedCharacters (fun psi => (rationalNormCharacters G psi).toMul)) :=
    h.isManifold_singleton
  have he : chartAt E χ = e := rfl
  have hsource : e.source = Set.univ := rfl
  have hsource' : e'.source = Set.univ := rfl
  have hfull (ψ : unramifiedCharacters (fun psi => (rationalNormCharacters G psi).toMul)) :
      ψ ∈ e.source := by
    rw [hsource]
    exact Set.mem_univ ψ
  have hchart : ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, E) ω e e.source := by
    rw [← he]
    exact contMDiffOn_chart
  have hchartInv : ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, E) ω e.symm e.target := by
    rw [← he]
    exact contMDiffOn_chart_symm
  have hforward : ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, E) ω (f' ∘ e.symm) e.target :=
    (contDiffOn_rationalUnramifiedBasisTransition G b b').contMDiffOn
  have hbackward : ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, E) ω (f ∘ e'.symm) e'.target :=
    (contDiffOn_rationalUnramifiedBasisTransition G b' b).contMDiffOn
  refine ⟨{
    toPartialEquiv := e'.toPartialEquiv
    open_source := e'.open_source
    open_target := e'.open_target
    contMDiffOn_toFun := ?_
    contMDiffOn_invFun := ?_ }, ?_, fun _ _ => rfl⟩
  · change ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, E) ω f' e'.source
    rw [hsource', ← hsource]
    refine (hforward.comp hchart (fun _ hψ => e.map_source hψ)).congr ?_
    intro ψ hψ
    change f' ψ = f' (e.symm (e ψ))
    rw [e.left_inv hψ]
  · change ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, E) ω e'.symm e'.target
    refine (hchartInv.comp hbackward (fun z _ => e.map_source (hfull (e'.symm z)))).congr ?_
    intro z _
    change e'.symm z = e.symm (e (e'.symm z))
    rw [e.left_inv (hfull (e'.symm z))]
  · change χ ∈ e'.source
    rw [hsource']
    exact Set.mem_univ χ

end Langlands.Plancherel
