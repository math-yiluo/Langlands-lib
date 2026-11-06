import Langlands.Global.LocalModularCharacter.ChartLie
import Langlands.Global.LocalModularCharacter.RegularChart
import Langlands.GroupScheme.AffinePointFiniteCoordinates

/-! # An identity chart of a smooth affine group over a complete field

Let `G` be a smooth affine group scheme of finite type over a field `F`, and `K` a complete
nontrivially normed field that is an `F`-algebra. The group `G(K)`, with its regular-function
evaluation topology, has a chart at the identity in which the group law is strictly
differentiable at the origin with derivative the identity on the second factor, and in which
conjugation by any `g` is strictly differentiable at the origin with derivative a linear
automorphism of determinant `det Ad(g)`. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry Filter Topology
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.Global.LocalModularCharacter

variable {F : Type u} [Field F] (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom]

/-- The topology of a normed field, on its bundled algebra. -/
local instance identityChartTopology {K : Type u} [NontriviallyNormedField K] [Algebra F K] :
    TopologicalSpace (CommAlgCat.of F K) :=
  inferInstanceAs (TopologicalSpace K)

/-- A normed field is a topological ring, on its bundled algebra. -/
local instance identityChartTopologicalRing {K : Type u} [NontriviallyNormedField K]
    [Algebra F K] : IsTopologicalRing (CommAlgCat.of F K) :=
  inferInstanceAs (IsTopologicalRing K)

/-- The evaluation topology on the points of `G` with values in a normed field. -/
local instance identityChartPointsTopology {K : Type u} [NontriviallyNormedField K]
    [Algebra F K] : TopologicalSpace (G.affinePoints (CommAlgCat.of F K)) :=
  G.affinePointsTopologicalSpace (CommAlgCat.of F K)

/-- The points of `G` with values in a normed field form a topological group. -/
local instance identityChartPointsTopologicalGroup {K : Type u} [NontriviallyNormedField K]
    [Algebra F K] : IsTopologicalGroup (G.affinePoints (CommAlgCat.of F K)) :=
  G.affinePointsIsTopologicalGroup (CommAlgCat.of F K)

attribute [local instance] chartLieKernelCommGroup chartLieKernelModule

/-- **Identity chart of a smooth affine group.** -/
theorem exists_identityChart (hG : Smooth G.X.hom) {K : Type u} [NontriviallyNormedField K]
    [CompleteSpace K] [Algebra F K] :
    ∃ (d : ℕ) (φ : OpenPartialHomeomorph (G.affinePoints (CommAlgCat.of F K)) (Fin d → K)),
      (1 : G.affinePoints (CommAlgCat.of F K)) ∈ φ.source ∧ φ 1 = 0 ∧
      (∃ L : (Fin d → K) × (Fin d → K) →L[K] (Fin d → K),
        HasStrictFDerivAt (fun p : (Fin d → K) × (Fin d → K) => φ (φ.symm p.1 * φ.symm p.2))
          L 0 ∧ ∀ w, L (0, w) = w) ∧
      ∀ g : G.affinePoints (CommAlgCat.of F K), ∃ A : (Fin d → K) ≃L[K] (Fin d → K),
        HasStrictFDerivAt (fun z => φ (g * φ.symm z * g⁻¹))
          (A : (Fin d → K) →L[K] (Fin d → K)) 0 ∧
        LinearMap.det (A.toLinearEquiv : (Fin d → K) →ₗ[K] (Fin d → K)) =
          LinearMap.det (adjoint G K g) := by
  let e := G.affinePointsAlgebraHomeomorph (CommAlgCat.of F K)
  obtain ⟨d, φ₀, n, c, R, R', hp, hp0, hR, hφ, hreg, hinj⟩ := exists_regularChart G.X hG (e 1)
  let φ : OpenPartialHomeomorph (G.affinePoints (CommAlgCat.of F K)) (Fin d → K) :=
    e.transOpenPartialHomeomorph φ₀
  have hev (x : G.affinePoints (CommAlgCat.of F K)) (a : AffineCoordinateRing F G.X) :
      e x a = G.affinePointEvaluation (CommAlgCat.of F K) x a :=
    G.affinePointsAlgebraHomeomorph_apply _ x a
  have hsymm (s : Fin d → K) : e (φ.symm s) = φ₀.symm s := e.apply_symm_apply _
  refine ⟨d, φ, hp, hp0, chart_derivatives G φ c (R := R) (R' := R') hp hp0 ?_ ?_ ?_ ?_⟩
  · simpa only [hev] using hR
  · intro x hx
    have h := hφ (e x) hx
    simp only [hev] at h
    exact h
  · intro a
    obtain ⟨L, hL⟩ := hreg a
    refine ⟨L, ?_⟩
    have h : (fun s => G.affinePointEvaluation (CommAlgCat.of F K) (φ.symm s) a) =
        fun s => φ₀.symm s a := by
      funext s
      rw [← hev, hsymm]
    rw [h]
    exact hL
  · intro D hD hR0
    refine hinj D (fun a b => ?_) hR0
    simpa only [hev] using hD a b

end Langlands.Global.LocalModularCharacter
