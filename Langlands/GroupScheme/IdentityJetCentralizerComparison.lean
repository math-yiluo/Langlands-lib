import Langlands.GroupScheme.ConnectedResidueFibres
import Langlands.GroupScheme.IdentityJetCenterDetection
import Langlands.GroupScheme.IdentityJetCentralizerStabilizationStatement

/-! # Comparison of the conjugation kernel with jet centralizers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.IdentityJet

/-- Fixing every point of the jet is equivalent to commuting with every point
of the group which factors through its jet. Both conditions use all refinements. -/
theorem mem_conjugationKernel_iff_centralizesJet {S : Scheme.{u}} (G : GroupScheme S)
    [IsSeparated G.X.hom] (n : ℕ) {U : Over S} (g : U ⟶ G.X) :
    g ∈ (conjugationAction G n).kernel.carrier U ↔ CentralizesJet G n g := by
  constructor
  · intro hg V a x hx
    obtain ⟨y, hy⟩ := hx
    let z : V ⟶ (schemeFunctor S n).obj G := Over.homMk y (by
      change y ≫ projection G n = V.hom
      rw [projection, ← Category.assoc, hy, x.w])
    have hz : z ≫ overInclusion G n = x := Over.OverMorphism.ext hy
    have h := conjugatePoint_inclusion G n (a ≫ g) z
    have hfix : (conjugationAction G n).act (a ≫ g) z = z := hg V a z
    rw [← conjugationAction_act, hfix, hz] at h
    exact mul_inv_eq_iff_eq_mul.mp h.symm
  · intro hg V a z
    rw [conjugationAction_act, ← cancel_mono (overInclusion G n), conjugatePoint_inclusion]
    have h := hg V a (z ≫ overInclusion G n) ⟨z.left, rfl⟩
    rw [h, mul_assoc, mul_inv_cancel, mul_one]

end Langlands.GroupScheme.IdentityJet

namespace Langlands.GroupScheme

/-- Uniform centre detection supplies the affine-base jet centralizer statement. -/
theorem jetCentralizerStabilization_of_centerDetection :
    JetCentralizerStabilizationStatement.{u} := by
  intro R G hsm hsep hqc hconn
  have : GeometricallyConnected G.X.hom :=
    geometricallyConnected_of_connectedResidueFibres G hconn
  obtain ⟨n, hn⟩ := IdentityJet.exists_order_detects_center G
  refine ⟨n, fun U g hg h => ?_⟩
  have hc := (IdentityJet.mem_conjugationKernel_iff_centralizesJet G n g).mpr hg
  change (IdentityJet.conjugationAction G n).kernel = center G at hn
  rw [hn] at hc
  exact (commute_of_mem_center hc h).eq

end Langlands.GroupScheme
