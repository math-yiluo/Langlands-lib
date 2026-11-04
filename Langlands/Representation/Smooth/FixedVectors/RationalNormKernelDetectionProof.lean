import Langlands.Representation.Smooth.FixedVectors.RationalNormKernelDetectionStatement
import Langlands.Representation.Smooth.FixedVectors.CompactRestrictionDetectionProof
import Langlands.Representation.CompactCoefficient.TotalCompactness
import Langlands.Representation.Plancherel.RationalCharacterTopology
import Langlands.Topology.Nonarchimedean.Subgroup
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected

/-! # Detection from finite restriction to the actual rational norm kernel -/

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands

universe u uV

/-- The actual finite-restriction and compact-coefficient inputs imply fixed-vector
detection for irreducible smooth subquotients. -/
theorem rationalNormKernelFixedVectorDetection :
    RationalNormKernelFixedVectorDetectionStatement.{u, uV} := by
  intro hfinite F _ _ _ _ G hG
  let := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
  intro _ _ _ A D K hK hD hgen hcompact hDA
  classical
  let H := Plancherel.rationalCommonNormKernel G
  have hH : IsClosed (H : Set (GroupScheme.rationalPoints G)) :=
    Plancherel.isClosed_rationalCommonNormKernel G
  let : LocallyCompactSpace H := hH.locallyCompactSpace
  let : MeasurableSpace H := borel H
  let : BorelSpace H := ⟨rfl⟩
  have hKH : K ≤ H := Plancherel.compactSubgroup_le_rationalCommonNormKernel G K hK
  obtain ⟨_, _, m, W, hW, hspan⟩ := hfinite F G hG D hD
  let : Representation.IsIrreducible D.representation := hD
  let : Nontrivial D :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GroupScheme.rationalPoints G))
      D.representation.asModule
  have hnonempty : Nonempty (Fin m) := by
    by_contra hn
    let : IsEmpty (Fin m) := not_nonempty_iff.mp hn
    have hb : (⊥ : Submodule ℂ D) = ⊤ := by
      simpa only [iSup_of_empty] using hspan
    obtain ⟨v, hv⟩ := exists_ne (0 : D)
    apply hv
    have hvbot : v ∈ (⊥ : Submodule ℂ D) := by
      rw [hb]
      trivial
    exact hvbot
  let : Nonempty (Fin m) := hnonempty
  have hcof : ∀ L : OpenSubgroup H, ∃ J : OpenSubgroup H,
      IsCompact (J : Set H) ∧ J ≤ L := by
    intro L
    obtain ⟨J, hJL, hJ, _⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance H ∅ L
    exact ⟨J, hJ, hJL⟩
  exact compactRestrictionFixedVectorDetection
    (GroupScheme.rationalPoints G) H MeasureTheory.Measure.haar A D K hKH hgen
    (Fin m) W hW
    (fun j => hasCompactSmoothDualCoefficients_subrepresentation
      hcof (SmoothRep.restrictSubgroup H D) hcompact (W j))
    hspan hDA

end Langlands
