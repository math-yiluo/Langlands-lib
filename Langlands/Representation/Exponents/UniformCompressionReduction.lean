import Langlands.Representation.Exponents.UniformCompressionStabilizationStatement
import Langlands.Representation.Jacquet.CompressionUniformity

/-! # Exact qualitative reduction for dynamic-parabolic compression

The qualitative hypothesis retains every geometric premise of the existing
uniform target. The countable-sum diagonal argument proves their equivalence.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme

/-- Pointwise eventual compression stability with exactly the geometric inputs
of the existing uniform target, at independent field and carrier universes. -/
def PointwiseCompressionStabilizationStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
      (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
      (g : rationalPoints G),
      (∀ m ∈ (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)), m * g = g * m) →
      Jacquet.IsIwahoriContraction K
        ((Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)))
        ((Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)))
        ((Dynamic.unipotent (Dynamic.inverseCocharacter χ)).carrier (Over.mk (𝟙 _))) g →
      Jacquet.PointwiseCompressionEventuallyStable.{u, v} K hK g

/-- The exact uniform Library target is equivalent to qualitative stability on
all smooth objects. This is a reduction, not a proof of either proposition. -/
theorem uniformCompressionStabilizationStatement_iff_pointwise :
    UniformCompressionStabilizationStatement.{u, v} ↔
      PointwiseCompressionStabilizationStatement.{u, v} := by
  constructor
  · intro h k _ _ _ _ _ G hG
    letI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := pointTopology
    intro _ _ χ K hK g hcentral hcontract A
    obtain ⟨b, hb⟩ := h k G hG χ K hK g hcentral hcontract
    apply (Jacquet.compactCompression_eventuallyStable_iff_exists_stationaryFrom
      A.representation A.isSmooth K hK g).mpr
    exact ⟨b, hb A A.representation A.isSmooth⟩
  · intro h k _ _ _ _ _ G hG
    letI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := pointTopology
    intro _ _ χ K hK g hcentral hcontract
    obtain ⟨b, hb⟩ := Jacquet.uniformCompressionStationary_of_pointwise K hK g
      (h k G hG χ K hK g hcentral hcontract)
    refine ⟨b, ?_⟩
    intro V _ _ ρ hρ
    exact hb (SmoothRep.of ρ hρ)

end Langlands.Aubert.General.RationalPointFamily
