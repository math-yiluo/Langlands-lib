import Langlands.Geometry.Analytic.QuasiEtaleLiftCompatibilityStatement
import Langlands.Geometry.Analytic.QuasiEtaleRigidity.QuasiEtaleRigid

/-! # Proof: lifts of a continuous action are compatible with morphisms over the base -/

universe u v z

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory Topology

/-- Lifts of a continuous action to compact quasi-étale spaces are compatible with morphisms
over the base, on an open subgroup. -/
theorem quasiEtaleLiftCompatibility (K : Type u) [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] : QuasiEtaleLiftCompatibilityStatement.{u, v, z} K := by
  intro G _ _ _ X U V ρ p q f hfpq _ _ hp _ hU hV a b
  refine exists_open_subgroup_intertwining hfpq (isRigid_of_quasiEtale p hp hU)
    (fun τ => ?_) a b
  have : CompactSpace (localizedSpaceFunctor.obj V) := hV.1
  have : T2Space (localizedSpaceFunctor.obj U) := hU.2
  have : T2Space (presentationOf U).presentation.space := hU.2
  have hK : IsCompact ((localizedSpaceFunctor.map f : localizedSpaceFunctor.obj V →
      localizedSpaceFunctor.obj U) ⁻¹' τ.locus) :=
    (τ.isCompact_locus.isClosed.preimage (localizedSpaceFunctor.map f).hom.continuous).isCompact
  obtain ⟨E, -, hE⟩ := exists_isNear_postcomp f τ hK
  refine ⟨E, fun φ hφ => ?_⟩
  have h := hE V φ (𝟙 V) hφ
  rwa [Category.id_comp] at h

end Langlands.Analytic.SaturatedAtlasPresentation
