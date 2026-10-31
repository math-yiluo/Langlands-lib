import Langlands.AlgebraicGeometry.Modules.NoetherianUniversalPerfectSectionsStatement
import Langlands.AlgebraicGeometry.Modules.NoetherianCechPerfectRepresentativeProof
import Langlands.AlgebraicGeometry.Modules.CechResolution.Comparison
import Langlands.AlgebraicGeometry.OrderedAffineCoverCompact
import Langlands.AlgebraicGeometry.Picard.LineBundleQuasicoherent

/-! # Universal perfect sections over a noetherian base: proof -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules

attribute [local instance] HasDerivedCategory.standard

/-- The noetherian Čech representative computes actual derived sections over
the original base and every scalar extension. -/
theorem noetherianUniversalPerfectSections :
    NoetherianUniversalPerfectSectionsStatement.{u} := by
  intro R _ X f hf hp L
  let := hf
  let := hp
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let 𝒰 := Scheme.OrderedAffineCover.ofCompactSpace X
  have htriv : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj L.obj ≅
        SheafOfModules.unit U.toScheme.ringCatSheaf) := by
    intro x
    obtain ⟨U, hx, ⟨e⟩⟩ := L.property x
    exact ⟨U, hx, ⟨((Scheme.Modules.restrictFunctorIsoPullback U.ι).app L.obj).symm ≪≫ e⟩⟩
  obtain ⟨K, hK, ⟨α⟩, hScalar⟩ :=
    noetherianCechPerfectRepresentative R X f L.obj htriv 𝒰
  refine ⟨K, hK, ?_, ?_⟩
  · obtain ⟨β⟩ := CechResolution.nonempty_cechCochainComplex_iso R X f 𝒰 L.obj
    exact ⟨α ≪≫ β⟩
  · intro T φ
    let := φ.hom.toAlgebra
    obtain ⟨αT⟩ := hScalar T φ.hom
    let a := pullback.fst f (Spec.map φ)
    let g := pullback.snd f (Spec.map φ)
    let : ((Scheme.Modules.pullback a).obj L.obj).IsQuasicoherent :=
      L.property.isQuasicoherent_pullback a
    obtain ⟨βT⟩ := CechResolution.nonempty_cechCochainComplex_iso T _ g
      (𝒰.baseChange f T) ((Scheme.Modules.pullback a).obj L.obj)
    exact ⟨αT ≪≫ βT⟩

end Langlands.AlgebraicGeometry.Modules
