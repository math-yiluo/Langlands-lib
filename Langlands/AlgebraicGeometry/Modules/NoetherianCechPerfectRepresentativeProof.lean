import Langlands.AlgebraicGeometry.Modules.NoetherianCechPerfectRepresentativeStatement
import Langlands.AlgebraicGeometry.Modules.NoetherianCechProjectiveRepresentativeProof
import Langlands.Cohomology.ModuleComplex.BoundedProjectiveFamilyDerivedComparisonProof

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules

attribute [local instance] HasDerivedCategory.standard

theorem noetherianCechPerfectRepresentative :
    NoetherianCechPerfectRepresentativeStatement.{u} := by
  intro R _ _ X π _ _ M htriv 𝒰
  classical
  let n := Fintype.card 𝒰.ι
  obtain ⟨K, instACG, instMod, hKfin, hKproj, δ, hδδ, hKbdd,
      φ, hφ, Θ, h0inj, h0surj, hinj, hsurj, hΘ⟩ :=
    noetherianCechProjectiveRepresentative π M htriv 𝒰 n (by dsimp [n]; omega)
  obtain ⟨P, hP, hOriginal, hScalar⟩ :=
    Langlands.Cohomology.ModuleComplex.boundedProjectiveFamilyDerivedComparison
      R K δ hδδ n hKbdd
  refine ⟨P, hP, ?_, ?_⟩
  · exact hOriginal
      (fun i => (OModulePresheaf.ofModules π M).cochain 𝒰 i)
      (fun i => (OModulePresheaf.ofModules π M).d 𝒰 i)
      (fun i => (OModulePresheaf.ofModules π M).d_comp_d 𝒰 i)
      φ hφ h0inj h0surj hinj hsurj
  · intro A _ f
    let := f.toAlgebra
    let CA := OModulePresheaf.ofModules
      (pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
      ((Scheme.Modules.pullback
        (pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)
    obtain ⟨hd, _hPureTensor, hA0inj, hA0surj, hAinj, hAsurj⟩ := hΘ A
    exact hScalar A f
      (fun i => CA.cochain (𝒰.baseChange π A) i)
      (fun i => CA.d (𝒰.baseChange π A) i)
      (fun i => CA.d_comp_d (𝒰.baseChange π A) i)
      (Θ A) hd hA0inj hA0surj hAinj hAsurj

end Langlands.AlgebraicGeometry.Modules
