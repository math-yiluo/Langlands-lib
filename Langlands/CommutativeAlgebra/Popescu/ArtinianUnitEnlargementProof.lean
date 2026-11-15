import Langlands.CommutativeAlgebra.Popescu.ArtinianUnitEnlargementStatement
import Langlands.CommutativeAlgebra.Popescu.EnlargementTranscendental

/-! # Proof of the unit enlargement of flat Artinian approximations -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

namespace Enlargement

/-- The refined form of Stacks 07FI for units: split according to whether the residue of `ℓ` is
algebraic (`caseA`) or transcendental (`caseB`) over the residue field of `D`. -/
theorem artinianUnitEnlargement : ArtinianUnitEnlargementStatement.{u} := by
  intro k D L _ _ _ _ _ p _ _ _ _ _ _ _ ψ hψloc hψflat ℓ hℓ t b hli hsp
  let _ : Algebra D L := (ψ : D →+* L).toAlgebra
  have : IsScalarTower k D L := .of_algebraMap_eq fun c => (ψ.commutes c).symm
  have : IsLocalHom (algebraMap D L) := ⟨hψloc.map_nonunit⟩
  have : Module.Flat D L := hψflat
  have hψeq : IsScalarTower.toAlgHom k D L = ψ := by
    ext d
    rfl
  by_cases halg : IsAlgebraic (IsLocalRing.ResidueField D) (IsLocalRing.residue L ℓ)
  · obtain ⟨D', i1, i2, i3, i4, i5, ι, ψ', h1, h2, h3, h4, h5⟩ := caseA p ℓ hℓ halg t b hli hsp
    exact ⟨D', i1, i2, i3, i4, i5, ι, ψ', h1, h2, h3.trans hψeq, h4, h5⟩
  · obtain ⟨D', i1, i2, i3, i4, i5, ι, ψ', h1, h2, h3, h4, h5⟩ := caseB p ℓ hℓ halg t b hli hsp
    exact ⟨D', i1, i2, i3, i4, i5, ι, ψ', h1, h2, h3.trans hψeq, h4, h5⟩

end Enlargement

end Langlands.CommutativeAlgebra.Popescu
