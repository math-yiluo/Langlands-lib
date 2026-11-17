import Langlands.GroupScheme.IdentityJetSheaf
import Langlands.AlgebraicGeometry.Modules.CoherentClosure
import Langlands.AlgebraicGeometry.Modules.FiniteProjectiveAffineLocalBases

/-! # Actual finite local bases of smooth affine identity jets -/

noncomputable section
universe u

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.IdentityJet

variable {S : Scheme.{u}} (G : GroupScheme S)

instance inclusion_isClosedImmersion (n : ℕ) : IsClosedImmersion (inclusion G n) := by
  dsimp [inclusion]
  infer_instance

variable [IsAffineHom G.X.hom]

instance projection_isAffineHom (n : ℕ) : IsAffineHom (projection G n) := by
  dsimp [projection]
  infer_instance

/-- The actual pushed structure module of the identity jet is quasi-coherent. -/
instance isQuasicoherent_module (n : ℕ) : (module G n).IsQuasicoherent := by
  have : (Langlands.SchemeModule.structureModule (scheme G n)).IsQuasicoherent := by
    change (SheafOfModules.unit (scheme G n).ringCatSheaf).IsQuasicoherent
    infer_instance
  change ((Scheme.Modules.pushforward (projection G n)).obj
    (Langlands.SchemeModule.structureModule (scheme G n))).IsQuasicoherent
  exact Langlands.AlgebraicGeometry.Modules.QuasicoherentLocal.isQuasicoherent_pushforward _ _

variable [Smooth G.X.hom]

/-- Every actual identity jet has finite local bases over the arbitrary base. -/
theorem hasFiniteLocalBasis (n : ℕ) :
    Langlands.Scheme.Modules.HasFiniteLocalBasis (module G n) :=
  Langlands.AlgebraicGeometry.Modules.hasFiniteLocalBasis_of_finite_projective_affineSections
    (module G n) (fun U => finite_sections G n U) (fun U => projective_sections G n U)

/-- Actual finite frames, chosen only after proving finite local freeness. -/
def finiteLocalFrames (n : ℕ) :
    Langlands.AlgebraicGeometry.Picard.FiniteLocalFrames (module G n) :=
  Langlands.AlgebraicGeometry.Picard.FiniteLocalFrames.choose (hasFiniteLocalBasis G n)

/-- The actual determinant line of the smooth affine identity jet module. -/
def determinant (n : ℕ) : Langlands.AlgebraicGeometry.Picard.LineBundle S :=
  Langlands.AlgebraicGeometry.Picard.finiteLocallyFreeDeterminant (hasFiniteLocalBasis G n)

end Langlands.GroupScheme.IdentityJet
