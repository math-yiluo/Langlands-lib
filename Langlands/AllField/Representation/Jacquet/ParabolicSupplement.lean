import Langlands.Representation.Jacquet.Parabolic
import Langlands.AllField.Group.GL.BlockModulusSupplement
import Langlands.AllField.Representation.Jacquet.Parabolic
/-!
# Normalized Jacquet modules for standard block parabolics

The Jacquet module of a representation of `GL_n` along a standard block parabolic
is the actual coinvariant quotient of its restriction to the parabolic by the
unipotent radical. The Levi acts through its section into the parabolic,
normalized by the inverse square root of a supplied full positive modulus. For
p-adic fields that modulus is the explicit block modulus.
-/

noncomputable section

open CategoryTheory
open scoped NNReal

namespace Langlands.AllField.GeneralLinear.BlockShape
open Langlands.GeneralLinear.BlockShape
open Langlands.AllField.GeneralLinear.BlockShape
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear

universe uF uV uW uX

variable {F : Type uF} [CommRing F] {n : ℕ} (B : BlockShape n)
variable {V : Type uV} {W : Type uW} {X : Type uX}
variable [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
variable [AddCommGroup X] [Module ℂ X]

section Topology


end Topology

end Langlands.AllField.GeneralLinear.BlockShape

namespace Langlands.LocalFieldData
open Langlands.LocalFieldData

universe uF uV uW

variable {F : Type uF} [Field F]
variable (T : LocalFieldData F) {n : ℕ} (B : GeneralLinear.BlockShape n)
variable {V : Type uV} {W : Type uW}
variable [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- The Jacquet map of an actual intertwiner. -/
def normalizedJacquetMap {ρ : Representation ℂ (GeneralLinear n F) V}
    {τ : Representation ℂ (GeneralLinear n F) W} (f : ρ.IntertwiningMap τ) :
    (T.normalizedJacquet B ρ).IntertwiningMap (T.normalizedJacquet B τ) :=
  B.normalizedJacquetOfMap (T.leviModulus B) f

end Langlands.LocalFieldData

namespace Langlands

universe uF uV


end Langlands
