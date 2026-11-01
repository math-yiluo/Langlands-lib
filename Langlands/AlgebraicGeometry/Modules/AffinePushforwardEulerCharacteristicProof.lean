import Langlands.AlgebraicGeometry.Modules.AffinePushforwardEulerCharacteristicStatement
import Langlands.AlgebraicGeometry.Modules.AffineQuasicoherentHigherDirectImageVanishingProof
import Langlands.AlgebraicGeometry.Modules.PushforwardVanishing
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! # Proof of Euler invariance under actual affine pushforward -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

variable {X Y : Scheme.{u}} (h : X ⟶ Y) [IsAffineHom h]
  {R : CommRingCat.{u}} (g : Y ⟶ Spec R)

/-- The actual affine pushforward comparison, using quasi-coherence to
deduce the higher-direct-image vanishing hypothesis. -/
def affinePushforwardCohomologyIso (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    (relativeCohomology (h ≫ g) n).obj M ≅
      (relativeCohomology g n).obj ((Scheme.Modules.pushforward h).obj M) :=
  pushforwardCohomologyIso h g M
    (affineQuasicoherentHigherDirectImageVanishing X Y h inferInstance M inferInstance) n

/-- Actual affine pushforward preserves the finite-cohomology predicate
and the integer Euler characteristic. -/
theorem affinePushforwardEulerCharacteristic :
    AffinePushforwardEulerCharacteristicStatement.{u} := by
  intro K _ X Y h ha g M hq
  let := ha
  let := hq
  let e := affinePushforwardCohomologyIso h g M
  constructor
  · constructor
    · intro hM
      constructor
      · intro n
        let : Module.Finite K ((relativeCohomology (h ≫ g) n).obj M) := hM.1 n
        exact Module.Finite.equiv (e n).toLinearEquiv
      · obtain ⟨b, hb⟩ := hM.2
        exact ⟨b, fun n hn => IsZero.of_iso (hb n hn) (e n).symm⟩
    · intro hP
      constructor
      · intro n
        let : Module.Finite K
            ((relativeCohomology g n).obj ((Scheme.Modules.pushforward h).obj M)) :=
          hP.1 n
        exact Module.Finite.equiv (e n).toLinearEquiv.symm
      · obtain ⟨b, hb⟩ := hP.2
        exact ⟨b, fun n hn => IsZero.of_iso (hb n hn) (e n)⟩
  · intro hM hP
    unfold eulerCharacteristic
    apply finsum_congr
    intro n
    rw [(e n).toLinearEquiv.finrank_eq]

end Langlands.AlgebraicGeometry.Modules.DerivedSections
