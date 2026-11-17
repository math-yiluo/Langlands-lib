import Langlands.AlgebraicGeometry.Picard.AmpleIsoProof

/-! # Ampleness reflected by a positive actual tensor power -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard.LineBundle

open Langlands.Scheme.Modules Langlands.SchemeModule

variable {X : Scheme.{u}} {L M : LineBundle X}

/-- If an ample actual line is isomorphic to a positive tensor power of
another actual line, the latter line is ample. -/
theorem IsAmple.of_positive_tensorPower_iso (hM : M.IsAmple)
    {n : ℕ} (hn : 0 < n) (e : M.obj ≅ tensorPow L.obj n) : L.IsAmple := by
  refine ⟨hM.1, fun x => ?_⟩
  obtain ⟨k, hk, s, hx, ha⟩ := hM.2 x
  let E : tensorPow M.obj k ≅ tensorPow L.obj (n * k) :=
    tensorPowIso e k ≪≫ tensorPowMulIso L.obj n k
  let t : L.powSections (n * k) := E.hom.app ⊤ s
  have ht : L.sectionOpen t = M.sectionOpen s :=
    trivializationOpen_mapIso E s
  exact ⟨n * k, Nat.succ_le_iff.mpr (Nat.mul_pos hn (by omega)), t, ht ▸ hx, ht ▸ ha⟩

end Langlands.AlgebraicGeometry.Picard.LineBundle
