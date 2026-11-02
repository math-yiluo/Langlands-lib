import Langlands.AlgebraicGeometry.Picard.LineBundleAutomorphismScalarStatement
import Langlands.AlgebraicGeometry.Picard.RigidifiedIsoUniquenessProof

/-! # Automorphisms of locally free rank-one sheaves are unique global units -/

open CategoryTheory AlgebraicGeometry Opposite
open Langlands.AlgebraicGeometry.Picard (IsLocallyFreeRankOne)

set_option backward.isDefEq.respectTransparency false

universe u

noncomputable section

namespace Langlands.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- On a locally free module sheaf of rank one, a global function is determined by the
endomorphism it induces: if `a • 𝟙 M = b • 𝟙 M` then `a = b`. -/
theorem smul_id_injective_of_isLocallyFreeRankOne {M : X.Modules}
    (hM : IsLocallyFreeRankOne M) {a b : Γ(X, ⊤)} (h : a • 𝟙 M = b • 𝟙 M) : a = b := by
  choose W hxW t using hM
  refine TopCat.Sheaf.eq_of_locally_eq' X.sheaf W ⊤ (fun _ ↦ homOfLE le_top)
    (fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxW x⟩) a b fun x ↦ ?_
  apply smul_trivGen_injective (t x).some (𝟙 (W x))
  exact congrArg (fun g ↦ g.app (W x) (trivGen (t x).some (𝟙 (W x)))) h

end Langlands.Scheme.Modules

namespace Langlands.AlgebraicGeometry.Picard

/-- Every automorphism of a locally free module sheaf of rank one is multiplication by
exactly one global unit. -/
theorem lineBundleAutomorphismScalar : LineBundleAutomorphismScalarStatement.{u} := by
  intro X M hM e
  obtain ⟨c, hc⟩ := Langlands.Scheme.Modules.exists_eq_smul_id_of_isLocallyFreeRankOne hM e.hom
  obtain ⟨d, hd⟩ := Langlands.Scheme.Modules.exists_eq_smul_id_of_isLocallyFreeRankOne hM e.inv
  have hcd : c * d = 1 := by
    apply Langlands.Scheme.Modules.smul_id_injective_of_isLocallyFreeRankOne hM
    calc (c * d) • 𝟙 M = c • (𝟙 M ≫ (d • 𝟙 M)) := by rw [mul_smul, Category.id_comp]
      _ = e.hom ≫ e.inv := by rw [hc, hd, Linear.smul_comp]
      _ = (1 : Γ(X, ⊤)) • 𝟙 M := by rw [e.hom_inv_id, one_smul]
  let r : Γ(X, ⊤)ˣ := ⟨c, d, hcd, by rw [mul_comm]; exact hcd⟩
  refine ⟨r, hc, fun r' hr' ↦ Units.ext ?_⟩
  exact Langlands.Scheme.Modules.smul_id_injective_of_isLocallyFreeRankOne hM (hr'.symm.trans hc)

end Langlands.AlgebraicGeometry.Picard
