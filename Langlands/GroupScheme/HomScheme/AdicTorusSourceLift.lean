import Langlands.GroupScheme.AffineLinearEmbeddingProof
import Langlands.GroupScheme.GeneralLinearSmoothProof
import Langlands.GroupScheme.Reductive.GeneralLinear
import Langlands.GroupScheme.Torus.HenselianSubgroupLifting
import Langlands.GroupScheme.Torus.RelativeReductive
import Langlands.AlgebraicGeometry.AdicAffinePoints
import Mathlib.RingTheory.Henselian

/-! # Lifting an abstract residue torus over a complete local ring -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing
open Langlands.AlgebraicGeometry.AdicAffinePoints

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.HomScheme.Adic

/-- Every relative torus on the first adic quotient of a complete local ring
has an actual relative torus lift, with a specified residue isomorphism. -/
def AdicTorusSourceLiftStatement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsAdicComplete (maximalIdeal A) A]
    (T₀ : GroupScheme (quotientSpec (maximalIdeal A) 0)), RelativeTorus.IsTorus T₀ →
    ∃ (T : GroupScheme (Spec (CommRingCat.of A))), RelativeTorus.IsTorus T ∧
      Nonempty ((baseChange (quotientMap (maximalIdeal A) 0)).obj T ≅ T₀)

set_option maxHeartbeats 1000000 in
/-- Embed the residue torus into a general linear group and lift it in the
smooth affine group over the complete ring. -/
theorem adicTorusSourceLift : AdicTorusSourceLiftStatement.{u} := by
  intro A _ _ _ T₀ hT₀
  let k := A ⧸ maximalIdeal A ^ (0 + 1)
  have : (maximalIdeal A ^ (0 + 1)).IsMaximal := by
    rw [show 0 + 1 = 1 from rfl, pow_one]
    infer_instance
  let : Field k := Ideal.Quotient.field _
  change GroupScheme (Spec (CommRingCat.of k)) at T₀
  let m := maximalIdeal A
  let b : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A) := quotientMap m 0
  have hk : Function.Surjective (algebraMap A k) := Ideal.Quotient.mk_surjective
  have : HenselianLocalRing A := ⟨fun p hp a ha hu =>
    HenselianRing.is_henselian p hp a ha (hu.map (IsLocalRing.residue A))⟩
  have : IsAffineHom T₀.X.hom := hT₀.isAffineHom
  have : Smooth T₀.X.hom := hT₀.smooth
  obtain ⟨N, i, hi⟩ := affineLinearEmbeddingStatement k T₀ inferInstance inferInstance
  let G := GeneralLinear.groupScheme (Fin N) (CommRingCat.of A)
  have : Smooth G.X.hom := GeneralLinear.smoothStatement _ _
  have : IsAffineHom G.X.hom := GeneralLinear.isAffineHom_groupScheme _ _
  let e := GeneralLinear.baseChangeIso (Fin N) b
  let j : T₀ ⟶ (baseChange b).obj G := i ≫ e.inv
  obtain ⟨d⟩ := HenselianTorusLifting.nonempty_liftData hk G j (hi.comp_iso e.symm) hT₀
  exact ⟨d.torus, d.relativeTorus, ⟨d.residueIso⟩⟩

end Langlands.GroupScheme.HomScheme.Adic
