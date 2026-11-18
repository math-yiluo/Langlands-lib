import Mathlib.FieldTheory.SeparableClosure
import Langlands.AlgebraicGeometry.PointedAffineEtale
import Langlands.AlgebraicGeometry.StrictLocalEtaleLimitStatement
import Langlands.CommutativeAlgebra.PointedEtaleColimit

/-! # Existence of strictly local affine limits of étale neighbourhoods -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

open PointedAffineEtale Langlands.CommutativeAlgebra.PointedEtaleColimit

set_option backward.isDefEq.respectTransparency false in
private def strictLocalLimitOfColimit {S : Scheme.{u}} {s : S} {Ω : Type u} [Field Ω]
    [IsSepClosed Ω] (g : Spec (CommRingCat.of Ω) ⟶ S)
    (hg : g (IsLocalRing.closedPoint Ω) = s) (c : Cocone (rings g)) (hc : IsColimit c)
    [HenselianLocalRing c.pt] [IsSepClosed (IsLocalRing.ResidueField c.pt)]
    (p : c.pt ⟶ CommRingCat.of Ω) (hp : ∀ i, c.ι.app i ≫ p = (point g).app i)
    (hker : RingHom.ker p.hom = IsLocalRing.maximalIdeal c.pt) : StrictLocalEtaleLimit S s where
  ring := c.pt
  index := Index g
  diagram := diagram g
  structural := structural g
  projection := (spectrumCone g c).π
  baseMap := baseMap g c
  compatible := spectrumCone_compatible g c
  isLimit := spectrumConeIsLimit g hc
  closedPoint_image := by
    have hclosed : Spec.map p (IsLocalRing.closedPoint Ω) = IsLocalRing.closedPoint c.pt := by
      apply PrimeSpectrum.ext
      change Ideal.comap p.hom (IsLocalRing.maximalIdeal Ω) = IsLocalRing.maximalIdeal c.pt
      rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot, hker]
    rw [← hclosed]
    exact (congrArg (fun f : Spec (CommRingCat.of Ω) ⟶ S => f (IsLocalRing.closedPoint Ω))
      (baseMap_point g c p hp)).trans hg

/-- Every point of an affine scheme has a strictly local affine limit of affine étale
neighbourhoods. -/
theorem strictLocalEtaleLimitExistence : StrictLocalEtaleLimitExistenceStatement.{u} := by
  intro S _ s
  let Ω := SeparableClosure (S.residueField s)
  let g : Spec (CommRingCat.of Ω) ⟶ S :=
    Spec.algebraMap (S.residueField s) Ω ≫ S.fromSpecResidueField s
  have hg : g (IsLocalRing.closedPoint Ω) = s := S.fromSpecResidueField_apply s _
  let c := colimit.cocone (rings g)
  let hc := colimit.isColimit (rings g)
  have hr : Refines (point g) := refinement g
  have : HenselianLocalRing c.pt := henselianLocalRing hc (point g) hr
  have : IsSepClosed (IsLocalRing.ResidueField c.pt) := isSepClosed_residueField hc (point g) hr
  exact ⟨strictLocalLimitOfColimit g hg c hc (fieldMap hc (point g)) (ι_fieldMap hc (point g))
    (ker_fieldMap hc (point g) hr)⟩

end Langlands.AlgebraicGeometry
