import Langlands.GroupScheme.Dynamic.ActionConjugation
import Langlands.GroupScheme.Dynamic.Conjugation

/-! # The conjugation action of a represented dynamic centralizer on the unipotent subgroup -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

variable {S : Scheme.{u}} {G Z U : GroupScheme S} {χ : (Gm S).toGrp ⟶ G}
  {iZ : Z ⟶ G} {iU : U ⟶ G}
  (hZ : (centralizer χ).IsRepresentedBy iZ) (hU : (unipotent χ).IsRepresentedBy iU)

include hZ hU

/-- The representing inclusion of `U(χ)` is normalized by that of `Z(χ)`. -/
theorem range_unipotent_isNormalizedBy_range_centralizer :
    (SubgroupFunctor.range iU).IsNormalizedBy (SubgroupFunctor.range iZ) := by
  rw [hU.2, hZ.2]
  intro T g x hg hx
  exact unipotent_isNormalizedBy_parabolic χ T g x (centralizer_le_parabolic χ T hg) hx

/-- The actual action of the represented centralizer `Z(χ)` (the Levi factor `M`) on the
represented unipotent subgroup `U(χ)` by normalized conjugation `(m, u) ↦ m u m⁻¹`. -/
def centralizerAdjointAction : AutomorphicAction Z U :=
  have : Mono iU.hom.hom := hU.1
  AutomorphicAction.ofNormalizedConjugation iU iZ
    (range_unipotent_isNormalizedBy_range_centralizer hZ hU)

/-- Orientation: `m` acts by `u ↦ m u m⁻¹`, computed after the inclusions into `G`. -/
theorem centralizerAdjointAction_act_comp {T : Over S} (m : T ⟶ Z.X) (u : T ⟶ U.X) :
    (centralizerAdjointAction hZ hU).act m u ≫ iU.hom.hom =
      (m ≫ iZ.hom.hom) * (u ≫ iU.hom.hom) * (m ≫ iZ.hom.hom)⁻¹ :=
  SubgroupFunctor.lift_comp_normalizedConjugation_comp iU iZ
    (range_unipotent_isNormalizedBy_range_centralizer hZ hU) m u

/-- Uniqueness: an action of `Z` on `U` given after the inclusions by `(m, u) ↦ m u m⁻¹` on
every test scheme is `centralizerAdjointAction`. -/
theorem eq_centralizerAdjointAction (b : AutomorphicAction Z U)
    (hb : ∀ {T : Over S} (m : T ⟶ Z.X) (u : T ⟶ U.X),
      b.act m u ≫ iU.hom.hom = (m ≫ iZ.hom.hom) * (u ≫ iU.hom.hom) * (m ≫ iZ.hom.hom)⁻¹) :
    b = centralizerAdjointAction hZ hU := by
  have : Mono iU.hom.hom := hU.1
  apply AutomorphicAction.ext_act
  intro T m u
  apply (cancel_mono iU.hom.hom).1
  rw [hb, centralizerAdjointAction_act_comp]

end Langlands.GroupScheme.Dynamic
