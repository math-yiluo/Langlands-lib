import Langlands.GroupScheme.Torus.RelativeCocharacterCentralizers
import Langlands.GroupScheme.Torus.ExponentHomomorphisms
import Langlands.GroupScheme.Torus.TransporterFunctoriality

/-! # Actual transporter points in relative cocharacter centralizers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace PointwiseSchemeAction

variable {S : Scheme.{u}} {H G : GroupScheme S}

/-- A transporter for a homomorphism fixing a cocharacter centralizes that
actual cocharacter, on every test scheme. -/
theorem IsTransporter.mem_centralizer_of_fixed_cocharacter
    {i : H ⟶ G} {c : H ⟶ H} (χ : (Gm S).toGrp ⟶ H)
    (hχ : χ ≫ c = χ) {T : Over S} {g : T ⟶ G.X}
    (hg : IsTransporter (c ≫ i) i g) :
    g ∈ (Dynamic.centralizer (χ ≫ i)).carrier T := by
  have hc : IsTransporter (χ ≫ i) (χ ≫ i) g := by
    simpa only [← Category.assoc, hχ] using hg.precomp χ
  rw [Dynamic.mem_centralizer, Dynamic.orbit]
  rw [hc _ (fst T (Gm S).X) (snd T (Gm S).X), mul_inv_cancel_right]

end PointwiseSchemeAction

namespace splitTorus.RelativeCocharacterCentralizer

variable {r : Type u} [CommRing r] (I : Type u) [Fintype I] [DecidableEq I]
  (G : GroupScheme (Spec (CommRingCat.of r))) [IsAffineHom G.X.hom]
  (i : splitTorus (Spec (CommRingCat.of r)) I ⟶ G) (n : I → ℤ)
  (e : (I → ℤ) ≃ₗ[ℤ] (I → ℤ))
  (hfix : CommGroupScheme.groupHom (exponentCocharacter _ I n) ≫
    (exponentIso _ I e).hom = CommGroupScheme.groupHom (exponentCocharacter _ I n))
  {T : Over (Spec (CommRingCat.of r))} (g : T ⟶ G.X)
  (hg : PointwiseSchemeAction.IsTransporter ((exponentIso _ I e).hom ≫ i) i g)

/-- Factor the specified actual transporter point through the actual relative
cocharacter centralizer, retaining the supplied point itself. -/
def transporterPoint : T ⟶ (groupScheme I G i n).X :=
  ((isRepresentedBy_inclusion I G i n).pointsEquiv T).symm
    ⟨g, hg.mem_centralizer_of_fixed_cocharacter
      (CommGroupScheme.groupHom (exponentCocharacter _ I n)) hfix⟩

/-- Inclusion of the constructed centralizer point recovers the original
transporter as an equality of actual over-morphisms. -/
@[reassoc (attr := simp)] theorem transporterPoint_comp :
    transporterPoint I G i n e hfix g hg ≫ (inclusion I G i n).hom.hom = g :=
  (isRepresentedBy_inclusion I G i n).pointsEquiv_symm_comp _

/-- The factored point transports the actual torus inside the relative
centralizer by the same integral-coordinate automorphism, on all refinements. -/
theorem transporterPoint_isTransporter :
    PointwiseSchemeAction.IsTransporter
      ((exponentIso _ I e).hom ≫ torusHom I G i n) (torusHom I G i n)
      (transporterPoint I G i n e hfix g hg) := by
  let : Mono (inclusion I G i n).hom.hom := (isRepresentedBy_inclusion I G i n).1
  apply PointwiseSchemeAction.IsTransporter.of_comp (inclusion I G i n)
  simpa only [Category.assoc, torusHom_comp, transporterPoint_comp] using hg

/-- Factoring a transporter commutes with every refinement of its test scheme. -/
theorem transporterPoint_naturality {U : Over (Spec (CommRingCat.of r))} (a : U ⟶ T) :
    a ≫ transporterPoint I G i n e hfix g hg =
      transporterPoint I G i n e hfix (a ≫ g) (hg.restrict a) := by
  let : Mono (inclusion I G i n).hom.hom := (isRepresentedBy_inclusion I G i n).1
  apply (cancel_mono (inclusion I G i n).hom.hom).mp
  simp only [Category.assoc, transporterPoint_comp]

end splitTorus.RelativeCocharacterCentralizer

end Langlands.GroupScheme
