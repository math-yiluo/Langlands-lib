import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.Rational.Characters
import Langlands.GroupScheme.RepresentedSubgroup

/-! # Central shifts preserve dynamic subgroup functors -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

variable {S : Scheme.{u}} {T : CommGroupScheme S} {G : GroupScheme S}
    (i : T.toGrp ⟶ G) (ν ζ : cocharacterLattice T)

/-- Adding a central cocharacter leaves every actual conjugation orbit unchanged. -/
theorem orbit_add_of_isCentral
    (hζ : IsCentral (CommGroupScheme.groupHom ζ ≫ i))
    {U : Over S} (g : U ⟶ G.X) :
    orbit (CommGroupScheme.groupHom (ν + ζ) ≫ i) g =
      orbit (CommGroupScheme.groupHom ν ≫ i) g := by
  have hc := commute_of_mem_center
    (hζ (U ⊗ (Gm S).X) (snd U (Gm S).X)) (fst U (Gm S).X ≫ g)
  simp only [Grp.comp_hom_hom, ← Category.assoc] at hc
  simp only [orbit, Grp.comp_hom_hom, ← Category.assoc,
    comp_groupHom_add, MonObj.mul_comp]
  rw [mul_inv_rev]
  calc
    _ = ((snd U (Gm S).X ≫ (CommGroupScheme.groupHom ν).hom.hom) ≫ i.hom.hom) *
        (((snd U (Gm S).X ≫ (CommGroupScheme.groupHom ζ).hom.hom) ≫ i.hom.hom) *
          (fst U (Gm S).X ≫ g)) *
        ((snd U (Gm S).X ≫ (CommGroupScheme.groupHom ζ).hom.hom) ≫ i.hom.hom)⁻¹ *
        ((snd U (Gm S).X ≫ (CommGroupScheme.groupHom ν).hom.hom) ≫ i.hom.hom)⁻¹ := by
      group
    _ = _ := by rw [hc.eq]; group

/-- Central shifts preserve the parabolic functor on every scheme test. -/
theorem parabolic_add_of_isCentral
    (hζ : IsCentral (CommGroupScheme.groupHom ζ ≫ i)) :
    parabolic (CommGroupScheme.groupHom (ν + ζ) ≫ i) =
      parabolic (CommGroupScheme.groupHom ν ≫ i) := by
  apply SubgroupFunctor.ext
  intro U
  apply Subgroup.ext
  intro g
  simp only [mem_parabolic, IsOrbitExtension, orbit_add_of_isCentral i ν ζ hζ]

/-- Central shifts preserve the centralizer functor on every scheme test. -/
theorem centralizer_add_of_isCentral
    (hζ : IsCentral (CommGroupScheme.groupHom ζ ≫ i)) :
    centralizer (CommGroupScheme.groupHom (ν + ζ) ≫ i) =
      centralizer (CommGroupScheme.groupHom ν ≫ i) := by
  apply SubgroupFunctor.ext
  intro U
  apply Subgroup.ext
  intro g
  simp only [mem_centralizer, orbit_add_of_isCentral i ν ζ hζ]

/-- Central shifts preserve the identity-limit functor on every scheme test. -/
theorem unipotent_add_of_isCentral
    (hζ : IsCentral (CommGroupScheme.groupHom ζ ≫ i)) :
    unipotent (CommGroupScheme.groupHom (ν + ζ) ≫ i) =
      unipotent (CommGroupScheme.groupHom ν ≫ i) := by
  apply SubgroupFunctor.ext
  intro U
  apply Subgroup.ext
  intro g
  simp only [mem_unipotent, HasLimit, IsOrbitExtension,
    orbit_add_of_isCentral i ν ζ hζ]

variable {P Q : GroupScheme S} (j : P ⟶ G) (l : Q ⟶ G)
    (hj : (parabolic (CommGroupScheme.groupHom (ν + ζ) ≫ i)).IsRepresentedBy j)
    (hl : (parabolic (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy l)

/-- The canonical isomorphism of parabolic representatives for a central shift. -/
def centralShiftParabolicIso
    (hζ : IsCentral (CommGroupScheme.groupHom ζ ≫ i)) : P ≅ Q :=
  hj.isoOfIsRepresentedBy
    (by rw [parabolic_add_of_isCentral i ν ζ hζ]; exact hl)

/-- The central-shift isomorphism commutes with the ambient subgroup maps. -/
theorem centralShiftParabolicIso_hom_comp
    (hζ : IsCentral (CommGroupScheme.groupHom ζ ≫ i)) :
    (centralShiftParabolicIso i ν ζ j l hj hl hζ).hom ≫ l = j :=
  SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

end Langlands.GroupScheme.Dynamic
