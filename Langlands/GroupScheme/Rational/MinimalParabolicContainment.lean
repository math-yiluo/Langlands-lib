import Langlands.GroupScheme.Rational.MinimalParabolicStatement
import Langlands.GroupScheme.Rational.LeviFactorization

/-! # Torus containment in represented dynamic parabolics -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A commutative subgroup lies in the dynamic parabolic of each of its
cocharacters on every test scheme. -/
theorem range_le_dynamicParabolic {S : Scheme.{u}}
    {T : CommGroupScheme S} {G : GroupScheme S}
    (i : T.toGrp ⟶ G) (χ : (Gm S).toGrp ⟶ T.toGrp) :
    SubgroupFunctor.range i ≤ Dynamic.parabolic (χ ≫ i) :=
  (range_le_torusCentralizer i).trans
    ((torusCentralizer_le_dynamicCentralizer i χ).trans
      (Dynamic.centralizer_le_parabolic (χ ≫ i)))

namespace Dynamic

variable {S : Scheme.{u}} {T : CommGroupScheme S} {G P : GroupScheme S}
  (i : T.toGrp ⟶ G) (χ : (Gm S).toGrp ⟶ T.toGrp) {j : P ⟶ G}

/-- The ambient commutative subgroup factors through any actual representative
of the dynamic parabolic of one of its cocharacters. -/
def parabolicTorusFactor (hj : (parabolic (χ ≫ i)).IsRepresentedBy j) : T.toGrp ⟶ P :=
  hj.factorHom i (range_le_dynamicParabolic i χ)

theorem parabolicTorusFactor_comp (hj : (parabolic (χ ≫ i)).IsRepresentedBy j) :
    parabolicTorusFactor i χ hj ≫ j = i :=
  hj.factorHom_comp _ _

end Dynamic

/-- A generic dynamic parabolic, once known to be minimal, supplies an actual
minimal parabolic containing the original torus. Genericity is used only by
the explicit structural premise. -/
theorem exists_minimalParabolic_containing_of_genericMinimal
    (hminimal : GenericMinimalParabolicStatement.{u})
    (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T) :
    letI := hG.isAffineHom
    IsGenericCocharacter i ν →
      ∃ (P : GroupScheme (Spec (CommRingCat.of k))) (j : P ⟶ G),
        IsMinimalParabolicSubgroup j ∧ ∃ f : T.toGrp ⟶ P, f ≫ j = i := by
  have := hG.isAffineHom
  intro hν
  obtain ⟨P, j, hj, heq⟩ :=
    isMinimalParabolicFunctor_iff_exists.mp (hminimal k G hG T i hi ν hν)
  have := hj.1.isClosedSubgroup.mono
  have hrep :
      (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy j :=
    ⟨Over.mono_of_mono_left _, heq⟩
  exact ⟨P, j, hj, Dynamic.parabolicTorusFactor i (CommGroupScheme.groupHom ν) hrep,
    Dynamic.parabolicTorusFactor_comp i (CommGroupScheme.groupHom ν) hrep⟩

end Langlands.GroupScheme
