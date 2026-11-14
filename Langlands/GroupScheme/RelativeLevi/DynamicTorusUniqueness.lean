import Langlands.GroupScheme.Rational.DynamicLeviConjugacyReduction

/-! # Dynamic Levi complements containing the defining cocharacter -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.DynamicLeviConjugacy

variable {S : Scheme.{u}} {G P L : GroupScheme S}
    (χ : (Gm S).toGrp ⟶ G) {j : P ⟶ G}
    (hj : (Dynamic.parabolic χ).IsRepresentedBy j)
    (l : L ⟶ P) (q : P ⟶ L) (hlq : l ≫ q = 𝟙 L)
    (hker : ∀ (V : Over S) (x : V ⟶ P.X),
      x ≫ q.hom.hom = 1 ↔ x ≫ j.hom.hom ∈ (Dynamic.unipotent χ).carrier V)

include hj hlq hker in
/-- A retract complement of the dynamic radical containing the defining cocharacter
is precisely the dynamic centralizer, on every test scheme. -/
theorem range_eq_centralizer_of_cocharacter_factors [IsSeparated G.X.hom]
    (lamL : (Gm S).toGrp ⟶ L) (hμ : lamL ≫ l ≫ j = χ) :
    SubgroupFunctor.range (l ≫ j) = Dynamic.centralizer χ := by
  have hχ : parabolicCocharacter χ hj = lamL ≫ l :=
    hj.hom_ext ((parabolicCocharacter_comp χ hj).trans hμ.symm)
  have hμq : parabolicCocharacter χ hj ≫ q = lamL := by
    rw [hχ, Category.assoc, hlq, Category.comp_id]
  have hμ' : χ ≫ (G.innerIso (1 : Over.mk (𝟙 S) ⟶ G.X)).hom =
      (parabolicCocharacter χ hj ≫ q) ≫ l ≫ j := by
    rw [innerIso_one_hom, Category.comp_id, hμq, hμ]
  have h := range_comp_innerIso_inv_eq_centralizer l q hlq hker
    ((Dynamic.unipotent χ).carrier (Over.mk (𝟙 S))).one_mem hμ'
  simpa only [← innerIso_inv_hom, inv_one, innerIso_one_hom, Category.comp_id] using h

include hj hlq hker in
/-- A complement containing the defining cocharacter is canonically isomorphic
to any representative of its dynamic centralizer. -/
def centralizerComplementIso [IsSeparated G.X.hom]
    (lamL : (Gm S).toGrp ⟶ L) (hμ : lamL ≫ l ≫ j = χ)
    {Z : GroupScheme S} {z : Z ⟶ G}
    (hz : (Dynamic.centralizer χ).IsRepresentedBy z) : L ≅ Z := by
  have : Mono l.hom.hom :=
    mono_of_mono_fac (hom_hom_comp_hom_hom l q hlq)
  have : Mono j.hom.hom := hj.1
  let hrep : (Dynamic.centralizer χ).IsRepresentedBy (l ≫ j) :=
    ⟨by simpa only [Grp.comp_hom_hom] using
        (inferInstance : Mono (l.hom.hom ≫ j.hom.hom)),
      range_eq_centralizer_of_cocharacter_factors χ hj l q hlq hker lamL hμ⟩
  exact hrep.isoOfIsRepresentedBy hz

include hj hlq hker in
theorem centralizerComplementIso_hom_comp [IsSeparated G.X.hom]
    (lamL : (Gm S).toGrp ⟶ L) (hμ : lamL ≫ l ≫ j = χ)
    {Z : GroupScheme S} {z : Z ⟶ G}
    (hz : (Dynamic.centralizer χ).IsRepresentedBy z) :
    (centralizerComplementIso χ hj l q hlq hker lamL hμ hz).hom ≫ z = l ≫ j := by
  exact SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ hz

end Langlands.GroupScheme.DynamicLeviConjugacy
