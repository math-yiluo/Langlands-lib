import Langlands.GroupScheme.Reductive.CommutingMultiplication
import Langlands.GroupScheme.Reductive.NormalCentralizer

/-! # Retraction onto a factor of a commuting multiplication isomorphism -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {H K G : GroupScheme S}
variable (j : H ⟶ G) (i : K ⟶ G)
variable (hc : ∀ (T : Over S) (h : T ⟶ H.X) (n : T ⟶ K.X),
  Commute (h ≫ j.hom.hom) (n ≫ i.hom.hom))
variable [IsIso (commutingSubgroupMultiplicationHom j i hc)]

/-- The actual first-factor projection: inverse multiplication followed by the
first projection of the product of group schemes. -/
def commutingFactorRetraction : G ⟶ H :=
  inv (commutingSubgroupMultiplicationHom j i hc) ≫ fst H K

/-- Applying the projection to a product of the two factor images recovers its
first coordinate, on any test scheme. -/
theorem comp_commutingFactorRetraction_product {T : Over S}
    (h : T ⟶ H.X) (n : T ⟶ K.X) :
    ((h ≫ j.hom.hom) * (n ≫ i.hom.hom)) ≫
      (commutingFactorRetraction j i hc).hom.hom = h := by
  rw [← comp_subgroupMultiplication]
  simp only [commutingFactorRetraction, Grp.comp_hom_hom, Grp.fst_hom_hom]
  have hinv :
      subgroupMultiplication j i ≫
        (inv (commutingSubgroupMultiplicationHom j i hc)).hom.hom = 𝟙 _ := by
    change (commutingSubgroupMultiplicationHom j i hc).hom.hom ≫ _ = _
    rw [← Grp.comp_hom_hom, IsIso.hom_inv_id, Grp.id_hom_hom]
    rfl
  rw [Category.assoc, ← Category.assoc (subgroupMultiplication j i), hinv,
    Category.id_comp, lift_fst]

/-- The first factor is a section of the constructed projection. -/
@[simp]
theorem comp_commutingFactorRetraction :
    j ≫ commutingFactorRetraction j i hc = 𝟙 H := by
  apply hom_ext_points
  intro T h
  simpa only [Grp.comp_hom_hom, ← Category.assoc, MonObj.one_comp, mul_one,
    Grp.id_hom_hom, Category.comp_id] using
    comp_commutingFactorRetraction_product j i hc h (1 : T ⟶ K.X)

/-- The complementary factor maps to the identity under the projection. -/
@[simp]
theorem complementary_comp_commutingFactorRetraction {T : Over S}
    (n : T ⟶ K.X) :
    (n ≫ i.hom.hom) ≫ (commutingFactorRetraction j i hc).hom.hom = 1 := by
  simpa only [MonObj.one_comp, one_mul] using
    comp_commutingFactorRetraction_product j i hc (1 : T ⟶ H.X) n

/-- A point is killed by the projection precisely when it belongs to the
complementary factor's actual range on that same test scheme. -/
theorem comp_commutingFactorRetraction_eq_one_iff {T : Over S}
    (g : T ⟶ G.X) :
    g ≫ (commutingFactorRetraction j i hc).hom.hom = 1 ↔
      g ∈ (SubgroupFunctor.range i).carrier T := by
  constructor
  · intro hg
    let v := g ≫ (inv (commutingSubgroupMultiplicationHom j i hc)).hom.hom
    have hfst : v ≫ fst H.X K.X = 1 := by
      simpa only [commutingFactorRetraction, Grp.comp_hom_hom, Grp.fst_hom_hom,
        Category.assoc, v] using hg
    have hmul :
        ((v ≫ fst H.X K.X) ≫ j.hom.hom) *
          ((v ≫ snd H.X K.X) ≫ i.hom.hom) = g := by
      rw [← comp_subgroupMultiplication, lift_comp_fst_snd]
      change (g ≫ (inv (commutingSubgroupMultiplicationHom j i hc)).hom.hom) ≫
        (commutingSubgroupMultiplicationHom j i hc).hom.hom = g
      rw [Category.assoc, ← Grp.comp_hom_hom, IsIso.inv_hom_id,
        Grp.id_hom_hom, Category.comp_id]
    rw [hfst, MonObj.one_comp, one_mul] at hmul
    exact SubgroupFunctor.mem_range.mpr ⟨v ≫ snd H.X K.X, hmul⟩
  · rintro ⟨n, rfl⟩
    exact complementary_comp_commutingFactorRetraction j i hc n

/-- Every kernel point commutes with every point of the first factor. -/
theorem commute_of_comp_commutingFactorRetraction_eq_one
    {T : Over S} (h : T ⟶ H.X) (g : T ⟶ G.X)
    (hg : g ≫ (commutingFactorRetraction j i hc).hom.hom = 1) :
    Commute (h ≫ j.hom.hom) g := by
  obtain ⟨n, rfl⟩ :=
    (comp_commutingFactorRetraction_eq_one_iff j i hc g).mp hg
  exact hc T h n

/-- The full scheme-theoretic kernel of the projection centralizes the first
factor, including after every change of test scheme. -/
theorem kernel_commutingFactorRetraction_range_le_centralizer :
    SubgroupFunctor.range (kernelι (commutingFactorRetraction j i hc)) ≤
      (AutomorphicAction.conjugation j).fixedSubgroup := by
  apply (range_le_conjugation_fixedSubgroup_iff j _).mpr
  intro T h x
  apply commute_of_comp_commutingFactorRetraction_eq_one j i hc h
  exact (mem_range_kernelι_iff _ _).mp (SubgroupFunctor.mem_range.mpr ⟨x, rfl⟩)

end Langlands.GroupScheme
