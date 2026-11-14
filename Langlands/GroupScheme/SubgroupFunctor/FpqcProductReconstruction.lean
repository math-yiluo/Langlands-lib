import Langlands.GroupScheme.SubgroupFunctor.FpqcDescent
import Langlands.GroupScheme.Rational.SplitTorusFactorization
import Langlands.GroupScheme.Rational.LeviFactorization

/-! # Reconstructing subgroup maps from fpqc product factorizations -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SubgroupFunctor

variable {S : Scheme.{u}} {A B P Q G : GroupScheme S}

/-- An effective epimorphism on the source detects containment in a monic
subgroup on every test scheme. -/
theorem range_comp_le_iff_of_effectiveEpi
    (e : A ⟶ P) [EffectiveEpi e.hom.hom.left]
    (i : P ⟶ G) (j : Q ⟶ G) [Mono j.hom.hom] :
    range (e ≫ i) ≤ range j ↔ range i ≤ range j := by
  constructor
  · intro h
    have hi : i.hom.hom ∈ (range j).carrier P.X := by
      apply mem_range_of_comp_mem_range j e.hom.hom
      exact h A.X (mem_range.mpr ⟨𝟙 A.X, by simp⟩)
    intro U x hx
    obtain ⟨y, rfl⟩ := mem_range.mp hx
    exact (range j).comp_mem y hi
  · intro h U x hx
    obtain ⟨y, rfl⟩ := mem_range.mp hx
    apply h U
    exact mem_range.mpr ⟨y ≫ e.hom.hom, Category.assoc _ _ _⟩

/-- A subgroup functor contains a commuting product if and only if it
contains both factors. This is a statement about the pointwise range. -/
theorem range_prodHom_le_iff
    (a : A ⟶ G) (b : B ⟶ G)
    (hab : ∀ (U : Over S) (x : U ⟶ A.X) (y : U ⟶ B.X),
      Commute (x ≫ a.hom.hom) (y ≫ b.hom.hom))
    (F : SubgroupFunctor G) :
    range (prodHom a b hab) ≤ F ↔ range a ≤ F ∧ range b ≤ F := by
  constructor
  · intro h
    constructor
    · intro U x hx
      obtain ⟨y, rfl⟩ := mem_range.mp hx
      apply h U
      refine mem_range.mpr ⟨y ≫ (prodInl A B).hom.hom, ?_⟩
      rw [Category.assoc, ← Grp.comp_hom_hom, prodInl_prodHom]
    · intro U x hx
      obtain ⟨y, rfl⟩ := mem_range.mp hx
      apply h U
      refine mem_range.mpr ⟨y ≫ (prodInr A B).hom.hom, ?_⟩
      rw [Category.assoc, ← Grp.comp_hom_hom, prodInr_prodHom]
  · rintro ⟨ha, hb⟩ U x hx
    obtain ⟨p, rfl⟩ := mem_range.mp hx
    rw [comp_prodHom]
    exact (F.carrier U).mul_mem
      (ha U (mem_range.mpr ⟨_, rfl⟩))
      (hb U (mem_range.mpr ⟨_, rfl⟩))

/-- An fpqc product factorization reconstructs containment in any monic
subgroup from containment of the two factors. -/
theorem range_le_iff_of_fpqc_product
    (a : A ⟶ G) (b : B ⟶ G)
    (hab : ∀ (U : Over S) (x : U ⟶ A.X) (y : U ⟶ B.X),
      Commute (x ≫ a.hom.hom) (y ≫ b.hom.hom))
    (i : P ⟶ G) (e : A ⊗ B ⟶ P) [EffectiveEpi e.hom.hom.left]
    (he : e ≫ i = prodHom a b hab) (j : Q ⟶ G) [Mono j.hom.hom] :
    range i ≤ range j ↔ range a ≤ range j ∧ range b ≤ range j := by
  rw [← range_comp_le_iff_of_effectiveEpi e i j, he, range_prodHom_le_iff]

/-- Monic subgroups reconstructed from the same two factor ranges coincide. -/
theorem range_eq_of_fpqc_products
    {B' P' : GroupScheme S} (a : A ⟶ G) (b : B ⟶ G) (b' : B' ⟶ G)
    (hab : ∀ (U : Over S) (x : U ⟶ A.X) (y : U ⟶ B.X),
      Commute (x ≫ a.hom.hom) (y ≫ b.hom.hom))
    (hab' : ∀ (U : Over S) (x : U ⟶ A.X) (y : U ⟶ B'.X),
      Commute (x ≫ a.hom.hom) (y ≫ b'.hom.hom))
    (i : P ⟶ G) [Mono i.hom.hom]
    (e : A ⊗ B ⟶ P) [EffectiveEpi e.hom.hom.left]
    (he : e ≫ i = prodHom a b hab)
    (i' : P' ⟶ G) [Mono i'.hom.hom]
    (e' : A ⊗ B' ⟶ P') [EffectiveEpi e'.hom.hom.left]
    (he' : e' ≫ i' = prodHom a b' hab')
    (hb : range b = range b') : range i = range i' := by
  have hi := (range_le_iff_of_fpqc_product a b hab i e he i).mp le_rfl
  have hi' := (range_le_iff_of_fpqc_product a b' hab' i' e' he' i').mp le_rfl
  apply le_antisymm
  · apply (range_le_iff_of_fpqc_product a b hab i e he i').mpr
    exact ⟨hi'.1, hb ▸ hi'.2⟩
  · apply (range_le_iff_of_fpqc_product a b' hab' i' e' he' i).mpr
    exact ⟨hi.1, hb ▸ hi.2⟩

/-- The homomorphism reconstructed from an fpqc product factorization and
the containment of both factors in a given monic subgroup. -/
def factorOfFpqcProduct
    (a : A ⟶ G) (b : B ⟶ G)
    (hab : ∀ (U : Over S) (x : U ⟶ A.X) (y : U ⟶ B.X),
      Commute (x ≫ a.hom.hom) (y ≫ b.hom.hom))
    (i : P ⟶ G) (e : A ⊗ B ⟶ P) [EffectiveEpi e.hom.hom.left]
    (he : e ≫ i = prodHom a b hab) (j : Q ⟶ G) [Mono j.hom.hom]
    (ha : range a ≤ range j) (hb : range b ≤ range j) : P ⟶ Q :=
  (show (range j).IsRepresentedBy j from ⟨inferInstance, rfl⟩).factorHom i
    ((range_le_iff_of_fpqc_product a b hab i e he j).mpr ⟨ha, hb⟩)

/-- The reconstructed homomorphism has the prescribed ambient composite. -/
@[reassoc (attr := simp)]
theorem factorOfFpqcProduct_comp
    (a : A ⟶ G) (b : B ⟶ G)
    (hab : ∀ (U : Over S) (x : U ⟶ A.X) (y : U ⟶ B.X),
      Commute (x ≫ a.hom.hom) (y ≫ b.hom.hom))
    (i : P ⟶ G) (e : A ⊗ B ⟶ P) [EffectiveEpi e.hom.hom.left]
    (he : e ≫ i = prodHom a b hab) (j : Q ⟶ G) [Mono j.hom.hom]
    (ha : range a ≤ range j) (hb : range b ≤ range j) :
    factorOfFpqcProduct a b hab i e he j ha hb ≫ j = i :=
  SubgroupFunctor.IsRepresentedBy.factorHom_comp _ _ _

end Langlands.GroupScheme.SubgroupFunctor
