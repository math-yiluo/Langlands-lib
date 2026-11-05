import Langlands.GroupScheme.Rational.LeviAmbientTransport
import Langlands.GroupScheme.Rational.TorusCentralizerConjugacy

/-! # Rational Levi centralizers of conjugate commutative subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G P R : GroupScheme (Spec (CommRingCat.of k))}
  {A B : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Conjugacy inside a group mapping into the ambient parabolic transports an
existing rational Levi presentation of the whole-torus centralizer. -/
theorem SubgroupConjugate.exists_rationalLevi_torusCentralizer
    {a : A.toGrp ⟶ R} {b : B.toGrp ⟶ R}
    (hconj : SubgroupConjugate a b) (r : R ⟶ P) (j : P ⟶ G)
    (h : ∃ (L : GroupScheme (Spec (CommRingCat.of k))) (l : L ⟶ P),
      IsRationalLeviSubgroup l ∧
        (torusCentralizer (a ≫ r ≫ j)).IsRepresentedBy (l ≫ j)) :
    ∃ (L : GroupScheme (Spec (CommRingCat.of k))) (l : L ⟶ P),
      IsRationalLeviSubgroup l ∧
        (torusCentralizer (b ≫ r ≫ j)).IsRepresentedBy (l ≫ j) := by
  obtain ⟨g, e, he⟩ := hconj.postcomp r
  obtain ⟨L, l, hl, hcent⟩ := h
  have hsquare :
      (a ≫ r ≫ j) ≫ (G.innerIso (g ≫ j.hom.hom)).hom =
        e.hom ≫ (b ≫ r ≫ j) := by
    rw [← Category.assoc a r, Category.assoc (a ≫ r), ← innerIso_hom_comp,
      ← Category.assoc, he, Category.assoc]
    simp only [Category.assoc]
  refine ⟨L, l ≫ (P.innerIso g).hom, hl.comp_iso (P.innerIso g), ?_⟩
  have hrep := hcent.torusCentralizer_of_iso_square e
    (G.innerIso (g ≫ j.hom.hom)) hsquare
  simpa only [Category.assoc, innerIso_hom_comp] using hrep

/-- Rational Levi centralizer existence is invariant under subgroup conjugacy
inside any group mapping to the proposed ambient parabolic. -/
def LeviTorusCentralizerConjugacyStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G P R : GroupScheme (Spec (CommRingCat.of k))) (r : R ⟶ P) (j : P ⟶ G)
    (A B : CommGroupScheme (Spec (CommRingCat.of k)))
    (a : A.toGrp ⟶ R) (b : B.toGrp ⟶ R),
    SubgroupConjugate a b →
    (∃ (L : GroupScheme (Spec (CommRingCat.of k))) (l : L ⟶ P),
      IsRationalLeviSubgroup l ∧
        (torusCentralizer (a ≫ r ≫ j)).IsRepresentedBy (l ≫ j)) →
    ∃ (L : GroupScheme (Spec (CommRingCat.of k))) (l : L ⟶ P),
      IsRationalLeviSubgroup l ∧
        (torusCentralizer (b ≫ r ≫ j)).IsRepresentedBy (l ≫ j)

/-- The uniform conjugacy transport theorem. -/
theorem leviTorusCentralizerConjugacy : LeviTorusCentralizerConjugacyStatement.{u} := by
  intro k _ G P R r j A B a b hconj h
  exact hconj.exists_rationalLevi_torusCentralizer r j h

end Langlands.GroupScheme
