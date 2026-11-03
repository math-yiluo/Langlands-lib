import Langlands.AlgebraicGeometry.FullProductFactorizationSieve

/-! # Comparing full-product factorizations in schemes and over a base -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.FullProductFactorization

variable {S : Scheme.{u}}

/-- The source product in the sieve and the chosen product in `Over S` agree. -/
def testProductIso {X Y T : Over S} (t : T ⟶ Y) :
    pullback X.hom (t.left ≫ Y.hom) ≅ (X ⊗ T).left :=
  pullback.congrHom rfl t.w

@[reassoc (attr := simp)]
lemma testProductIso_hom_fst {X Y T : Over S} (t : T ⟶ Y) :
    (testProductIso (X := X) t).hom ≫ pullback.fst X.hom T.hom =
      pullback.fst X.hom (t.left ≫ Y.hom) := by
  simp [testProductIso, pullback.congrHom_hom, pullback.lift_fst]

@[reassoc (attr := simp)]
lemma testProductIso_hom_snd {X Y T : Over S} (t : T ⟶ Y) :
    (testProductIso (X := X) t).hom ≫ pullback.snd X.hom T.hom =
      pullback.snd X.hom (t.left ≫ Y.hom) := by
  simp [testProductIso, pullback.congrHom_hom, pullback.lift_snd]

/-- Compatibility of the source comparison with the actual product map. -/
lemma testProductIso_hom_whiskerLeft {X Y T : Over S} (t : T ⟶ Y) :
    (testProductIso (X := X) t).hom ≫ (X ◁ t).left = productMap X.hom Y.hom t.left := by
  apply pullback.hom_ext <;> simp [Category.assoc]

/-- A factorization of a morphism over the base automatically respects the base. -/
lemma exists_over_lift_iff {A B D : Over S} (d : D ⟶ B) (a : A ⟶ B) :
    (∃ q : A ⟶ D, q ≫ d = a) ↔
      ∃ q : A.left ⟶ D.left, q ≫ d.left = a.left := by
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨q.left, congrArg (fun h => h.left) hq⟩
  · rintro ⟨q, hq⟩
    refine ⟨Over.homMk q ?_, ?_⟩
    · rw [← d.w, ← Category.assoc, hq, a.w]
    · exact Over.OverMorphism.ext hq

/-- Scheme-sieve membership is the full-product factorization in `Over S`. -/
lemma mem_iff_over {X Y D T : Over S} (d : D ⟶ X ⊗ Y) (t : T ⟶ Y) :
    sieve X.hom Y.hom d.left t.left ↔ ∃ q : X ⊗ T ⟶ D, q ≫ d = (X ◁ t) := by
  rw [exists_over_lift_iff]
  let e := testProductIso (X := X) t
  have he : e.hom ≫ (X ◁ t).left = productMap X.hom Y.hom t.left :=
    testProductIso_hom_whiskerLeft t
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨e.inv ≫ q, ?_⟩
    rw [Category.assoc e.inv q d.left, hq, ← he, e.inv_hom_id_assoc]
  · rintro ⟨q, hq⟩
    refine ⟨e.hom ≫ q, ?_⟩
    rw [Category.assoc e.hom q d.left, hq, he]

end Langlands.AlgebraicGeometry.FullProductFactorization
