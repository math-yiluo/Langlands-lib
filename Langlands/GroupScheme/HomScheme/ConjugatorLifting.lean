import Langlands.GroupScheme.HomScheme.ConjugationMap
import Mathlib.CategoryTheory.MorphismProperty.Composition

/-! # Lifting relative homomorphisms and specified conjugators -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.HomScheme

open TorusSubgroupModuli

variable {S : Scheme.{u}} {H G : GroupScheme S} {T T' T'' : Over S}

/-- Conjugate an arbitrary relative family by a point on its test scheme. -/
def conjugateRelative (i : RelativeHom H G T) (g : T ⟶ G.X) :
    RelativeHom H G T :=
  i ≫ (((baseChange T.hom).obj G).innerIso
    (RelativeLevi.pulledBackPoint G T g)).hom

/-- Arbitrary relative conjugation commutes with restriction. -/
theorem evaluate_conjugateRelative (a : T' ⟶ T) (i : RelativeHom H G T)
    (g : T ⟶ G.X) :
    evaluate a (conjugateRelative i g) =
      conjugateRelative (evaluate a i) (a ≫ g) := by
  apply hom_ext_points
  intro V x
  apply (familyPointsEquiv (G := G) a V).injective
  rw [familyPointsEquiv_comp_evaluate]
  change familyPointsEquiv (G := H) a V x ≫ i.hom.hom ≫
      ((((baseChange T.hom).obj G).innerIso
        (RelativeLevi.pulledBackPoint G T g)).hom).hom.hom =
    familyPointsEquiv (G := G) a V (x ≫ (evaluate a i).hom.hom ≫
      ((((baseChange T'.hom).obj G).innerIso
        (RelativeLevi.pulledBackPoint G T' (a ≫ g))).hom).hom.hom)
  rw [← Category.assoc, comp_innerIso_hom, ← Category.assoc, comp_innerIso_hom,
    map_mul, map_mul, map_inv, RelativeLevi.familyPointsEquiv_constantPoint]
  congr 2
  exact (familyPointsEquiv_comp_evaluate a i V x).symm

@[simp]
theorem conjugateRelative_one (i : RelativeHom H G T) :
    conjugateRelative i 1 = i := by
  change i ≫ (((baseChange T.hom).obj G).innerIso
    (RelativeLevi.pulledBackPointHom G T 1)).hom = i
  rw [map_one, innerIso_one_hom, Category.comp_id]

/-- Restriction lifts homomorphisms and every specified conjugator between
their restrictions. -/
def HasConjugatorLifting (H G : GroupScheme S) : MorphismProperty (Over S) :=
  fun _ _ a =>
    Function.Surjective (evaluate (H := H) (G := G) a) ∧
    ∀ (i j : RelativeHom H G _) (g₀ : _ ⟶ G.X),
      evaluate a j = conjugateRelative (evaluate a i) g₀ →
      ∃ g : _ ⟶ G.X, a ≫ g = g₀ ∧ j = conjugateRelative i g

/-- Lifting along a composite follows by lifting successively, including
the prescribed conjugating element. -/
theorem hasConjugatorLifting_comp (b : T'' ⟶ T') (a : T' ⟶ T)
    (hb : HasConjugatorLifting H G b) (ha : HasConjugatorLifting H G a) :
    HasConjugatorLifting H G (b ≫ a) := by
  constructor
  · intro i₀
    obtain ⟨i₁, hi₁⟩ := hb.1 i₀
    obtain ⟨i, hi⟩ := ha.1 i₁
    exact ⟨i, by rw [evaluate_comp, hi, hi₁]⟩
  · intro i j g₀ h
    rw [evaluate_comp, evaluate_comp] at h
    obtain ⟨g₁, hg₁, hj₁⟩ := hb.2 (evaluate a i) (evaluate a j) g₀ h
    obtain ⟨g, hg, hj⟩ := ha.2 i j g₁ hj₁
    exact ⟨g, by rw [Category.assoc, hg, hg₁], hj⟩

/-- Every isomorphism of test schemes has the specified lifting property. -/
theorem hasConjugatorLifting_of_isIso (a : T' ⟶ T) [IsIso a] :
    HasConjugatorLifting H G a := by
  constructor
  · intro i₀
    refine ⟨evaluate (inv a) i₀, ?_⟩
    rw [← evaluate_comp, IsIso.hom_inv_id, evaluate_id]
  · intro i j g₀ h
    refine ⟨inv a ≫ g₀, by simp, ?_⟩
    have h' := congrArg (evaluate (H := H) (G := G) (inv a)) h
    rw [← evaluate_comp, IsIso.inv_hom_id, evaluate_id,
      evaluate_conjugateRelative, ← evaluate_comp, IsIso.inv_hom_id,
      evaluate_id] at h'
    exact h'

instance hasConjugatorLifting_isMultiplicative (H G : GroupScheme S) :
    (HasConjugatorLifting H G).IsMultiplicative where
  id_mem _ := hasConjugatorLifting_of_isIso _
  comp_mem a b ha hb := hasConjugatorLifting_comp a b ha hb

instance hasConjugatorLifting_respectsIso (H G : GroupScheme S) :
    (HasConjugatorLifting H G).RespectsIso :=
  MorphismProperty.respectsIso_of_isStableUnderComposition
    (fun _ _ a _ => hasConjugatorLifting_of_isIso a)

end Langlands.GroupScheme.HomScheme
