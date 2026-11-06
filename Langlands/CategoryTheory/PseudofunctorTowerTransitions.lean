import Mathlib.CategoryTheory.Bicategory.Functor.Cat
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.Data.Nat.Init

/-! # Actual transitions along arbitrary maps of a tower -/

noncomputable section
universe v w u u'
open CategoryTheory CategoryTheory.Bicategory

namespace Langlands.CategoryTheory.PseudofunctorTowerTransitions

variable {D : Type u} [Category.{v} D] (F : LocallyDiscrete D ⥤ᵖ Cat.{w, u'})

/-- Transport an action object along an equality of its source test. -/
lemma actionObjectCongr {A A' B : D} (hA : A = A')
    (q : A ⟶ B) (q' : A' ⟶ B) (hq : HEq q q')
    (L : F.obj (.mk A)) (L' : F.obj (.mk A')) (hL : HEq L L') :
    (F.map q.toLoc).toFunctor.obj L = (F.map q'.toLoc).toFunctor.obj L' := by
  cases hA
  cases hq
  cases hL
  rfl

/-- Adjacent transitions extend to every displayed later-to-earlier tower map. -/
lemma hasTransition (A : ℕ → D)
    (q : ∀ {n m : ℕ}, n ≤ m → (A m ⟶ A n))
    (s : ∀ n, A (n + 1) ⟶ A n)
    (hid : ∀ n, q (le_refl n) = 𝟙 (A n))
    (hcomp : ∀ {n m : ℕ} (h : n ≤ m), s m ≫ q h = q (h.trans (Nat.le_succ m)))
    (L : ∀ n, F.obj (.mk (A n)))
    (e : ∀ n, (F.map (s n).toLoc).toFunctor.obj (L (n + 1)) ≅ L n)
    {n m : ℕ} (hnm : n ≤ m) :
    Nonempty ((F.map (q hnm).toLoc).toFunctor.obj (L m) ≅ L n) := by
  induction m, hnm using Nat.le_induction with
  | base =>
      rw [hid n]
      exact ⟨(Cat.Hom.toNatIso (F.mapId (.mk (A n)))).app (L n)⟩
  | succ m hnm ih =>
      obtain ⟨d⟩ := ih
      have h : (s m).toLoc ≫ (q hnm).toLoc =
          (q (hnm.trans (Nat.le_succ m))).toLoc := by
        rw [← Quiver.Hom.comp_toLoc, hcomp]
      exact ⟨(Cat.Hom.toNatIso (F.mapComp' (s m).toLoc (q hnm).toLoc
          (q (hnm.trans (Nat.le_succ m))).toLoc h)).app (L (m + 1)) ≪≫
        (F.map (q hnm).toLoc).toFunctor.mapIso (e m) ≪≫ d⟩

/-- An actual isomorphism along the displayed map, chosen from the proved existence. -/
def transitionIso (A : ℕ → D)
    (q : ∀ {n m : ℕ}, n ≤ m → (A m ⟶ A n))
    (s : ∀ n, A (n + 1) ⟶ A n)
    (hid : ∀ n, q (le_refl n) = 𝟙 (A n))
    (hcomp : ∀ {n m : ℕ} (h : n ≤ m), s m ≫ q h = q (h.trans (Nat.le_succ m)))
    (L : ∀ n, F.obj (.mk (A n)))
    (e : ∀ n, (F.map (s n).toLoc).toFunctor.obj (L (n + 1)) ≅ L n)
    {n m : ℕ} (hnm : n ≤ m) :
    (F.map (q hnm).toLoc).toFunctor.obj (L m) ≅ L n :=
  (hasTransition F A (fun {_ _} h => q h) s hid (fun {_ _} h => hcomp h) L e hnm).some

end Langlands.CategoryTheory.PseudofunctorTowerTransitions
