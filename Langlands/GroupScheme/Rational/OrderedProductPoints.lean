import Langlands.GroupScheme.Rational.WeightSemigroup
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! # All-test coordinates and point formulas for ordered multiplication -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {B : Scheme.{u}}

section Coordinates

variable {I : Type v} [Finite I] (H : I → GroupScheme B)

/-- The underlying fan of a finite product, allowing an index universe
independent of the base-scheme universe. -/
def finiteProductIsLimit :
    IsLimit (Fan.mk (∏ᶜ H).X fun i => (Pi.π H i).hom.hom) :=
  isLimitOfHasProductOfPreservesLimit (Grp.forget (Over B)) H

/-- Coordinates on every test scheme for an independently indexed finite
product of actual group schemes. -/
def finiteProductPointsEquiv (T : Over B) :
    (T ⟶ (∏ᶜ H).X) ≃* (∀ i, T ⟶ (H i).X) where
  toFun x i := x ≫ (Pi.π H i).hom.hom
  invFun x := Fan.IsLimit.lift (finiteProductIsLimit H) x
  left_inv x := by
    apply Fan.IsLimit.hom_ext (finiteProductIsLimit H)
    intro i
    exact Fan.IsLimit.fac (finiteProductIsLimit H) _ i
  right_inv x := by
    funext i
    exact Fan.IsLimit.fac (finiteProductIsLimit H) x i
  map_mul' x y := by
    funext i
    exact MonObj.mul_comp x y (Pi.π H i).hom.hom

@[simp]
theorem finiteProductPointsEquiv_apply (T : Over B)
    (x : T ⟶ (∏ᶜ H).X) (i : I) :
    finiteProductPointsEquiv H T x i = x ≫ (Pi.π H i).hom.hom := rfl

@[simp]
theorem finiteProductPointsEquiv_symm_π (T : Over B)
    (x : ∀ i, T ⟶ (H i).X) (i : I) :
    (finiteProductPointsEquiv H T).symm x ≫ (Pi.π H i).hom.hom = x i :=
  Fan.IsLimit.fac (finiteProductIsLimit H) x i

/-- The finite product coordinates commute with every map of test schemes. -/
theorem finiteProductPointsEquiv_naturality {T V : Over B} (a : V ⟶ T)
    (x : T ⟶ (∏ᶜ H).X) :
    finiteProductPointsEquiv H V (a ≫ x) =
      fun i => a ≫ finiteProductPointsEquiv H T x i := by
  funext i
  exact Category.assoc a x (Pi.π H i).hom.hom

/-- Reassembling a family of points commutes with every map of test schemes. -/
theorem finiteProductPointsEquiv_symm_naturality {T V : Over B} (a : V ⟶ T)
    (x : ∀ i, T ⟶ (H i).X) :
    a ≫ (finiteProductPointsEquiv H T).symm x =
      (finiteProductPointsEquiv H V).symm (fun i => a ≫ x i) := by
  apply Fan.IsLimit.hom_ext (finiteProductIsLimit H)
  intro i
  change (a ≫ (finiteProductPointsEquiv H T).symm x) ≫ (Pi.π H i).hom.hom =
    (finiteProductPointsEquiv H V).symm (fun i => a ≫ x i) ≫ (Pi.π H i).hom.hom
  simp only [Category.assoc, finiteProductPointsEquiv_symm_π]

end Coordinates

section OrderedPoints

variable {n : ℕ} {G : GroupScheme B} {H : Fin n → GroupScheme B}

/-- The ordered product on points, in the same order as `orderedMultiplication`. -/
def orderedPoints (j : ∀ i, H i ⟶ G) {T : Over B}
    (x : ∀ i, T ⟶ (H i).X) : T ⟶ G.X :=
  (List.ofFn fun i => x i ≫ (j i).hom.hom).prod

private theorem comp_list_prod {T V : Over B} (a : V ⟶ T)
    (l : List (T ⟶ G.X)) :
    a ≫ l.prod = (l.map (fun x => a ≫ x)).prod := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.prod_cons, List.map_cons, MonObj.comp_mul, ih]

private theorem list_prod_comp {Q : GroupScheme B} (q : G ⟶ Q) {T : Over B}
    (l : List (T ⟶ G.X)) :
    l.prod ≫ q.hom.hom = (l.map (fun x => x ≫ q.hom.hom)).prod := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.prod_cons, List.map_cons, MonObj.mul_comp, ih]

/-- Evaluating the actual multiplication morphism gives the ordered point product. -/
theorem comp_orderedMultiplication (j : ∀ i, H i ⟶ G)
    {T : Over B} (x : T ⟶ (∏ᶜ H).X) :
    x ≫ orderedMultiplication j =
      orderedPoints j (finiteProductPointsEquiv H T x) := by
  unfold orderedMultiplication orderedPoints
  rw [comp_list_prod]
  simp only [List.map_ofFn, Function.comp_def, finiteProductPointsEquiv_apply, Category.assoc]

/-- A family reassembled into a product point evaluates to its ordered product. -/
@[simp]
theorem finiteProductPointsEquiv_symm_orderedMultiplication (j : ∀ i, H i ⟶ G)
    {T : Over B} (x : ∀ i, T ⟶ (H i).X) :
    (finiteProductPointsEquiv H T).symm x ≫ orderedMultiplication j =
      orderedPoints j x := by
  rw [comp_orderedMultiplication, MulEquiv.apply_symm_apply]

/-- Ordered point multiplication commutes with changing the test scheme. -/
theorem orderedPoints_naturality (j : ∀ i, H i ⟶ G)
    {T V : Over B} (a : V ⟶ T) (x : ∀ i, T ⟶ (H i).X) :
    a ≫ orderedPoints j x = orderedPoints j (fun i => a ≫ x i) := by
  unfold orderedPoints
  rw [comp_list_prod]
  simp only [List.map_ofFn, Function.comp_def, Category.assoc]

/-- Ordered point multiplication commutes with a homomorphism of targets. -/
theorem orderedPoints_map {Q : GroupScheme B}
    {R : Fin n → GroupScheme B} (j : ∀ i, H i ⟶ G) (k : ∀ i, R i ⟶ Q)
    (q : G ⟶ Q) (p : ∀ i, H i ⟶ R i)
    (h : ∀ i, j i ≫ q = p i ≫ k i)
    {T : Over B} (x : ∀ i, T ⟶ (H i).X) :
    orderedPoints j x ≫ q.hom.hom =
      orderedPoints k (fun i => x i ≫ (p i).hom.hom) := by
  unfold orderedPoints
  rw [list_prod_comp]
  simp only [List.map_ofFn, Function.comp_def]
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext i
  have hi := congrArg (fun f => f.hom.hom) (h i)
  change (j i).hom.hom ≫ q.hom.hom = (p i).hom.hom ≫ (k i).hom.hom at hi
  simpa only [Category.assoc] using congrArg (fun f => x i ≫ f) hi

/-- The scheme multiplication map is an isomorphism exactly when the ordered
factorization function is bijective on every test scheme. -/
theorem isIso_orderedMultiplication_iff (j : ∀ i, H i ⟶ G) :
    IsIso (orderedMultiplication j) ↔
      ∀ T : Over B, Function.Bijective (orderedPoints j (T := T)) := by
  rw [isIso_iff_yoneda_map_bijective]
  apply forall_congr'
  intro T
  have heq : (fun x : T ⟶ (∏ᶜ H).X => x ≫ orderedMultiplication j) =
      (orderedPoints j (T := T)) ∘ finiteProductPointsEquiv H T := by
    funext x
    exact comp_orderedMultiplication j x
  rw [heq]
  exact Function.Bijective.of_comp_iff _ (finiteProductPointsEquiv H T).bijective

/-- The equivalent unique-factorization criterion retains arbitrary test schemes. -/
theorem isIso_orderedMultiplication_iff_existsUnique (j : ∀ i, H i ⟶ G) :
    IsIso (orderedMultiplication j) ↔
      ∀ (T : Over B) (g : T ⟶ G.X),
        ∃! x : ∀ i, T ⟶ (H i).X, orderedPoints j x = g := by
  rw [isIso_orderedMultiplication_iff]
  exact forall_congr' fun T => Function.bijective_iff_existsUnique (orderedPoints j (T := T))

end OrderedPoints

end Langlands.GroupScheme.RelativeRoot
