/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
# Small free abelian presheaf chains of a Čech family

Source: Stacks Project, Cohomology on Sites, Tags 03AS, 03AT and 03AU.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Limits Opposite

namespace SmallCech

variable {C : Type u} [Category.{v} C] (X : C)

/-- The sum of representables of a formal family over X, using only v-small Hom sets.
Source: Stacks 03AS and 03AT. 
(blueprint: lem-sc-small-cech-free-exact)
-/
def tupleRepresentables (Y : FormalCoproduct.{v} (Over X)) : Cᵒᵖ ⥤ Type v where
  obj Z := Σ i : Y.I, Z.unop ⟶ (Y.obj i).left
  map g := ↾fun a ↦ ⟨a.1, g.unop ≫ a.2⟩
  map_id Z := by
    apply ConcreteCategory.hom_ext
    intro a
    simp
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro a
    simp [Category.assoc]

/-- A map of formal families induces a map between their representable sums.
Source: Stacks 03AS and 03AT. 
(blueprint: lem-sc-small-cech-free-exact)
-/
def tupleRepresentablesMap {Y Y' : FormalCoproduct.{v} (Over X)} (f : Y ⟶ Y') :
    tupleRepresentables X Y ⟶ tupleRepresentables X Y' where
  app Z := ↾fun a ↦ ⟨f.f a.1, a.2 ≫ (f.φ a.1).left⟩
  naturality Z W g := by
    apply ConcreteCategory.hom_ext
    intro a
    simp [tupleRepresentables, Category.assoc]

/-- The functor sending a formal family to its coproduct of free abelian representables.
Source: Stacks 03AS and 03AT. 
(blueprint: lem-sc-small-cech-free-exact)
-/
noncomputable def freePresheaf :
    FormalCoproduct.{v} (Over X) ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{v}) where
  obj Y := tupleRepresentables X Y ⋙ AddCommGrpCat.free
  map f := Functor.whiskerRight (tupleRepresentablesMap X f) AddCommGrpCat.free
  map_id Y := by
    apply NatTrans.ext
    funext Z
    change AddCommGrpCat.free.map _ = 𝟙 _
    rw [← AddCommGrpCat.free.map_id]
    congr 1
    apply ConcreteCategory.hom_ext
    intro a
    simp [tupleRepresentablesMap]
  map_comp f g := by
    apply NatTrans.ext
    funext Z
    change AddCommGrpCat.free.map _ =
      AddCommGrpCat.free.map _ ≫ AddCommGrpCat.free.map _
    rw [← AddCommGrpCat.free.map_comp]
    congr 1
    apply ConcreteCategory.hom_ext
    intro a
    simp [tupleRepresentablesMap, Category.assoc]

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

variable [HasFiniteWidePullbacks C] {ι : Type v} (U : ι → C) (π : ∀ i, U i ⟶ X)

/-- The alternating chains of the free abelian representable sums on categorical products.
Source: Stacks 03AT. 
(blueprint: lem-sc-small-cech-free-exact)
-/
noncomputable abbrev freeComplex : ChainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{v}) ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex _).obj
    ((FormalCoproduct.mk ι (fun i ↦ Over.mk (π i))).cech ⋙ freePresheaf X)

-- The following constructions are made at one fixed presheaf argument. A lift
-- is selected by its composite to X, so all faces select the same lift.
private noncomputable abbrev tupleProduct (p : ℕ) (t : Fin (p + 1) → ι) : Over X :=
  ∏ᶜ (fun k ↦ Over.mk (π (t k)))

private noncomputable def tupleProjection (p : ℕ) (t : Fin (p + 1) → ι)
    (k : Fin (p + 1)) : (tupleProduct X U π p t).left ⟶ U (t k) :=
  (Pi.π (fun k ↦ Over.mk (π (t k))) k).left

private theorem tupleProjection_comm (p : ℕ) (t : Fin (p + 1) → ι)
    (k : Fin (p + 1)) :
    tupleProjection X U π p t k ≫ π (t k) = (tupleProduct X U π p t).hom := by
  exact (Pi.π (fun k ↦ Over.mk (π (t k))) k).w

private noncomputable def tupleProductLift (p : ℕ) (t : Fin (p + 1) → ι) (Z : C)
    (a : ∀ k, Z ⟶ U (t k))
    (ha : ∀ k, a k ≫ π (t k) = a 0 ≫ π (t 0)) :
    Z ⟶ (tupleProduct X U π p t).left :=
  (Pi.lift (fun k ↦ Over.homMk (U := Over.mk (a 0 ≫ π (t 0)))
    (V := Over.mk (π (t k))) (a k) (ha k))).left

private theorem tupleProductLift_projection (p : ℕ) (t : Fin (p + 1) → ι) (Z : C)
    (a : ∀ k, Z ⟶ U (t k))
    (ha : ∀ k, a k ≫ π (t k) = a 0 ≫ π (t 0)) (k : Fin (p + 1)) :
    tupleProductLift X U π p t Z a ha ≫ tupleProjection X U π p t k = a k := by
  exact congrArg (fun f ↦ f.left) (Pi.lift_comp_π (fun k ↦ Over.homMk (U := Over.mk (a 0 ≫ π (t 0)))
    (V := Over.mk (π (t k))) (a k) (ha k)) k)

private theorem tupleProduct_hom_ext {p : ℕ} {t : Fin (p + 1) → ι} {Z : C}
    {a b : Z ⟶ (tupleProduct X U π p t).left}
    (h : ∀ k, a ≫ tupleProjection X U π p t k =
      b ≫ tupleProjection X U π p t k) : a = b := by
  have hb : b ≫ (tupleProduct X U π p t).hom =
      a ≫ (tupleProduct X U π p t).hom := by
    rw [← tupleProjection_comm X U π p t 0, ← Category.assoc,
      ← Category.assoc, h 0]
  let aa : Over.mk (a ≫ (tupleProduct X U π p t).hom) ⟶
      tupleProduct X U π p t := Over.homMk a rfl
  let bb : Over.mk (a ≫ (tupleProduct X U π p t).hom) ⟶
      tupleProduct X U π p t := Over.homMk b hb
  have hab : aa = bb := by
    apply Pi.hom_ext
    intro k
    apply Over.OverMorphism.ext
    exact h k
  exact congrArg (fun f ↦ f.left) hab

private noncomputable def tupleIndexMap {p q : ℕ} (t : Fin (p + 1) → ι)
    (α : Fin (q + 1) → Fin (p + 1)) :
    (tupleProduct X U π p t).left ⟶ (tupleProduct X U π q (t ∘ α)).left :=
  (Pi.lift (fun k ↦ Pi.π (fun k ↦ Over.mk (π (t k))) (α k))).left

private theorem tupleIndexMap_projection {p q : ℕ} (t : Fin (p + 1) → ι)
    (α : Fin (q + 1) → Fin (p + 1)) (k : Fin (q + 1)) :
    tupleIndexMap X U π t α ≫ tupleProjection X U π q (t ∘ α) k =
      tupleProjection X U π p t (α k) := by
  exact congrArg (fun f ↦ f.left)
    (Pi.lift_comp_π (fun k ↦ Pi.π (fun k ↦ Over.mk (π (t k))) (α k)) k)

private abbrev TupleBasis (p : ℕ) (Z : Cᵒᵖ) :=
  Σ t : Fin (p + 1) → ι, Z.unop ⟶ (tupleProduct X U π p t).left

private noncomputable def tupleBase {p : ℕ} {Z : Cᵒᵖ} (x : TupleBasis X U π p Z) : Z.unop ⟶ X :=
  x.2 ≫ tupleProjection X U π p x.1 0 ≫ π (x.1 0)

private theorem tupleBase_eq {p : ℕ} {Z : Cᵒᵖ} (x : TupleBasis X U π p Z)
    (i : Fin (p + 1)) : x.2 ≫ tupleProjection X U π p x.1 i ≫ π (x.1 i) = tupleBase X U π x := by
  simp only [tupleBase, tupleProjection_comm X U π]

private noncomputable def selectedLift (Z : Cᵒᵖ) (φ : Z.unop ⟶ X)
    (h : ∃ l : Σ i : ι, Z.unop ⟶ U i, l.2 ≫ π l.1 = φ) :
    Σ i : ι, Z.unop ⟶ U i := Classical.choose h

private theorem tuple_has_lift {p : ℕ} {Z : Cᵒᵖ} (x : TupleBasis X U π p Z) :
    ∃ l : Σ i : ι, Z.unop ⟶ U i, l.2 ≫ π l.1 = tupleBase X U π x :=
  ⟨⟨x.1 0, x.2 ≫ tupleProjection X U π p x.1 0⟩, by rw [Category.assoc]; rfl⟩

private noncomputable def tupleLift {p : ℕ} {Z : Cᵒᵖ} (x : TupleBasis X U π p Z) :
    Σ i : ι, Z.unop ⟶ U i :=
  selectedLift X U π Z (tupleBase X U π x) (tuple_has_lift X U π x)

private noncomputable def prefixIndices {p : ℕ} {Z : Cᵒᵖ}
    (x : TupleBasis X U π p Z) : Fin (p + 2) → ι :=
  Fin.cons (tupleLift X U π x).1 x.1

private noncomputable def prefixArrows {p : ℕ} {Z : Cᵒᵖ}
    (x : TupleBasis X U π p Z) : ∀ i, Z.unop ⟶ U (prefixIndices X U π x i) :=
  Fin.cases (tupleLift X U π x).2 (fun i ↦ x.2 ≫ tupleProjection X U π p x.1 i)

private theorem prefixArrows_comm {p : ℕ} {Z : Cᵒᵖ}
    (x : TupleBasis X U π p Z) (i : Fin (p + 2)) :
    prefixArrows X U π x i ≫ π (prefixIndices X U π x i) =
      prefixArrows X U π x 0 ≫ π (prefixIndices X U π x 0) := by
  refine Fin.cases ?_ (fun i ↦ ?_) i
  · rfl
  · change (x.2 ≫ tupleProjection X U π p x.1 i) ≫ π (x.1 i) =
      (tupleLift X U π x).2 ≫ π (tupleLift X U π x).1
    rw [show (tupleLift X U π x).2 ≫ π (tupleLift X U π x).1 = tupleBase X U π x from
      Classical.choose_spec (tuple_has_lift X U π x)]
    rw [Category.assoc]
    exact tupleBase_eq X U π x i

private noncomputable def tuplePrefix {p : ℕ} {Z : Cᵒᵖ}
    (x : TupleBasis X U π p Z) : TupleBasis X U π (p + 1) Z :=
  ⟨prefixIndices X U π x,
    tupleProductLift X U π (p + 1) (prefixIndices X U π x) Z.unop
      (prefixArrows X U π x) (prefixArrows_comm X U π x)⟩

private theorem tuplePrefix_pr {p : ℕ} {Z : Cᵒᵖ}
    (x : TupleBasis X U π p Z) (i : Fin (p + 2)) :
    (tuplePrefix X U π x).2 ≫ tupleProjection X U π (p + 1) (tuplePrefix X U π x).1 i =
      prefixArrows X U π x i :=
  tupleProductLift_projection X U π (p + 1) (prefixIndices X U π x) Z.unop
    (prefixArrows X U π x) (prefixArrows_comm X U π x) i

private noncomputable def tupleFace {p : ℕ} {Z : Cᵒᵖ} (i : Fin (p + 2))
    (x : TupleBasis X U π (p + 1) Z) : TupleBasis X U π p Z :=
  ⟨x.1 ∘ i.succAbove, x.2 ≫ tupleIndexMap X U π x.1 i.succAbove⟩

private theorem tupleFace_pr {p : ℕ} {Z : Cᵒᵖ} (i : Fin (p + 2))
    (x : TupleBasis X U π (p + 1) Z) (k : Fin (p + 1)) :
    (tupleFace X U π i x).2 ≫ tupleProjection X U π p (tupleFace X U π i x).1 k =
      x.2 ≫ tupleProjection X U π (p + 1) x.1 (i.succAbove k) := by
  dsimp [tupleFace]
  rw [Category.assoc, tupleIndexMap_projection X U π]

private theorem tupleFace_base {p : ℕ} {Z : Cᵒᵖ} (i : Fin (p + 2))
    (x : TupleBasis X U π (p + 1) Z) :
    tupleBase X U π (tupleFace X U π i x) = tupleBase X U π x := by
  unfold tupleBase
  rw [← Category.assoc, tupleFace_pr X U π, Category.assoc]
  exact tupleBase_eq X U π x _

private theorem tuple_ext {p : ℕ} {Z : Cᵒᵖ} {x y : TupleBasis X U π p Z}
    (ht : x.1 = y.1)
    (h : ∀ k, HEq (x.2 ≫ tupleProjection X U π p x.1 k)
      (y.2 ≫ tupleProjection X U π p y.1 k)) : x = y := by
  obtain ⟨t, a⟩ := x
  obtain ⟨t', b⟩ := y
  dsimp at ht
  subst t'
  have hab : a = b := tupleProduct_hom_ext X U π (fun k ↦ eq_of_heq (h k))
  cases hab
  rfl

private theorem tupleFace_prefix_zero {p : ℕ} {Z : Cᵒᵖ} (x : TupleBasis X U π p Z) :
    tupleFace X U π 0 (tuplePrefix X U π x) = x := by
  apply tuple_ext X U π
  · funext i
    simp [tupleFace, tuplePrefix, prefixIndices]
  · intro i
    rw [tupleFace_pr X U π]
    simp only [Fin.zero_succAbove]
    rw [tuplePrefix_pr X U π]
    rfl

private theorem tupleLift_face {p : ℕ} {Z : Cᵒᵖ} (i : Fin (p + 2))
    (x : TupleBasis X U π (p + 1) Z) :
    tupleLift X U π (tupleFace X U π i x) = tupleLift X U π x := by
  unfold tupleLift
  congr 1
  exact tupleFace_base X U π i x

private theorem tupleFace_prefix_succ {p : ℕ} {Z : Cᵒᵖ}
    (i : Fin (p + 2)) (x : TupleBasis X U π (p + 1) Z) :
    tupleFace X U π i.succ (tuplePrefix X U π x) = tuplePrefix X U π (tupleFace X U π i x) := by
  apply tuple_ext X U π
  · change (Fin.cons (tupleLift X U π x).1 x.1) ∘ i.succ.succAbove =
      Fin.cons (tupleLift X U π (tupleFace X U π i x)).1 (x.1 ∘ i.succAbove)
    rw [tupleLift_face X U π]
    exact Fin.cons_comp_succ_succAbove _ _ _
  · intro k
    rw [tupleFace_pr X U π, tuplePrefix_pr X U π, tuplePrefix_pr X U π]
    refine Fin.cases ?_ (fun k ↦ ?_) k
    · change HEq (prefixArrows X U π x (i.succ.succAbove 0))
        (tupleLift X U π (tupleFace X U π i x)).2
      erw [Fin.succ_succAbove_zero]
      change HEq (tupleLift X U π x).2 (tupleLift X U π (tupleFace X U π i x)).2
      exact (Sigma.ext_iff.mp (tupleLift_face X U π i x).symm).2
    · change HEq (prefixArrows X U π x (i.succ.succAbove k.succ))
        ((tupleFace X U π i x).2 ≫ tupleProjection X U π p (tupleFace X U π i x).1 k)
      erw [Fin.succ_succAbove_succ]
      change HEq (x.2 ≫ tupleProjection X U π (p + 1) x.1 (i.succAbove k))
        ((tupleFace X U π i x).2 ≫ tupleProjection X U π p (tupleFace X U π i x).1 k)
      rw [tupleFace_pr X U π]

-- Extend the prefix and deletion functions by the free abelian group functor.
private noncomputable def freePrefix (p : ℕ) (Z : Cᵒᵖ) :
    ((freeComplex X U π).X p).obj Z ⟶ ((freeComplex X U π).X (p + 1)).obj Z :=
  AddCommGrpCat.free.map (↾fun x ↦ tuplePrefix X U π x)

private noncomputable def freeFace (p : ℕ) (Z : Cᵒᵖ)
    (i : Fin (p + 2)) :
    ((freeComplex X U π).X (p + 1)).obj Z ⟶ ((freeComplex X U π).X p).obj Z :=
  AddCommGrpCat.free.map (↾fun x ↦ tupleFace X U π i x)

private theorem freePrefix_face_zero (p : ℕ) (Z : Cᵒᵖ) :
    freePrefix X U π p Z ≫ freeFace X U π p Z 0 = 𝟙 _ := by
  change AddCommGrpCat.free.map (↾fun x ↦ tuplePrefix X U π x) ≫
    AddCommGrpCat.free.map (↾fun x ↦ tupleFace X U π 0 x) = 𝟙 _
  rw [← Functor.map_comp, ← Functor.map_id]
  congr 1
  apply ConcreteCategory.hom_ext
  intro x
  exact tupleFace_prefix_zero X U π x

private theorem freePrefix_face_succ (p : ℕ) (Z : Cᵒᵖ)
    (i : Fin (p + 2)) :
    freePrefix X U π (p + 1) Z ≫ freeFace X U π (p + 1) Z i.succ =
      freeFace X U π p Z i ≫ freePrefix X U π p Z := by
  change AddCommGrpCat.free.map (↾fun x ↦ tuplePrefix X U π x) ≫
      AddCommGrpCat.free.map (↾fun x ↦ tupleFace X U π i.succ x) =
    AddCommGrpCat.free.map (↾fun x ↦ tupleFace X U π i x) ≫
      AddCommGrpCat.free.map (↾fun x ↦ tuplePrefix X U π x)
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  apply ConcreteCategory.hom_ext
  intro x
  exact tupleFace_prefix_succ X U π i x

private theorem freeComplex_d_app (p : ℕ) (Z : Cᵒᵖ) :
    ((freeComplex X U π).d (p + 1) p).app Z =
      Finset.univ.sum (fun i : Fin (p + 2) ↦
        (-1 : ℤ) ^ (i : ℕ) • freeFace X U π p Z i) := by
  simp only [freeComplex, AlgebraicTopology.alternatingFaceMapComplex_obj_d,
    AlgebraicTopology.AlternatingFaceMapComplex.objD]
  change ((evaluation Cᵒᵖ AddCommGrpCat).obj Z).map
    (Finset.univ.sum (fun i : Fin (p + 2) ↦ (-1 : ℤ) ^ (i : ℕ) •
      SimplicialObject.δ
        ((FormalCoproduct.mk ι (fun i ↦ Over.mk (π i))).cech ⋙ freePresheaf X) i)) = _
  rw [Functor.map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Functor.map_zsmul]
  congr 1

-- The first face is the identity; successor faces cancel the other composite.
private theorem freeComplex_evaluation_contracting (n : ℕ) (Z : Cᵒᵖ) :
    freePrefix X U π (n + 1) Z ≫ ((freeComplex X U π).d (n + 2) (n + 1)).app Z +
      ((freeComplex X U π).d (n + 1) n).app Z ≫ freePrefix X U π n Z = 𝟙 _ := by
  rw [freeComplex_d_app X U π (n + 1) Z, freeComplex_d_app X U π n Z]
  rw [Preadditive.comp_sum, Fin.sum_univ_succ]
  simp only [Preadditive.comp_zsmul, Fin.val_zero, pow_zero, one_smul,
    freePrefix_face_zero, Fin.val_succ, pow_succ, mul_neg_one,
    neg_smul, Preadditive.comp_neg, freePrefix_face_succ,
    Preadditive.sum_comp, Preadditive.zsmul_comp]
  rw [Finset.sum_neg_distrib]
  simp

/-- The free Čech presheaf chains are exact in positive degrees, for any family.
Source: Stacks Project, Cohomology on Sites, Tags 03AT and 03AU.
(blueprint: lem-sc-small-cech-free-exact)

Proof: Evaluate the chain complex at Z. Its basis in degree n consists of an
(n+1)-tuple of family indices together with a map from Z to the corresponding
product over X. Partition the basis by the composite Z -> X. The product universal
property identifies each fibre with (n+1)-tuples of lifts of that composite to the
family. Face maps delete coordinates. If the lift set is empty, every chain group
of that fibre is zero. Otherwise choose a lift and prepend it: the alternating
boundary satisfies d h + h d = id in positive degrees. Thus every fibre complex
is exact, and so is their direct sum. Kernels and cokernels in abelian presheaves
are evaluated objectwise, so objectwise exactness proves the assertion.
Only the basis and Hom sets must be v-small; Z ranges over C without being part
of a product indexing set. The argument uses no covering assumption. -/
theorem freeComplex_exactAt (q : ℕ) : (freeComplex X U π).ExactAt (q + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (q + 2) (q + 1) q (by simp) (by simp)]
  let L := (freeComplex X U π).sc' (q + 2) (q + 1) q
  have he (Z : Cᵒᵖ) : (L.map ((evaluation Cᵒᵖ AddCommGrpCat).obj Z)).Exact := by
    rw [ShortComplex.ab_exact_iff]
    intro x hx
    refine ⟨freePrefix X U π (q + 1) Z x, ?_⟩
    have hid := ConcreteCategory.congr_hom (freeComplex_evaluation_contracting X U π q Z) x
    change ((freeComplex X U π).d (q + 1) q).app Z x = 0 at hx
    change ((freeComplex X U π).d (q + 2) (q + 1)).app Z
        (freePrefix X U π (q + 1) Z x) +
      freePrefix X U π q Z (((freeComplex X U π).d (q + 1) q).app Z x) = x at hid
    change ((freeComplex X U π).d (q + 2) (q + 1)).app Z
      (freePrefix X U π (q + 1) Z x) = x
    simpa only [hx, map_zero, add_zero] using hid
  rw [ShortComplex.exact_iff_isZero_homology, IsZero.iff_id_eq_zero]
  apply NatTrans.ext
  funext Z
  have hz : IsZero (((evaluation Cᵒᵖ AddCommGrpCat).obj Z).obj L.homology) :=
    ((L.mapHomologyIso ((evaluation Cᵒᵖ AddCommGrpCat).obj Z)).isZero_iff).mp
      ((L.map ((evaluation Cᵒᵖ AddCommGrpCat).obj Z)).exact_iff_isZero_homology.mp (he Z))
  exact hz.eq_of_src _ _

end SmallCech
end CategoryTheory
