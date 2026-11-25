/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDescentDataCategory
import WeilConjectures.AlgebraicGeometry.FpqcCanonicalPullbackDatum

/-! Auxiliary steps for Stacks Project, Descent, Lemma 0241. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace CategoryTheory

/-- Pullback of descent data exists for every morphism of schemes.
Source: Stacks Project, Descent, Lemma 023Y (pullback), specialized to a fixed base.
(blueprint: lem-galois-descent-pullback-construction).

Proof: For each datum A, use V' = V ×_X X' with projections q and p. Given f₀,f₁
with equal composites to S and a point z over f₀, compose z with q, apply A's
transport to (f₀r,f₁r), and lift the resulting point together with f₁ to V'.
The two projection equations prove naturality, the identity law and the cocycle law.
For a compatible morphism, use its usual pullback map. Its compatibility follows
by projecting to V and X' and applying the original compatibility equation.
The functor laws follow from those of Over.pullback. The pullback square is the
canonical one, and its first projection gives both IsBaseChange and naturality. -/
theorem descent_pullback_construction
    {S X X' : Scheme.{u}} (a : X ⟶ S) (r : X' ⟶ X) :
    ∃ (F : Over.DescentDataCategory a ⥤ Over.DescentDataCategory (r ≫ a))
      (q : ∀ A : Over.DescentDataCategory a, (F.obj A).V.left ⟶ A.V.left),
      (∀ A, ∃ hq : q A ≫ A.V.hom = (F.obj A).V.hom ≫ r,
        IsPullback (q A) (F.obj A).V.hom A.V.hom r ∧
        Over.DescentDatum.IsBaseChange rfl hq A.datum (F.obj A).datum) ∧
      ∀ A B (f : A ⟶ B), (F.map f).hom.left ≫ q B = q A ≫ f.hom.left := by
  classical
  let E (A : Over.DescentDataCategory a) :
      Over.DescentDatum (r ≫ a) (Over.mk (pullback.snd A.V.hom r)) :=
    (exists_canonical_pullback_descent_datum a (r ≫ a) r rfl A.datum).choose
  have bc (A : Over.DescentDataCategory a) :
      Over.DescentDatum.IsBaseChange rfl (pullback.condition (f := A.V.hom) (g := r))
        A.datum (E A) :=
    (exists_canonical_pullback_descent_datum a (r ≫ a) r rfl A.datum).choose_spec
  let obj (A : Over.DescentDataCategory a) : Over.DescentDataCategory (r ≫ a) :=
    ⟨Over.mk (pullback.snd A.V.hom r), E A⟩
  let map {A B : Over.DescentDataCategory a} (f : A ⟶ B) : (obj A).V ⟶ (obj B).V :=
    Over.homMk (pullback.lift (pullback.fst A.V.hom r ≫ f.hom.left)
      (pullback.snd A.V.hom r) (by simp [pullback.condition])) (by simp [obj])
  have map_fst {A B : Over.DescentDataCategory a} (f : A ⟶ B) :
      (map f).left ≫ pullback.fst B.V.hom r = pullback.fst A.V.hom r ≫ f.hom.left := by
    simp [map]
  have compatible {A B : Over.DescentDataCategory a} (f : A ⟶ B) :
      ∀ {T : Scheme.{u}} (i j : T ⟶ X') (h : i ≫ (r ≫ a) = j ≫ (r ≫ a))
        (z : Over.mk i ⟶ (obj A).V),
        (obj B).datum.transport i j h (z ≫ map f) =
          (obj A).datum.transport i j h z ≫ map f := by
    intro T i j h z
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · have hA := bc A i j h z
      have hB := bc B i j h (z ≫ map f)
      have hf := congrArg (fun k ↦ k.left) (f.commutes (i ≫ r) (j ≫ r)
        (by simpa only [Category.assoc] using h)
        (Over.homMk (z.left ≫ pullback.fst A.V.hom r)
          (by
            rw [Category.assoc, pullback.condition, ← Category.assoc]
            exact congrArg (fun k ↦ k ≫ r) (Over.w z))))
      dsimp [obj] at *
      simp only [Category.assoc, map_fst] at hB ⊢
      rw [← hB]
      have hh := hf.trans (congrArg (fun k ↦ k ≫ f.hom.left) hA)
      convert hh using 1
      · congr 2
      · simp only [Category.assoc]
    · exact (Over.w _).trans (Over.w _).symm
  let F : Over.DescentDataCategory a ⥤ Over.DescentDataCategory (r ≫ a) :=
    { obj := obj
      map := fun f ↦ ⟨map f, compatible f⟩
      map_id := by
        intro A
        apply Over.DescentDataCategory.Hom.ext
        apply Over.OverMorphism.ext
        change (pullback.lift (pullback.fst A.V.hom r ≫ 𝟙 A.V.left)
          (pullback.snd A.V.hom r) _) = 𝟙 _
        apply pullback.hom_ext <;> simp
      map_comp := by
        intro A B C f g
        apply Over.DescentDataCategory.Hom.ext
        apply Over.OverMorphism.ext
        change (map (f ≫ g)).left = (map f).left ≫ (map g).left
        change (pullback.lift (pullback.fst A.V.hom r ≫ (f.hom ≫ g.hom).left)
          (pullback.snd A.V.hom r) _) = _
        apply pullback.hom_ext <;> simp [map, Category.assoc] }
  refine ⟨F, fun A ↦ pullback.fst A.V.hom r, ?_, ?_⟩
  · intro A
    exact ⟨pullback.condition, IsPullback.of_hasPullback A.V.hom r, bc A⟩
  · intro A B f
    exact map_fst f

end CategoryTheory
