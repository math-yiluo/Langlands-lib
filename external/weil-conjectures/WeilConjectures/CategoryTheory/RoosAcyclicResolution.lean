/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import WeilConjectures.CategoryTheory.RoosFinitePrefixLimits
import WeilConjectures.CategoryTheory.RoosPrefixAcyclic

/-!
# The functorial acyclic resolution of a tower

The finite-prefix construction of Stacks Project, Tag 07KW, Lemma 15.88.1.
(blueprint: lem-pc-roos-functorial-acyclic-resolution).
-/

@[expose] public section

universe u

namespace CategoryTheory

open Limits

/-- The product of all levels of a tower, with componentwise maps. 
(blueprint: lem-pc-roos-functorial-acyclic-resolution)
-/
noncomputable def roosProductFunctor :
    (ℕᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u} where
  obj A := ∏ᶜ fun n : ℕ ↦ A.obj (Opposite.op n)
  map φ := Limits.Pi.map (fun n : ℕ ↦ φ.app (Opposite.op n))
  map_id A := by
    apply Pi.hom_ext
    intro n
    simp
  map_comp φ ψ := by
    apply Pi.hom_ext
    intro n
    simp

/-- The natural endomorphism `1 - shift` of the levelwise product functor. 
(blueprint: lem-pc-roos-functorial-acyclic-resolution)
-/
noncomputable def roosProductDifferential :
    roosProductFunctor.{u} ⟶ roosProductFunctor.{u} where
  app A := towerTransitionEndomorphism
    (fun n ↦ A.map (homOfLE (Nat.le_succ n)).op)
  naturality _ _ φ := by
    dsimp only [roosProductFunctor]
    exact towerTransitionEndomorphism_natural_backward _ _ _
      (fun n ↦ (φ.naturality (homOfLE (Nat.le_succ n)).op).symm)

private noncomputable def prefixLimitIso (s : ℕ) (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) :
    limit (roosPrefixTower s A) ≅ roosProductFunctor.obj A :=
  (limit.isLimit _).conePointUniqueUpToIso (roosPrefixConeIsLimit s A)

@[reassoc] private theorem prefixLimitIso_π (s : ℕ) (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) (i : ℕ) :
    (prefixLimitIso s A).hom ≫ Pi.π (fun j : ℕ ↦ A.obj (Opposite.op j)) i =
      limit.π (roosPrefixTower s A) (Opposite.op (i + 1)) ≫
        roosPrefixEval s A (i + 1) i (by omega) := by
  change Pi.lift _ ≫ _ = _
  rw [Pi.lift_comp_π]
  rfl

private noncomputable def prefixLimitNatIso (s : ℕ) :
    roosPrefixFunctor.{u} s ⋙ lim ≅ roosProductFunctor :=
  NatIso.ofComponents (prefixLimitIso s) (by
    intro A B φ
    apply Pi.hom_ext
    intro i
    change limMap ((roosPrefixFunctor s).map φ) ≫ (prefixLimitIso s B).hom ≫ _ =
      (prefixLimitIso s A).hom ≫ Limits.Pi.map (fun j ↦ φ.app (Opposite.op j)) ≫ _
    rw [prefixLimitIso_π, Pi.map_π, prefixLimitIso_π_assoc]
    dsimp only [roosPrefixFunctor]
    change limMap ((roosPrefixFunctor s).map φ) ≫
      limit.π (roosPrefixTower s B) (Opposite.op (i + 1)) ≫ _ = _
    erw [limMap_π_assoc]
    rfl)

@[reassoc] private theorem prefixLimitIso_π_at (s : ℕ)
    (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) (n i : ℕ) (h : i < n + s) :
    (prefixLimitIso s A).hom ≫ Pi.π (fun j : ℕ ↦ A.obj (Opposite.op j)) i =
      limit.π (roosPrefixTower s A) (Opposite.op n) ≫ roosPrefixEval s A n i h := by
  rw [prefixLimitIso_π]
  exact roosPrefixCone_coordinate s A (limit.cone _) (i + 1) n i (by omega) h

private theorem prefixLimitDifferential (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) :
    lim.map (roosPrefixProjection.app A) ≫ (prefixLimitNatIso 0).hom.app A =
      (prefixLimitNatIso 1).hom.app A ≫ roosProductDifferential.app A := by
  apply Pi.hom_ext
  intro i
  change limMap (roosPrefixProjection.app A) ≫ (prefixLimitIso 0 A).hom ≫ _ =
    (prefixLimitIso 1 A).hom ≫ towerTransitionEndomorphism _ ≫ _
  rw [prefixLimitIso_π]
  dsimp only [roosPrefixProjection, roosPrefixFunctor]
  erw [limMap_π_assoc]
  simp only [towerTransitionEndomorphism, towerProductShift, Preadditive.sub_comp,
    Pi.lift_comp_π, Preadditive.comp_sub]
  erw [prefixLimitIso_π_at 1 A (i + 1) i (by omega),
    prefixLimitIso_π_at_assoc 1 A (i + 1) (i + 1) (by omega)]
  ext x
  rfl

/-- Finite-prefix towers give a functorial length-one limit-acyclic resolution.

Source: Stacks Project, More on Algebra, Tag 07KW, Lemma 15.88.1, proof.
(blueprint: lem-pc-roos-functorial-acyclic-resolution).

Proof: for a tower A indexed starting at zero, put U(A)_n = product of A_i for
0 <= i <= n, and V(A)_n = product of A_i for 0 <= i < n. Transitions forget
the last coordinate. Send a in A_n to its successive transitions in every A_i.
Send (x_i) in U(A)_n to (x_i - f_i(x_(i+1))) for i < n. These maps commute
with transitions. The first is injective by coordinate n. The kernel of the
second consists of successive-transition tuples. The second is surjective:
set x_n = 0 and solve downwards x_i = y_i + f_i(x_(i+1)). Thus the sequence
is levelwise short exact, hence short exact in the abelian functor category.
Apply tower morphisms coordinatewise to obtain functors U,V and natural maps.
Compatible finite prefixes identify each of lim U(A), lim V(A) with the full
product, naturally in A; the induced map is exactly 1 - shift. Both towers
have surjective transitions, so their positive derived limits vanish by
lem-pc-tower-surjective-lim-acyclic (Tag 07KW (3)). The empty prefix at n=0
is the zero group, so the construction also works at the initial index. -/
theorem exists_roos_acyclic_resolution
    [EnoughInjectives (ℕᵒᵖ ⥤ AddCommGrpCat.{u})]
    [(lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).Additive] :
    ∃ (U V : (ℕᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ (ℕᵒᵖ ⥤ AddCommGrpCat.{u}))
      (i : 𝟭 (ℕᵒᵖ ⥤ AddCommGrpCat.{u}) ⟶ U) (p : U ⟶ V)
      (w : ∀ A, i.app A ≫ p.app A = 0),
      (∀ A, (ShortComplex.mk (i.app A) (p.app A) (w A)).ShortExact) ∧
      ∃ (eU : U ⋙ lim ≅ roosProductFunctor) (eV : V ⋙ lim ≅ roosProductFunctor),
        (∀ A, lim.map (p.app A) ≫ eV.hom.app A =
          eU.hom.app A ≫ roosProductDifferential.app A) ∧
        ∀ (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) (q : ℕ), 1 ≤ q →
          IsZero ((lim.rightDerived q).obj (U.obj A)) ∧
          IsZero ((lim.rightDerived q).obj (V.obj A)) := by
  let U := roosPrefixFunctor 1
  let V := roosPrefixFunctor 0
  refine ⟨U, V, roosPrefixInclusion, roosPrefixProjection,
    roosPrefixInclusion_projection, ?_, ?_⟩
  · intro A
    simpa [U, V] using roosPrefix_shortExact A
  · refine ⟨prefixLimitNatIso 1, prefixLimitNatIso 0, ?_, ?_⟩
    · exact prefixLimitDifferential
    · intro A q hq
      exact ⟨roosPrefixAcyclic 1 A q hq, roosPrefixAcyclic 0 A q hq⟩

end CategoryTheory
