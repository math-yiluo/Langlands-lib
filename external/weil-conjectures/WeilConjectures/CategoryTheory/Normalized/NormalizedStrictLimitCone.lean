/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Tower
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic

import WeilConjectures.CategoryTheory.Normalized.NormalizedStrictLimitBase
import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Existence

/-! # Normalized strict inverse limit cones with an arbitrary initial term

Source: Stacks Project, sites-cohomology.tex, Tags 0940 and 0941.
-/

@[expose] public section
set_option autoImplicit false
universe a v b t w g
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
namespace CategoryTheory

/-- A strict derived inverse limit has its normalized homotopy-limit cone after an
exact coefficient equivalence and a positive-tail identification. The initial term
of the new tower is arbitrary. The normalization concerns every ordinary map into
the termwise inverse limit, and does not involve principal quotients or completion.

Source: Stacks Project, sites-cohomology.tex, Tags 0940 and 0941, the natural Roos
triangle and its ordinary-limit inclusion
(blueprint: lem-sfb-normalized-strict-limit-cone).

Proof: normalizedStrictLimitBase gives the homotopy-limit cone and the identity
eta followed by its nth leg = Q of the ordinary nth limit projection. The exact
derived equivalence preserves products and distinguished triangles. Transport the
cone through the given tail isomorphism. Choose a homotopy-limit cone on the full
tower G; its positive-tail restriction is again a homotopy-limit cone. Uniqueness
of homotopy limits gives an isomorphism from the transported normalized cone to
that restriction, compatible with every positive leg. Extend the full cone along
this isomorphism. It remains a homotopy limit and retains the required positive
legs. The normalization identity, precomposed by Q(b), gives the assertion. All
steps apply to zero and unbounded complexes and arbitrary initial terms; no
regularity or exactness of ordinary products is required. -/
theorem normalizedStrictLimitCone
    {A : Type a} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{g} A]
    {B : Type b} [Category.{t} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
    [HasDerivedCategory.{w} B]
    [HasLimitsOfShape ℕᵒᵖ A] [HasCountableProducts A]
    [HasCountableProducts (DerivedCategory A)]
    [HasCountableProducts (DerivedCategory B)]
    (R : DerivedCategory (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory A)
    (η : (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ R)
    (hR : R.IsRightDerivedFunctor η
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ)))
    (e : A ≌ B) [e.functor.Additive] [e.inverse.Additive]
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (G : ℕᵒᵖ ⥤ DerivedCategory B)
    (α : X.asFunctor ⋙ DerivedCategory.Q ⋙ e.mapDerivedCategory.functor ≅
      addOpFunctor 1 ⋙ G) :
    let Y := e.mapDerivedCategory.functor.obj (R.obj (DerivedCategory.Q.obj X))
    ∃ p : (Functor.const ℕᵒᵖ).obj Y ⟶ G,
      IsHomotopyLimit (Cone.mk Y p) ∧
      ∀ (P : CochainComplex A ℤ)
        (b : P ⟶ ((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)).obj X)
        (n : ℕ),
        e.mapDerivedCategory.functor.map (DerivedCategory.Q.map b ≫ η.app X) ≫
            p.app (op (n + 1)) =
          e.mapDerivedCategory.functor.map (DerivedCategory.Q.map
            (b ≫ (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app X)) ≫
              α.hom.app (op n) := by
  classical
  obtain ⟨q, hq, hη⟩ := normalizedStrictLimitBase R η hR X
  let ed := e.functor.mapDerivedCategory
  have : ed.Additive := Functor.additive_of_preserves_binary_products ed
  let cB := ed.mapCone (Cone.mk _ q)
  have hcB : IsHomotopyLimit cB := hq.map ed
  let ct := (Cone.postcompose α.hom).obj cB
  have hct : IsHomotopyLimit ct := hcB.of_iso α ct (Iso.refl _)
    (by intro n; simp [ct])
  let cf := homotopyLimitCone G
  have hcf : IsHomotopyLimit cf := isHomotopyLimit_homotopyLimitCone G
  obtain ⟨d, hd⟩ := hct.exists_iso (hcf.whiskerAdd 1)
  let c := cf.extend d.hom
  have hc : IsHomotopyLimit c := hcf.of_iso (Iso.refl G) c d.symm
    (by intro n; simp [c])
  refine ⟨c.π, hc, ?_⟩
  intro P b n
  have hleg : c.π.app (op (n + 1)) = ct.π.app (op n) := hd n
  rw [hleg]
  change ed.map (DerivedCategory.Q.map b ≫ η.app X) ≫
    (ed.map (q.app (op n)) ≫ α.hom.app (op n)) = _
  rw [← Category.assoc, ← ed.map_comp, Category.assoc, hη,
    ← DerivedCategory.Q.map_comp]
  rfl

end CategoryTheory
