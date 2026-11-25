/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
import WeilConjectures.CategoryTheory.DerivedModuleDirectSums

/-! # Coproduct generators of shifted free quotient complexes

Source: Stacks Project, Remark 15.60.11 (Tag 09PB).
(blueprint: lem-pc-derived-shifted-free-coproduct).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- A direct sum of complexes supported in single degrees becomes a coproduct of
shifts of the rank-one module after localization and shift by `-1`.
Source: Stacks Project, Remark 15.60.11 (Tag 09PB).
(blueprint: lem-pc-derived-shifted-free-coproduct).

Proof: apply `derivedModuleDirectSums` to the family of single complexes. Transport
that coproduct along the image of the given quotient isomorphism under `Q`. The shift
functor by `-1` is an equivalence and therefore preserves the coproduct. A single complex
supported in degree `d` is the shift by `-d` of the complex supported in degree zero;
compatibility of `Q` with shifts identifies its image with the corresponding shift of
`singleFunctor 0`. Combine the shifts to obtain degree `-d - 1`, and precompose the
shifted coprojections with these comparison isomorphisms. Isomorphic diagrams have
isomorphic colimit cocones, which gives the asserted universal property. This argument
also applies to the empty family and to a ring with `0 = 1`. -/
theorem derivedShiftedFreeCoproduct (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    (T : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (I : Type (max u v)) (degree : I → ℤ)
    (hT : Nonempty (T ≅ ∐ (fun i : I =>
      (HomologicalComplex.single (ModuleCat.{max u v} R)
        (ComplexShape.up ℤ) (degree i)).obj (ModuleCat.of R (ULift.{v} R))))) :
    ∃ (d : I → ℤ)
      (j : ∀ i : I, (((DerivedCategory.singleFunctor
        (ModuleCat.{max u v} R) 0).obj (ModuleCat.of R (ULift.{v} R)))⟦d i⟧) ⟶
          (DerivedCategory.Q.obj T)⟦(-1 : ℤ)⟧),
      Nonempty (IsColimit (Cofan.mk ((DerivedCategory.Q.obj T)⟦(-1 : ℤ)⟧) j)) := by
  classical
  let C := ModuleCat.{max u v} R
  let D := DerivedCategory C
  let A := ModuleCat.of R (ULift.{v} R)
  let B (i : I) := (HomologicalComplex.single C (ComplexShape.up ℤ) (degree i)).obj A
  let s := shiftFunctor D (-1 : ℤ)
  let j₀ (i : I) := DerivedCategory.Q.map (Sigma.ι B i)
  have h₀ : IsColimit (Cofan.mk (DerivedCategory.Q.obj (∐ B)) j₀) :=
    (derivedModuleDirectSums R I B).some
  have hs : IsColimit (Cofan.mk (s.obj (DerivedCategory.Q.obj (∐ B)))
      (fun i ↦ s.map (j₀ i))) :=
    Cofan.isColimitMapCoconeEquiv s _ _ (isColimitOfPreserves s h₀)
  let e := s.mapIso (DerivedCategory.Q.mapIso hT.some.symm)
  let d (i : I) := -degree i + (-1)
  let ei (i : I) :
      (((DerivedCategory.singleFunctor C 0).obj A)⟦d i⟧) ≅
        s.obj (DerivedCategory.Q.obj (B i)) :=
    (shiftFunctorAdd D (-degree i) (-1 : ℤ)).app _ ≪≫
      s.mapIso (((DerivedCategory.singleFunctors C).shiftIso
        (-degree i) (degree i) 0 (by omega)).app A)
  let j (i : I) := (ei i).hom ≫ s.map (j₀ i) ≫ e.hom
  refine ⟨d, j, ⟨Cofan.IsColimit.mk _ (fun t ↦
    e.inv ≫ hs.desc (Cofan.mk t.pt (fun i ↦ (ei i).inv ≫ t.inj i))) ?_ ?_⟩⟩
  · intro t i
    dsimp [j]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    have hf : s.map (j₀ i) ≫
        hs.desc (Cofan.mk t.pt (fun i ↦ (ei i).inv ≫ t.inj i)) =
          (ei i).inv ≫ t.inj i := hs.fac _ ⟨i⟩
    rw [hf]
    simp
  · intro t m hm
    apply (cancel_epi e.hom).1
    simp only [Iso.hom_inv_id_assoc]
    apply hs.hom_ext
    rintro ⟨i⟩
    apply (cancel_epi (ei i).hom).1
    have hf : s.map (j₀ i) ≫
        hs.desc (Cofan.mk t.pt (fun i ↦ (ei i).inv ≫ t.inj i)) =
          (ei i).inv ≫ t.inj i := hs.fac _ ⟨i⟩
    change (ei i).hom ≫ s.map (j₀ i) ≫ e.hom ≫ m = _
    simp only [Cofan.mk_ι_app]
    rw [hf, Iso.hom_inv_id_assoc]
    simpa only [cofan_mk_inj, j, Category.assoc] using hm i


end CategoryTheory
