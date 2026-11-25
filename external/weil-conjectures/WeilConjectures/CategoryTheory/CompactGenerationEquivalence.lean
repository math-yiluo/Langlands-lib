/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.CompactlyGenerated
public import Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-!
# Compact generation is preserved by triangulated equivalences

Source: Stacks Project, Derived Categories, Tags 09SM, 09SJ and 09SQ.
-/

@[expose] public section

universe w u₁ u₂ v₁ v₂

namespace CategoryTheory

open Limits

/-- An additive equivalence compatible with shifts preserves compact generation.
Source: Stacks Project, Derived Categories, Definition 13.37.1 (Tag 09SM),
Definition 13.36.3 (Tag 09SJ) and Definition 13.37.5 (Tag 09SQ)
(blueprint: lem-pc-compact-generation-equivalence).

Proof: Choose the original compact generating family and map it by e.functor.
For a family in D, use e.inverse to pull it back to C. The additive Hom equivalences
and the canonical isomorphism identifying a preserved coproduct identify the canonical
map from the direct sum of Hom groups with the original one. This proves compactness
of each image generator. The coproduct of the images is isomorphic to the image of
the original coproduct. Given a nonzero K in D, its inverse image is nonzero, since an
equivalence preserves and reflects zero objects. The original generator therefore
has a nonzero map to a shift of that inverse image. Apply e.functor, then compose
with its shift comparison and counit to obtain a nonzero map to the corresponding
shift of K. Faithfulness and the invertibility of the comparison maps preserve
nonvanishing. This proves the generator condition, including an empty indexing type:
the argument uses only the generator assumption and never chooses an index. -/
theorem compactGenerationEquivalence
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [HasZeroObject C] [HasZeroObject D] [HasShift C ℤ] [HasShift D ℤ]
    [Preadditive C] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D] [IsTriangulated C] [IsTriangulated D]
    [HasCoproducts.{w} C] [HasCoproducts.{w} D]
    (e : C ≌ D) [e.functor.Additive] [e.inverse.Additive] [e.functor.CommShift ℤ]
    (hC : IsCompactlyGeneratedTriangulated.{w} C) :
    IsCompactlyGeneratedTriangulated.{w} D := by
  classical
  obtain ⟨I, E, hE, hG⟩ := hC
  refine ⟨I, fun i ↦ e.functor.obj (E i), ?_, ?_⟩
  · intro i J T
    let U := fun j ↦ e.inverse.obj (T j)
    let q := PreservesCoproduct.iso e.inverse T
    let L : ∀ j, (e.functor.obj (E i) ⟶ T j) →+ (E i ⟶ U j) := fun j ↦
      (Preadditive.leftComp _ (e.unitIso.hom.app (E i))).comp e.inverse.mapAddHom
    have hL : ∀ j, Function.Bijective (L j) := by
      intro j
      exact (e.toAdjunction.homEquiv (E i) (T j)).bijective
    let B : (e.functor.obj (E i) ⟶ ∐ T) →+ (E i ⟶ ∐ U) :=
      (Preadditive.rightComp _ q.hom).comp
        ((Preadditive.leftComp _ (e.unitIso.hom.app (E i))).comp e.inverse.mapAddHom)
    have hB : Function.Bijective B := by
      exact q.homToEquiv.bijective.comp
        (e.toAdjunction.homEquiv (E i) (∐ T)).bijective
    have hS : Function.Bijective (DirectSum.map L) :=
      ⟨(DirectSum.map_injective L).2 (fun j ↦ (hL j).1),
        (DirectSum.map_surjective L).2 (fun j ↦ (hL j).2)⟩
    let a := DirectSum.toAddMonoid
      (fun j ↦ Preadditive.rightComp (e.functor.obj (E i)) (Sigma.ι T j))
    let b := DirectSum.toAddMonoid
      (fun j ↦ Preadditive.rightComp (E i) (Sigma.ι U j))
    have hb : Function.Bijective b := hE i J U
    have hi (j : J) : e.inverse.map (Sigma.ι T j) ≫ q.hom = Sigma.ι U j := by
      apply (cancel_mono q.inv).mp
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      dsimp [q]
      exact (ι_comp_sigmaComparison e.inverse T j).symm
    have square : B.comp a = b.comp (DirectSum.map L) := by
      apply DirectSum.addHom_ext
      intro j f
      simp only [AddMonoidHom.comp_apply, DirectSum.map_of]
      dsimp [a, b]
      rw [DirectSum.toAddMonoid_of, DirectSum.toAddMonoid_of]
      change (e.unitIso.hom.app (E i) ≫ e.inverse.map (f ≫ Sigma.ι T j)) ≫ q.hom =
        (e.unitIso.hom.app (E i) ≫ e.inverse.map f) ≫ Sigma.ι U j
      simp only [Functor.map_comp, Category.assoc, hi]
    have hs : Function.Bijective (B ∘ a) := by
      change Function.Bijective (B.comp a)
      rw [square]
      exact hb.comp hS
    exact (Function.Bijective.of_comp_iff' hB a).mp hs
  · intro K hK
    have hn : ¬ IsZero (e.inverse.obj K) := by
      intro hz
      exact hK ((Functor.map_isZero e.functor hz).of_iso (e.counitIso.app K).symm)
    obtain ⟨n, f, hf⟩ := hG (e.inverse.obj K) hn
    let q := PreservesCoproduct.iso e.functor E
    let r : e.functor.obj ((e.inverse.obj K)⟦n⟧) ≅ K⟦n⟧ :=
      (e.functor.commShiftIso n).app _ ≪≫
        (shiftFunctor D n).mapIso (e.counitIso.app K)
    refine ⟨n, q.inv ≫ e.functor.map f ≫ r.hom, ?_⟩
    intro h
    have hm : e.functor.map f = 0 := by
      apply (cancel_epi q.inv).mp
      apply (cancel_mono r.hom).mp
      simpa using h
    exact hf ((Functor.map_eq_zero_iff e.functor).mp hm)

end CategoryTheory
