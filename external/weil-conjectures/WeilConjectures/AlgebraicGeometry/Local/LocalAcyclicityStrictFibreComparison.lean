/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Local.LocalAcyclicityAbelianSheaf
import WeilConjectures.AlgebraicGeometry.Strict.StrictBaseClosedPointLocalizations

/-! # Comparing the strict-local fibre above a closed geometric point

## References

* Stacks Project, Tag 0GJU, first two paragraphs of the proof
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

private theorem strictMap_structural
    {X S : Scheme.{u}} (f : X ⟶ S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) :
    localAcyclicityStrictMap f x ≫ Scheme.strictHenselizationStructuralMap (x ≫ f) =
      Scheme.strictHenselizationStructuralMap x ≫ f :=
  (existsUnique_localAcyclicityStrictMap f x).choose_spec.1.1

private theorem strictMap_point
    {X S : Scheme.{u}} (f : X ⟶ S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) :
    Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationRingPointEvaluation x)) ≫
        localAcyclicityStrictMap f x =
      Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationRingPointEvaluation (x ≫ f))) :=
  (existsUnique_localAcyclicityStrictMap f x).choose_spec.1.2

private theorem strict_congr_structural
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {x y : Spec (.of Ω) ⟶ S} (h : x = y) :
    eqToHom (congrArg Scheme.strictHenselizationScheme h) ≫
        Scheme.strictHenselizationStructuralMap y =
      Scheme.strictHenselizationStructuralMap x := by
  subst y
  simp

private theorem strict_congr_point
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {x y : Spec (.of Ω) ⟶ S} (h : x = y) :
    Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationRingPointEvaluation x)) ≫
        eqToHom (congrArg Scheme.strictHenselizationScheme h) =
      Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationRingPointEvaluation y)) := by
  subst y
  simp

/-- The strict-local fibre over a closed point of the strict-base change is a variety
of vanishing cycles for the original morphism, compatibly with its map to the original
scheme. The canonical map on the strict localization of the source is invertible.
The fibre comparison commutes with its first projection. -/
theorem localAcyclicity_strict_fibre_comparison
    {X S X' : Scheme.{u}} (f : X ⟶ S)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (p : X' ⟶ X) (f' : X' ⟶ Scheme.strictHenselizationScheme s)
    (hcart : IsPullback p f' f (Scheme.strictHenselizationStructuralMap s))
    {Ξ : Type u} [Field Ξ] [IsAlgClosed Ξ] (x' : Spec (.of Ξ) ⟶ X')
    (a : Spec (.of Ξ) ⟶ Spec (.of Ω))
    (hclosed : x' ≫ f' =
      a ≫ Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationRingPointEvaluation s)))
    {Ω' : Type u} [Field Ω'] [IsAlgClosed Ω']
    (t : Spec (.of Ω') ⟶ Scheme.strictHenselizationScheme s) :
    IsIso (localAcyclicityStrictMap p x') ∧
    ∃ e : Scheme.strictHenselizationScheme s ≅
        Scheme.strictHenselizationScheme ((x' ≫ p) ≫ f),
      ∃ E : pullback (Scheme.strictHenselizationStructuralMap x' ≫ f') t ≅
          localAcyclicityFiber f (x' ≫ p) (t ≫ e.hom),
        E.hom ≫ pullback.fst (localAcyclicityStrictMap f (x' ≫ p)) (t ≫ e.hom) =
          pullback.fst (Scheme.strictHenselizationStructuralMap x' ≫ f') t ≫
            localAcyclicityStrictMap p x' ∧
        E.hom ≫ pullback.fst (localAcyclicityStrictMap f (x' ≫ p)) (t ≫ e.hom) ≫
            Scheme.strictHenselizationStructuralMap (x' ≫ p) =
          pullback.fst (Scheme.strictHenselizationStructuralMap x' ≫ f') t ≫
            Scheme.strictHenselizationStructuralMap x' ≫ p := by
  have hpoint : (x' ≫ f') ≫ Scheme.strictHenselizationStructuralMap s =
      (x' ≫ p) ≫ f := by
    simpa only [Category.assoc] using congrArg (fun m ↦ x' ≫ m) hcart.w.symm
  let b := localAcyclicityStrictMap (Scheme.strictHenselizationStructuralMap s) (x' ≫ f') ≫
    eqToHom (congrArg Scheme.strictHenselizationScheme hpoint)
  have hb : b ≫ Scheme.strictHenselizationStructuralMap ((x' ≫ p) ≫ f) =
      Scheme.strictHenselizationStructuralMap (x' ≫ f') ≫
        Scheme.strictHenselizationStructuralMap s := by
    dsimp only [b]
    rw [Category.assoc, strict_congr_structural hpoint, strictMap_structural]
  have hbpoint : Spec.map (CommRingCat.ofHom
        (Scheme.strictHenselizationRingPointEvaluation (x' ≫ f'))) ≫ b =
      Spec.map (CommRingCat.ofHom
        (Scheme.strictHenselizationRingPointEvaluation ((x' ≫ p) ≫ f))) := by
    dsimp only [b]
    rw [← Category.assoc, strictMap_point, strict_congr_point hpoint]
  obtain ⟨_, hq, e, _, _, hE⟩ := Scheme.strictBaseClosedPointLocalizations f s p f' hcart
    x' a hclosed b hb hbpoint (localAcyclicityStrictMap f (x' ≫ p))
    (strictMap_structural f (x' ≫ p)) (strictMap_point f (x' ≫ p))
    (localAcyclicityStrictMap p x') (strictMap_structural p x') (strictMap_point p x')
  obtain ⟨E, hE, _⟩ := hE Ω' t
  refine ⟨hq, e, E, hE, ?_⟩
  rw [← Category.assoc, hE, Category.assoc, strictMap_structural]

end AlgebraicGeometry.Etale
