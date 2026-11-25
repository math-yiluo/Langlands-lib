/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
import WeilConjectures.AlgebraicGeometry.PerfectSupportedStabilizedLift

/-! # Lifting maps from perfect complexes with support

Source: Stacks Project, Derived Categories of Schemes, Tag 09IM, Lemma 36.13.11
(blueprint: lem-sc-perfect-support-map-lift).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem stabilization_split
    {C : Type*} [Category C] [HasZeroMorphisms C] [HasBinaryBiproducts C]
    [HasShift C ℤ] (P E : C) (α : P ⟶ E)
    (S : ℕ → C) (e0 : S 0 ≅ P)
    (e : ∀ k : ℕ, S (k + 1) ≅ S k ⊞ (S k)⟦(1 : ℤ)⟧)
    (a : ∀ k : ℕ, S k ⟶ E)
    (ha0 : a 0 = e0.hom ≫ α)
    (ha : ∀ k : ℕ, a (k + 1) = (e k).hom ≫ biprod.fst ≫ a k)
    (n : ℕ) : ∃ (i : P ⟶ S n) (p : S n ⟶ P),
      i ≫ p = 𝟙 P ∧ i ≫ a n = α := by
  induction n with
  | zero =>
    refine ⟨e0.inv, e0.hom, e0.inv_hom_id, ?_⟩
    simp [ha0]
  | succ k ih =>
    obtain ⟨i, p, hip, hia⟩ := ih
    refine ⟨i ≫ biprod.inl ≫ (e k).inv, (e k).hom ≫ biprod.fst ≫ p, ?_, ?_⟩
    · simpa only [Category.assoc, Iso.inv_hom_id_assoc, biprod.inl_fst_assoc] using hip
    · rw [ha]
      simpa only [Category.assoc, Iso.inv_hom_id_assoc, biprod.inl_fst_assoc] using hia

set_option backward.isDefEq.respectTransparency false in
/-- A map from a perfect complex on a quasi-compact open extends as a direct summand
of a map from a global perfect complex with the prescribed closed support.
Support is expressed by vanishing of every cohomology stalk off the closed subset.
Restriction uses the canonical equivalence from the localized site to the open subscheme.
Source: Stacks Project, Derived Categories of Schemes, Tag 09IM, Lemma 36.13.11
(blueprint: lem-sc-perfect-support-map-lift).

Proof:
1. Cover X by U and finitely many affine opens. Induction reduces to X = U ∪ V
   with V affine; the intersections remain quasi-compact by quasi-separatedness.
2. Apply lem-sc-affine-perfect-support-extension on V to extend the restriction of P
   to a perfect Q supported on T ∩ V, whose restriction is (P ⊕ P[1])|_(U ∩ V).
3. Compose with projection to P and alpha. By lem-sc-affine-perfect-map-lift, replace
   Q by Q tensor^L I, retaining perfectness and support, to lift this map to E|_V.
   The replacement map is an isomorphism on the overlap.
4. Apply lem-sc-derived-open-gluing to this map on V and alpha composed with the
   projection P ⊕ P[1] → P on U, using the overlap isomorphism and its compatibility.
   The resulting map beta : R → E has R perfect and supported on T, since these
   conditions are local on U ∪ V. Inclusion and projection on P ⊕ P[1] exhibit the
   required compatible direct summand on U. -/
theorem exists_perfect_supported_map_lift
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (U : X.Opens) (hU : IsCompact (U : Set X))
    (T : Set X) (hT : IsClosed T) (hTc : IsCompact Tᶜ)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [∀ V : U.toScheme.Opens,
      HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))]
    (E : schemeDerivedQCohCategory X)
    (P : schemeDerivedCategory U.toScheme) (hP : IsPerfect U.toScheme P)
    (hPT : ∀ (n : ℤ) (x : U.toScheme), x.val ∉ T →
      Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) n).obj P).val.presheaf x)))
    (α : P ⟶ ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
        (Modules.overEquiv U)).mapDerivedCategory.obj E.obj) :
    ∃ (R : schemeDerivedCategory X) (β : R ⟶ E.obj),
      IsPerfect X R ∧
      (∀ (n : ℤ) (x : X), x ∉ T →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj R).val.presheaf x))) ∧
      ∃ (ι : P ⟶ ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory.obj R)
        (π : ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory.obj R ⟶ P),
        ι ≫ π = 𝟙 P ∧ ι ≫ ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory.map β = α :=
  by
    let F := ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
      Equivalence.functor
          (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
          (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
          (Modules.overEquiv U)).mapDerivedCategory
    let S : ℕ → schemeDerivedCategory.{u, w} U.toScheme :=
      Nat.rec P (fun _ Q ↦ Q ⊞ Q⟦(1 : ℤ)⟧)
    let a : ∀ n : ℕ, S n ⟶ F.obj E.obj :=
      Nat.rec α (fun _ f ↦ biprod.fst ≫ f)
    obtain ⟨n, R, β, hR, hRT, e, he⟩ :=
      exists_perfect_supported_stabilized_lift X U hU T hT hTc E S
        (fun _ ↦ Iso.refl _) hP hPT a (fun _ ↦ by simp [a, S])
    obtain ⟨i, p, hip, hia⟩ := stabilization_split P (F.obj E.obj) α S
      (Iso.refl _) (fun _ ↦ Iso.refl _) a (by simp [a]) (fun _ ↦ by simp [a, S]) n
    refine ⟨R, β, hR, hRT, i ≫ e.inv, e.hom ≫ p, ?_, ?_⟩
    · simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hip
    · change (i ≫ e.inv) ≫ F.map β = α
      rw [he]
      simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hia

end AlgebraicGeometry.Scheme
