/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Mathlib.Data.Nat.Choose.Basic

/-! # Cancelling the shifted summands of a restricted cone

Source: Stacks Project, Tag 08EK, proof, final paragraph; Derived Categories, Tag 05QT.
(blueprint: lem-sc-affine-binomial-projector-cone).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem exists_projector_triangle (Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {J : Type} [Finite J] (H : J → schemeDerivedCategory Y) (j₀ : J) :
    ∃ (a : ∏ᶜ H ⟶ ∏ᶜ H) (Z : schemeDerivedCategory Y)
      (b : ∏ᶜ H ⟶ Z) (d : Z ⟶ (∏ᶜ H)⟦(1 : ℤ)⟧),
      Triangle.mk a b d ∈ distTriang (schemeDerivedCategory Y) ∧
      Nonempty (Z ≅ H j₀ ⊞ (H j₀)⟦(1 : ℤ)⟧) := by
  classical
  let a : ∀ j, H j ⟶ H j := fun j ↦ if j = j₀ then 0 else 𝟙 _
  have hex (j : J) := distinguished_cocone_triangle (a j)
  choose Z b d h using hex
  let T : J → Triangle (schemeDerivedCategory Y) := fun j ↦ Triangle.mk (a j) (b j) (d j)
  have hT (j : J) : T j ∈ distTriang (schemeDerivedCategory Y) := h j
  have hzero (j : J) (hj : j ≠ j₀) : IsZero (Z j) := by
    apply (T j).isZero₃_of_isIso₁ (hT j)
    dsimp [T, a]
    rw [ite_eq_right hj]
    infer_instance
  let eZ : ∏ᶜ Z ≅ Z j₀ :=
    { hom := Pi.π Z j₀
      inv := Pi.lift (fun j ↦ if hj : j₀ = j then eqToHom (congrArg Z hj) else 0)
      hom_inv_id := by
        apply Pi.hom_ext
        intro j
        by_cases hj : j = j₀
        · subst j
          simp
        · exact (hzero j hj).eq_of_tgt _ _
      inv_hom_id := by simp }
  obtain ⟨e₀, _, _⟩ := exists_iso_binaryBiproduct_of_distTriang (T j₀).rotate
    (rot_of_distTriang _ (hT j₀)) (by simp [T, a])
  let Q := productTriangle T
  exact ⟨Q.mor₁, Q.obj₃, Q.mor₂, Q.mor₃,
    productTriangle_distinguished T hT, ⟨eZ ≪≫ e₀⟩⟩

/-- The binomial sum of shifts of F admits an endomorphism whose lifted cone restricts
to F plus F[1]. This is a cone computation, with no affine, support, or perfectness hypothesis.
Source: Stacks Project, Tag 08EK, proof, final paragraph; Tag 05QT
(blueprint: lem-sc-affine-binomial-projector-cone).

Proof: in the displayed finite biproduct, the degree-zero summand occurs exactly once,
because choose(s+1,0)=1. Define the endomorphism to be zero on this summand and identity
on every other summand, and conjugate by the given restriction isomorphism. Restriction
is an exact additive functor and commutes with shifts. The equation involving bU
identifies the first arrow of the restricted triangle, after changing its source by bU,
with this endomorphism. Split the finite biproduct into the degree-zero summand and
its complement. The direct sum of the cone triangle of zero on F and the contractible
identity triangle on the complement is distinguished. Uniqueness of the third object
of a distinguished triangle with fixed first arrow identifies the restricted cone
with F plus F[1]. For s=0 the complement is F[1]; the same calculation applies. -/
theorem exists_binomial_projector_cone_restrict (X : Scheme.{u}) (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [∀ V : U.toScheme.Opens,
      HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))]
    (s : ℕ) (F : schemeDerivedCategory U.toScheme) (A : schemeDerivedCategory X)
    (e : Nonempty
      (((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
        Equivalence.functor
          (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
          (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
          (Modules.overEquiv U)).mapDerivedCategory.obj A ≅
        biproduct (fun p : (j : Fin (s + 2)) × Fin (Nat.choose (s + 1) j.val) ↦
          F⟦(p.1.val : ℤ)⟧))) :
    ∃ α : ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
        Equivalence.functor
          (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
          (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
          (Modules.overEquiv U)).mapDerivedCategory.obj A ⟶
      ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
        Equivalence.functor
          (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
          (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
          (Modules.overEquiv U)).mapDerivedCategory.obj A,
      ∀ (A' : schemeDerivedCategory X) (γ : A' ⟶ A)
        (bU : ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
        Equivalence.functor
          (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
          (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
          (Modules.overEquiv U)).mapDerivedCategory.obj A' ≅
          ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
        Equivalence.functor
          (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
          (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
          (Modules.overEquiv U)).mapDerivedCategory.obj A),
        α = bU.inv ≫ ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
        Equivalence.functor
          (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
          (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
          (Modules.overEquiv U)).mapDerivedCategory.map γ →
        ∀ (E : schemeDerivedCategory X) (b : A ⟶ E) (d : E ⟶ A'⟦(1 : ℤ)⟧),
          Triangle.mk γ b d ∈ distTriang (schemeDerivedCategory X) →
          Nonempty (((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
        Equivalence.functor
          (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
          (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
          (Modules.overEquiv U)).mapDerivedCategory.obj E ≅ F ⊞ F⟦(1 : ℤ)⟧)  := by
  classical
  let R := ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
    Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Modules.overEquiv U)).mapDerivedCategory
  let J := (j : Fin (s + 2)) × Fin (Nat.choose (s + 1) j.val)
  let H : J → schemeDerivedCategory U.toScheme := fun p ↦ F⟦(p.1.val : ℤ)⟧
  let j₀ : J := ⟨0, ⟨0, by simp⟩⟩
  obtain ⟨a, Z, b, d, hQ, ⟨eZ⟩⟩ := exists_projector_triangle U.toScheme H j₀
  let Q := Triangle.mk a b d
  obtain ⟨e⟩ := e
  let eP : R.obj A ≅ ∏ᶜ H := e ≪≫ biproduct.isoProduct H
  refine ⟨eP.hom ≫ a ≫ eP.inv, ?_⟩
  intro A' γ bU hγ E bE dE htri
  let S := R.mapTriangle.obj (Triangle.mk γ bE dE)
  have hS : S ∈ distTriang (schemeDerivedCategory U.toScheme) :=
    R.map_distinguished _ htri
  have hcomm : S.mor₁ ≫ eP.hom = (bU ≪≫ eP).hom ≫ Q.mor₁ := by
    change R.map γ ≫ eP.hom = (bU.hom ≫ eP.hom) ≫ a
    rw [Category.assoc]
    have hγ' := congrArg (fun k ↦ bU.hom ≫ k ≫ eP.hom) hγ
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id,
      Category.comp_id] using hγ'.symm
  let eTri := isoTriangleOfIso₁₂ S Q hS hQ (bU ≪≫ eP) eP hcomm
  let eF : H j₀ ≅ F := (shiftFunctorZero _ ℤ).app F
  exact ⟨(Triangle.π₃.mapIso eTri) ≪≫ eZ ≪≫
    biprod.mapIso eF ((shiftFunctor _ (1 : ℤ)).mapIso eF)⟩


end AlgebraicGeometry.Scheme
