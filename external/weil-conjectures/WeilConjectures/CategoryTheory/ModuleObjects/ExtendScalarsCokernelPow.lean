/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import WeilConjectures.CategoryTheory.ModuleObjects.FreeCokernelPowTower

/-!
# Free modules, extension of scalars and reduction modulo an integer

Let `C` be a monoidal category and `φ : R ⟶ S` a morphism of commutative monoid objects.

* The free module functors and extension of scalars commute:
  `Mod.freeFunctor R ⋙ Mod.extendScalars φ ≅ Mod.freeFunctor S`
  (`CategoryTheory.Mod.freeFunctorCompExtendScalarsIso`), both functors being left adjoint to the
  forgetful functor `Mod C S ⥤ C`.
* If `k : S ⟶ S` vanishes, so does `k` on every `S`-module
  (`CategoryTheory.Mod.zsmul_id_eq_zero_of_zsmul_id_eq_zero`).
* An additive functor `F` preserving cokernels sends a cokernel of `k` to an isomorphism as soon
  as `k` vanishes on the image (`CategoryTheory.Functor.isIso_map_of_isColimit_cokernelCofork`).
  Hence the reductions `S ⟶ S ⊗ 𝟙/ℓⁿ` of the regular module become isomorphisms after any such
  functor killing `ℓⁿ`, e.g. extension of scalars to a ring killed by `ℓⁿ`
  (`CategoryTheory.Mod.isIso_map_freeCokernelPowTowerCone_π`).
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj Limits Opposite

namespace CategoryTheory.Functor

variable {A : Type*} [Category A] [Preadditive A] {D : Type*} [Category D] [Preadditive D]
  (F : A ⥤ D) [F.Additive]

/-- An additive functor preserving the cokernel `p` of `k : M ⟶ M` sends `p` to an isomorphism
as soon as `k` vanishes on `F M`. -/
lemma isIso_map_of_isColimit_cokernelCofork {M N : A} (p : M ⟶ N) (k : ℤ)
    (w : (k • 𝟙 M) ≫ p = 0) (hp : IsColimit (CokernelCofork.ofπ p w))
    [PreservesColimit (parallelPair (k • 𝟙 M) 0) F] (hk : k • 𝟙 (F.obj M) = 0) :
    IsIso (F.map p) :=
  isIso_colimit_cocone_parallelPair_of_eq (by rw [F.map_zsmul, F.map_id, hk, F.map_zero])
    (isColimitCoforkMapOfIsColimit F _ hp)

end CategoryTheory.Functor

namespace CategoryTheory.Mod

section FreeFunctor

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] (φ : R ⟶ S) [IsMonHom φ]

/-- **Extension of scalars of a free module is free**: `S ⊗_R (R ⊗ X) ≅ S ⊗ X`, both functors
being left adjoint to the forgetful functor `Mod C S ⥤ C`. -/
noncomputable def freeFunctorCompExtendScalarsIso :
    freeFunctor R ⋙ extendScalars φ ≅ freeFunctor S :=
  ((freeForgetAdjunction R).comp (extendRestrictAdjunction φ)).leftAdjointUniq
    ((freeForgetAdjunction S).ofNatIsoRight (Iso.refl _))

end FreeFunctor

section Torsion

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C]
  [MonoidalPreadditive C] {S : C} [MonObj S]

/-- If the integer `k` vanishes on the monoid object `S`, it vanishes on every `S`-module. -/
lemma zsmul_id_eq_zero_of_zsmul_id_eq_zero {k : ℤ} (hk : k • 𝟙 S = 0) (N : Mod C S) :
    k • 𝟙 N = 0 := by
  refine Mod.hom_ext _ _ ?_
  have h : k • 𝟙 N.X = (λ_ N.X).inv ≫ η[S] ▷ N.X ≫ (k • 𝟙 S) ▷ N.X ≫ γ[S, N.X] := by
    simp only [zsmul_whiskerRight, id_whiskerRight, Preadditive.zsmul_comp,
      Preadditive.comp_zsmul, Category.id_comp, one_act, Iso.inv_hom_id]
  rw [hk, MonoidalPreadditive.zero_whiskerRight, Limits.zero_comp, Limits.comp_zero,
    Limits.comp_zero] at h
  rw [zsmul_hom, id_hom', zero_hom]
  exact h

end Torsion

section CokernelPow

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C] [MonoidalPreadditive C]
  (S : C) [MonObj S] [PreservesFiniteColimits (tensorLeft S)]

/-- A morphism of `S`-modules whose underlying morphism is a cokernel of `k` in `C` is a cokernel
of `k` in `Mod C S`. -/
noncomputable def isColimitCokernelCoforkOfForget {M N : Mod C S} (p : M ⟶ N) (k : ℤ)
    (w : (k • 𝟙 M) ≫ p = 0) (hp : IsColimit (CokernelCofork.ofπ (f := k • 𝟙 M.X) p.hom
      (congrArg Mod.Hom.hom w))) :
    IsColimit (CokernelCofork.ofπ p w) :=
  isColimitOfReflects (forget S) ((isColimitMapCoconeCoforkEquiv' (forget S) w).symm hp)

omit [PreservesFiniteColimits (tensorLeft S)] in
@[reassoc]
lemma zsmul_id_comp_freeCokernelPowTowerCone_π (ℓ n : ℕ) :
    (((ℓ ^ n : ℕ) : ℤ) • 𝟙 (regular S)) ≫ (freeCokernelPowTowerCone S ℓ).π.app (op n) = 0 := by
  have h : (((ℓ ^ n : ℕ) : ℤ) • 𝟙 S) ≫ (ρ_ S).inv ≫
      S ◁ cokernel.π (((ℓ ^ n : ℕ) : ℤ) • 𝟙 (𝟙_ C)) = 0 := by
    rw [← Category.assoc, zsmul_id_comp_rightUnitor_inv, Category.assoc,
      ← MonoidalCategory.whiskerLeft_comp, cokernel.condition,
      MonoidalPreadditive.whiskerLeft_zero, Limits.comp_zero]
  exact Mod.hom_ext _ _ h

/-- The leg `S ⟶ S ⊗ 𝟙/ℓⁿ` of `Mod.freeCokernelPowTowerCone S ℓ` is a cokernel of `ℓⁿ` in the
category of `S`-modules. -/
noncomputable def isColimitCokernelCoforkFreeCokernelPowTowerConeπ (ℓ n : ℕ) :
    IsColimit (CokernelCofork.ofπ (f := ((ℓ ^ n : ℕ) : ℤ) • 𝟙 (regular S))
      ((freeCokernelPowTowerCone S ℓ).π.app (op n))
      (zsmul_id_comp_freeCokernelPowTowerCone_π S ℓ n)) :=
  isColimitCokernelCoforkOfForget S _ _ _
    (isColimitCokernelCoforkFreeCokernelPowTowerCone S ℓ n)

/-- **Reduction modulo `ℓⁿ` of the regular module**: an additive functor out of `S`-modules
preserving cokernels and killing `ℓⁿ` on the image of `S` sends the reduction
`S ⟶ S ⊗ 𝟙/ℓⁿ` to an isomorphism. -/
lemma isIso_map_freeCokernelPowTowerCone_π {D : Type*} [Category D] [Preadditive D]
    (F : Mod C S ⥤ D) [F.Additive] [PreservesColimitsOfShape WalkingParallelPair F] (ℓ n : ℕ)
    (hF : ((ℓ ^ n : ℕ) : ℤ) • 𝟙 (F.obj (regular S)) = 0) :
    IsIso (F.map ((freeCokernelPowTowerCone S ℓ).π.app (op n))) :=
  F.isIso_map_of_isColimit_cokernelCofork _ _ _
    (isColimitCokernelCoforkFreeCokernelPowTowerConeπ S ℓ n) hF

end CokernelPow

end CategoryTheory.Mod
