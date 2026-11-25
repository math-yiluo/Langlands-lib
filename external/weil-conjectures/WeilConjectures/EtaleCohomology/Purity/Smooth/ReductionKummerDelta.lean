/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.CategoryTheory.Shift.Adjunction

/-!
# Left adjoints of exact functors on derived categories and connecting morphisms

Let `G : D ⥤ C` be an exact functor between abelian categories and `Ψ ⊣ G.mapDerivedCategory` a
left adjoint of the induced functor on the derived categories, compatible with the shifts. The
left adjoint `Ψ` need not be exact (for instance the derived extension of scalars along a ring
morphism, left adjoint to the restriction of scalars), but it is still compatible with the
connecting morphisms of short exact sequences, in the following sense. Let `S` be a short exact
sequence in `C`, `S'` one in `D`, and `φ : S ⟶ G S'` a morphism of short complexes. The
components of `φ` placed in degree zero have transposes `e_k : Ψ(S_k[0]) ⟶ S'_k[0]` under the
adjunction, and the square

```
Ψ(S₃[0]) ──Ψ δ──▶ Ψ(S₁[0][1]) ≅ Ψ(S₁[0])[1]
    │ e₃                    │ e₁[1]
    ▼                       ▼
 S'₃[0] ──────δ'────▶ S'₁[0][1]
```

commutes (`CategoryTheory.ShortComplex.ShortExact.map_singleδ_comp_adjunction`). Indeed, the
transposes of both sides are `δ ≫ φ₁[0][1]` and `φ₃[0] ≫ δ_{G S'}`, since `G` is exact.

For the reduction of coefficients `Λ ⟶ Λ'` this compares the Kummer classes over `Λ` and `Λ'`
through the morphism of Kummer sequences given by the power map `μ_{ℓⁿ⁺¹} ⟶ μ_{ℓⁿ}`.
-/

@[expose] public section

universe w w' v v' u u'

open CategoryTheory Limits DerivedCategory

namespace CategoryTheory.ShortComplex.ShortExact

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
  (G : D ⥤ C) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  {Ψ : DerivedCategory C ⥤ DerivedCategory D} (adj : Ψ ⊣ G.mapDerivedCategory)

/-- The transpose `Ψ(X[0]) ⟶ X'[0]`, under `Ψ ⊣ G.mapDerivedCategory`, of a morphism
`X ⟶ G X'` placed in degree zero. -/
noncomputable def singleTranspose {X : C} {X' : D} (f : X ⟶ G.obj X') :
    Ψ.obj ((singleFunctor C 0).obj X) ⟶ (singleFunctor D 0).obj X' :=
  (adj.homEquiv _ _).symm
    ((singleFunctor C 0).map f ≫ (G.mapDerivedCategorySingleFunctor 0).inv.app X')

/-- The defining property of `singleTranspose`: its transpose is `f[0]`. -/
@[reassoc]
lemma unit_app_comp_map_singleTranspose {X : C} {X' : D} (f : X ⟶ G.obj X') :
    adj.unit.app _ ≫ G.mapDerivedCategory.map (singleTranspose G adj f) =
      (singleFunctor C 0).map f ≫ (G.mapDerivedCategorySingleFunctor 0).inv.app X' := by
  have h := (adj.homEquiv _ _).apply_symm_apply
    ((singleFunctor C 0).map f ≫ (G.mapDerivedCategorySingleFunctor 0).inv.app X')
  rwa [Adjunction.homEquiv_unit] at h

/-- **A left adjoint of an exact functor on derived categories commutes with the connecting
morphisms**: for short exact sequences `S` in `C`, `S'` in `D` and a morphism `φ : S ⟶ G S'`,
`Ψ δ_S` followed by the transpose of `φ₁` is the transpose of `φ₃` followed by `δ_{S'}`. -/
lemma map_singleδ_comp_adjunction [Ψ.CommShift ℤ] [adj.CommShift ℤ] {S : ShortComplex C}
    (hS : S.ShortExact) {S' : ShortComplex D} (hS' : S'.ShortExact)
    (φ : S ⟶ G.mapShortComplex.obj S') :
    Ψ.map hS.singleδ ≫ (Ψ.commShiftIso (1 : ℤ)).hom.app _ ≫
        (singleTranspose G adj φ.τ₁)⟦(1 : ℤ)⟧' =
      singleTranspose G adj φ.τ₃ ≫ hS'.singleδ := by
  apply (adj.homEquiv _ _).injective
  have hu := adj.shift_unit_app (1 : ℤ) ((singleFunctor C 0).obj S.X₁)
  have hn := adj.unit.naturality hS.singleδ
  have hc : (G.mapDerivedCategory.commShiftIso (1 : ℤ)).inv.app
      (Ψ.obj ((singleFunctor C 0).obj S.X₁)) ≫
        G.mapDerivedCategory.map ((singleTranspose G adj φ.τ₁)⟦(1 : ℤ)⟧') =
      (G.mapDerivedCategory.map (singleTranspose G adj φ.τ₁))⟦(1 : ℤ)⟧' ≫
        (G.mapDerivedCategory.commShiftIso (1 : ℤ)).inv.app _ :=
    ((G.mapDerivedCategory.commShiftIso (1 : ℤ)).inv.naturality _).symm
  have hδ := hS'.mapShiftedHom_singleδ G
  have hm := (singleTriangle.map hS (hS'.map_of_exact G) φ).comm₃
  have ht := unit_app_comp_map_singleTranspose G adj φ.τ₁
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [reassoc_of% unit_app_comp_map_singleTranspose, ← reassoc_of% hn]
  have hu' : adj.unit.app (((singleFunctor C 0).obj S.X₁)⟦(1 : ℤ)⟧) ≫
      G.mapDerivedCategory.map ((Ψ.commShiftIso (1 : ℤ)).hom.app _) =
        (adj.unit.app ((singleFunctor C 0).obj S.X₁))⟦(1 : ℤ)⟧' ≫
          (G.mapDerivedCategory.commShiftIso (1 : ℤ)).inv.app
            (Ψ.obj ((singleFunctor C 0).obj S.X₁)) := by
    rw [hu]
    simp
  have hδ' : G.mapDerivedCategory.map hS'.singleδ =
      (G.mapDerivedCategorySingleFunctor 0).hom.app S'.X₃ ≫ (hS'.map_of_exact G).singleδ ≫
        ((G.mapDerivedCategorySingleFunctor 0).inv.app S'.X₁)⟦(1 : ℤ)⟧' ≫
          (G.mapDerivedCategory.commShiftIso (1 : ℤ)).inv.app _ := by
    rw [← cancel_mono ((G.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app _)]
    simp only [ShiftedHom.map] at hδ
    rw [hδ]
    simp
  simp only [singleTriangle_mor₃, singleTriangle.map_hom₁, singleTriangle.map_hom₃] at hm
  rw [reassoc_of% hu', hc, ← Functor.map_comp_assoc, ht, hδ', Iso.inv_hom_id_app_assoc,
    Functor.map_comp_assoc]
  exact (reassoc_of% hm) _

end CategoryTheory.ShortComplex.ShortExact
