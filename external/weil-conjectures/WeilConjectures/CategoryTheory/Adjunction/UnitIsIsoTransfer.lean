/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ExchangeRightPaste
public import WeilConjectures.CategoryTheory.Adjunction.MateUnitIsIso

/-!
# Transferring the invertibility of units of adjunctions

Two ways of comparing the units of two adjunctions `L₁ ⊣ R₁` and `L₂ ⊣ R₂`:

* along a square of left adjoints `α : G ⋙ L₂ ⟶ L₁ ⋙ H` whose mate `β` is invertible (a base
  change morphism): `G (η₁ c)` is invertible if and only if `η₂ (G c)` is
  (`CategoryTheory.Adjunction.isIso_map_unit_app_iff_of_isIso_mateEquiv_app`, and its form
  `CategoryTheory.Adjunction.isIso_map_unit_app_iff_of_isIso_exchangeRight_app` for exchange
  morphisms). In algebraic geometry: the unit of `Lπ^* ⊣ Rπ_*` is compatible with base change,
  and the unit of `Lπ^* ⊣ Rπ_*` is the base change morphism of the square with sides `π`, `π`, `𝟙`,
  `𝟙`;
* along fully faithful comparison functors `A`, `B` with `F ⋙ B ≅ A ⋙ F'`: the invertibility of
  a unit only depends on the left adjoint, being the bijectivity of the left adjoint on morphisms
  into the object (`CategoryTheory.Adjunction.isIso_unit_app_of_isIso_unit_app_obj`). No
  compatibility of the right adjoints is needed.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

variable {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']

/-- Let `α : G ⋙ L₂ ⟶ L₁ ⋙ H` be a square of left adjoints `L₁ ⊣ R₁`, `L₂ ⊣ R₂`, invertible at
`c`, whose mate `β : R₁ ⋙ G ⟶ H ⋙ R₂` is invertible at `L₁ c`. Then `G` of the unit of
`L₁ ⊣ R₁` at `c` is invertible if and only if the unit of `L₂ ⊣ R₂` at `G c` is: by
`CategoryTheory.unit_mateEquiv`, `G (η₁ c) ≫ β (L₁ c) = η₂ (G c) ≫ R₂ (α c)`. -/
lemma isIso_map_unit_app_iff_of_isIso_mateEquiv_app {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : C' ⥤ D'}
    {R₂ : D' ⥤ C'} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) {G : C ⥤ C'} {H : D ⥤ D'}
    (α : TwoSquare G L₁ L₂ H) (c : C) [IsIso (α.app c)]
    [IsIso ((mateEquiv adj₁ adj₂ α).app (L₁.obj c))] :
    IsIso (G.map (adj₁.unit.app c)) ↔ IsIso (adj₂.unit.app (G.obj c)) := by
  have h := unit_mateEquiv adj₁ adj₂ α c
  refine ⟨fun _ ↦ ?_, fun _ ↦ ?_⟩
  · have : IsIso (adj₂.unit.app (G.obj c) ≫ R₂.map (α.app c)) := by
      erw [← h]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (R₂.map (α.app c))
  · have h' : IsIso (adj₂.unit.app (G.obj c) ≫ R₂.map (α.app c)) := inferInstance
    have : IsIso (G.map (adj₁.unit.app c) ≫ (mateEquiv adj₁ adj₂ α).app (L₁.obj c)) := by
      erw [h]
      exact h'
    exact IsIso.of_isIso_comp_right _ ((mateEquiv adj₁ adj₂ α).app (L₁.obj c))

/-- Conversely to `CategoryTheory.Adjunction.isIso_map_unit_app_iff_of_isIso_mateEquiv_app`: if
`α` is invertible at `c` and both `G (η₁ c)` and `η₂ (G c)` are invertible, then the mate `β` of
`α` is invertible at `L₁ c`. -/
lemma isIso_mateEquiv_app_of_isIso_unit_app {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : C' ⥤ D'}
    {R₂ : D' ⥤ C'} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) {G : C ⥤ C'} {H : D ⥤ D'}
    (α : TwoSquare G L₁ L₂ H) (c : C) [IsIso (α.app c)] [IsIso (G.map (adj₁.unit.app c))]
    [IsIso (adj₂.unit.app (G.obj c))] :
    IsIso ((mateEquiv adj₁ adj₂ α).app (L₁.obj c)) := by
  have h := unit_mateEquiv adj₁ adj₂ α c
  have h' : IsIso (adj₂.unit.app (G.obj c) ≫ R₂.map (α.app c)) := inferInstance
  have : IsIso (G.map (adj₁.unit.app c) ≫ (mateEquiv adj₁ adj₂ α).app (L₁.obj c)) := by
    erw [h]
    exact h'
  exact IsIso.of_isIso_comp_left (G.map (adj₁.unit.app c)) _

/-- The exchange morphism form of
`CategoryTheory.Adjunction.isIso_map_unit_app_iff_of_isIso_mateEquiv_app`: for an isomorphism
`θ : G ⋙ Lf' ≅ Lf ⋙ G'` of left adjoints whose exchange morphism is invertible at `Lf M`, `G` of
the unit of `Lf ⊣ Rf` at `M` is invertible if and only if the unit of `Lf' ⊣ Rf'` at `G M` is. -/
lemma isIso_map_unit_app_iff_of_isIso_exchangeRight_app {Lf : C ⥤ D} {Rf : D ⥤ C}
    {Lf' : C' ⥤ D'} {Rf' : D' ⥤ C'} {G : C ⥤ C'} {G' : D ⥤ D'} (af : Lf ⊣ Rf) (af' : Lf' ⊣ Rf')
    (θ : G ⋙ Lf' ≅ Lf ⋙ G') (M : C) [IsIso ((exchangeRight af af' θ).app (Lf.obj M))] :
    IsIso (G.map (af.unit.app M)) ↔ IsIso (af'.unit.app (G.obj M)) := by
  rw [exchangeRight_eq_mateEquiv] at *
  exact isIso_map_unit_app_iff_of_isIso_mateEquiv_app af af' (TwoSquare.mk _ _ _ _ θ.hom) M

/-- **Units along fully faithful comparison functors.** Let `F ⊣ G` and `F' ⊣ G'` be adjunctions,
and `A`, `B` fully faithful functors with `F ⋙ B ≅ A ⋙ F'`. If the unit of `F' ⊣ G'` is invertible
at `A K`, then the unit of `F ⊣ G` is invertible at `K`: `F'` is bijective on morphisms into
`A K`, hence, through `A` and `B`, `F` is bijective on morphisms into `K`. -/
lemma isIso_unit_app_of_isIso_unit_app_obj {F : C ⥤ D} {G : D ⥤ C} {F' : C' ⥤ D'}
    {G' : D' ⥤ C'} (adj : F ⊣ G) (adj' : F' ⊣ G') (A : C ⥤ C') (B : D ⥤ D') [A.Full] [A.Faithful]
    [B.Full] [B.Faithful] (e : F ⋙ B ≅ A ⋙ F') (K : C) [IsIso (adj'.unit.app (A.obj K))] :
    IsIso (adj.unit.app K) := by
  refine adj.isIso_unit_app_of_map_bijective K fun T ↦ ?_
  have hF' := adj'.map_bijective_of_isIso_unit_app (A.obj T) (B := A.obj K)
  have key : (fun f : T ⟶ K ↦ B.map (F.map f)) =
      (fun g ↦ e.hom.app T ≫ g ≫ e.inv.app K) ∘ (F'.map : (A.obj T ⟶ A.obj K) → _) ∘
        (A.map : (T ⟶ K) → _) := by
    funext f
    have := e.hom.naturality f
    simp only [Functor.comp_obj, Functor.comp_map] at this
    rw [← cancel_mono (e.hom.app K)]
    simp [this]
  have hB : Function.Bijective (fun f : T ⟶ K ↦ B.map (F.map f)) := by
    rw [key]
    have hc : Function.Bijective
        (fun g : F'.obj (A.obj T) ⟶ F'.obj (A.obj K) ↦ e.hom.app T ≫ g ≫ e.inv.app K) :=
      Function.bijective_iff_has_inverse.2
        ⟨fun g ↦ e.inv.app T ≫ g ≫ e.hom.app K, fun g ↦ by simp, fun g ↦ by simp⟩
    exact hc.comp (hF'.comp ((Functor.FullyFaithful.ofFullyFaithful A).map_bijective T K))
  exact (Function.Bijective.of_comp_iff'
    ((Functor.FullyFaithful.ofFullyFaithful B).map_bijective _ _) _).1 hB

end CategoryTheory.Adjunction
