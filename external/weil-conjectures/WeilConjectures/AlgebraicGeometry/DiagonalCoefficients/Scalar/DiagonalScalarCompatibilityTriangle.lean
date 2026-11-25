/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientScalars
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Scalar.DiagonalScalarRestrictionComposition

/-! # Cancellation of a common scalar route

Source: diagonal coefficient changes, paragraph (2), scalar associativity and
compatibility of the prescribed finite and colimit legs.
(blueprint: lem-diagonal-scalar-compatibility-triangle).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] Functor.leftDerivedFunctor
  Mod.derivedExtendMapDerivedCategoryAdjunction RestrictionSquare.mate scalarCompIso

private theorem triangle_eq_iff
    {C₀ C₁ C₂ : Type*} [Category* C₀] [Category* C₁] [Category* C₂]
    (F : C₀ ⥤ C₁) (G : C₁ ⥤ C₂) (H : C₀ ⥤ C₂) (A : H ≅ F ⋙ G)
    {S₀ T₀ : C₀} {S₁ T₁ : C₁} {S₂ T₂ : C₂}
    (s₀₁ : F.obj S₀ ⟶ S₁) [IsIso s₀₁]
    (s₁₂ : G.obj S₁ ⟶ S₂) (s₀₂ : H.obj S₀ ⟶ S₂)
    (t₀₁ : F.obj T₀ ⟶ T₁) (t₁₂ : G.obj T₁ ⟶ T₂) (t₀₂ : H.obj T₀ ⟶ T₂)
    (hs : s₀₂ = A.hom.app S₀ ≫ G.map s₀₁ ≫ s₁₂)
    (ht : t₀₂ = A.hom.app T₀ ≫ G.map t₀₁ ≫ t₁₂)
    (f₀ : S₀ ⟶ T₀) (f₁ : S₁ ⟶ T₁) (f₂ : S₂ ⟶ T₂)
    (h₀₁ : F.map f₀ ≫ t₀₁ = s₀₁ ≫ f₁) :
    (H.map f₀ ≫ t₀₂ = s₀₂ ≫ f₂) ↔
      (G.map f₁ ≫ t₁₂ = s₁₂ ≫ f₂) := by
  have hpath : H.map f₀ ≫ t₀₂ =
      A.hom.app S₀ ≫ G.map s₀₁ ≫ G.map f₁ ≫ t₁₂ := by
    rw [ht, ← Category.assoc, A.hom.naturality]
    simp only [Functor.comp_map, Category.assoc]
    rw [← G.map_comp_assoc, h₀₁, G.map_comp_assoc]
  rw [hpath, hs]
  simp only [Category.assoc, cancel_epi]

private theorem endpoint_hom {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] {X : Scheme.{u}}
    {M : Modules Λ X} {N : Modules Λ' X} {m : M.X ⟶ N.X}
    (e : Endpoint a M N m) : e.iso.hom = scalarHom a e.semilinear := by
  apply (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X)).homEquiv
    _ _ |>.injective
  rw [e.normalization]
  exact (((Mod.derivedExtendMapDerivedCategoryAdjunction
    (coefficientMap a X)).homEquiv _ _).apply_symm_apply _).symm

private theorem endpoint_shift {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] {X : Scheme.{u}}
    {M : Modules Λ X} {N : Modules Λ' X} {m : M.X ⟶ N.X}
    (e : Endpoint a M N m) : e.shift a = scalarShiftHom a e.semilinear := by
  unfold Endpoint.shift scalarShiftHom
  rw [endpoint_hom a e]

private def endpointOfHom
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] {X : Scheme.{u}}
    {M : Modules Λ X} {N : Modules Λ' X} {m : M.X ⟶ N.X}
    (s : Semilinear a M N m) [IsIso (scalarHom a s)] : Endpoint a M N m where
  semilinear := s
  iso := asIso (scalarHom a s)
  normalization := ((Mod.derivedExtendMapDerivedCategoryAdjunction
    (coefficientMap a X)).homEquiv _ _).apply_symm_apply _

private theorem endpoint_equations
    {Λ₀ Λ₁ Λ₂ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ₀] [IsCommMonObj Λ₀] [MonObj Λ₁] [IsCommMonObj Λ₁]
    [MonObj Λ₂] [IsCommMonObj Λ₂]
    (a : Λ₀ ⟶ Λ₁) (b : Λ₁ ⟶ Λ₂) (c : Λ₀ ⟶ Λ₂)
    [IsMonHom a] [IsMonHom b] [IsMonHom c] (hcoeff : a ≫ b = c)
    {X : Scheme.{u}} {M₀ : Modules Λ₀ X} {M₁ : Modules Λ₁ X} {M₂ : Modules Λ₂ X}
    {m₀₁ : M₀.X ⟶ M₁.X} {m₁₂ : M₁.X ⟶ M₂.X} {m₀₂ : M₀.X ⟶ M₂.X}
    (e₀₁ : Endpoint a M₀ M₁ m₀₁) (e₁₂ : Endpoint b M₁ M₂ m₁₂)
    (e₀₂ : Endpoint c M₀ M₂ m₀₂) (hline : m₀₁ ≫ m₁₂ = m₀₂) :
    (e₀₂.iso.hom = (scalarCompIso a b c hcoeff X).hom.app _ ≫
      (derivedScalars b X).map e₀₁.iso.hom ≫ e₁₂.iso.hom) ∧
    (e₀₂.shift c = (scalarCompIso a b c hcoeff X).hom.app _ ≫
      (derivedScalars b X).map (e₀₁.shift a) ≫ e₁₂.shift b) := by
  simpa only [endpoint_hom, endpoint_shift] using
    scalarHom_comp a b c hcoeff e₀₁.semilinear e₁₂.semilinear e₀₂.semilinear hline

private def endpoint_comp
    {Λ₀ Λ₁ Λ₂ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ₀] [IsCommMonObj Λ₀] [MonObj Λ₁] [IsCommMonObj Λ₁]
    [MonObj Λ₂] [IsCommMonObj Λ₂]
    (a : Λ₀ ⟶ Λ₁) (b : Λ₁ ⟶ Λ₂) (c : Λ₀ ⟶ Λ₂)
    [IsMonHom a] [IsMonHom b] [IsMonHom c] (hcoeff : a ≫ b = c)
    {X : Scheme.{u}} {M₀ : Modules Λ₀ X} {M₁ : Modules Λ₁ X} {M₂ : Modules Λ₂ X}
    {m₀₁ : M₀.X ⟶ M₁.X} {m₁₂ : M₁.X ⟶ M₂.X} {m₀₂ : M₀.X ⟶ M₂.X}
    (e₀₁ : Endpoint a M₀ M₁ m₀₁) (e₁₂ : Endpoint b M₁ M₂ m₁₂)
    (hline : m₀₁ ≫ m₁₂ = m₀₂) : Endpoint c M₀ M₂ m₀₂ := by
  let s : Semilinear c M₀ M₂ m₀₂ :=
    hline ▸ Semilinear.comp a b c hcoeff e₀₁.semilinear e₁₂.semilinear
  have h := (scalarHom_comp a b c hcoeff e₀₁.semilinear e₁₂.semilinear s hline).1
  rw [← endpoint_hom a e₀₁, ← endpoint_hom b e₁₂] at h
  have : IsIso (scalarHom c s) := by rw [h]; infer_instance
  exact endpointOfHom c s

private def endpoint_cancel
    {Λ₀ Λ₁ Λ₂ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ₀] [IsCommMonObj Λ₀] [MonObj Λ₁] [IsCommMonObj Λ₁]
    [MonObj Λ₂] [IsCommMonObj Λ₂]
    (a : Λ₀ ⟶ Λ₁) (b : Λ₁ ⟶ Λ₂) (c : Λ₀ ⟶ Λ₂)
    [IsMonHom a] [IsMonHom b] [IsMonHom c] (hcoeff : a ≫ b = c)
    {X : Scheme.{u}} {M₀ : Modules Λ₀ X} {M₁ : Modules Λ₁ X} {M₂ : Modules Λ₂ X}
    {m₀₁ : M₀.X ⟶ M₁.X} {m₁₂ : M₁.X ⟶ M₂.X} {m₀₂ : M₀.X ⟶ M₂.X}
    (e₀₁ : Endpoint a M₀ M₁ m₀₁) (e₀₂ : Endpoint c M₀ M₂ m₀₂)
    (s : Semilinear b M₁ M₂ m₁₂) (hline : m₀₁ ≫ m₁₂ = m₀₂) :
    Endpoint b M₁ M₂ m₁₂ := by
  have h := (scalarHom_comp a b c hcoeff e₀₁.semilinear s e₀₂.semilinear hline).1
  rw [← endpoint_hom a e₀₁, ← endpoint_hom c e₀₂] at h
  have : IsIso ((scalarCompIso a b c hcoeff X).hom.app _ ≫
      (derivedScalars b X).map e₀₁.iso.hom ≫ scalarHom b s) := by
    rw [← h]; infer_instance
  have := IsIso.of_isIso_comp_left ((scalarCompIso a b c hcoeff X).hom.app _)
    ((derivedScalars b X).map e₀₁.iso.hom ≫ scalarHom b s)
  have := IsIso.of_isIso_comp_left ((derivedScalars b X).map e₀₁.iso.hom)
    (scalarHom b s)
  exact endpointOfHom b s

private def regularSemilinear
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] (X : Scheme.{u}) :
    Semilinear a (Mod.regular (condensedRingObj Λ X))
      (Mod.regular (condensedRingObj Λ' X)) (coefficientMap a X) where
  hom := Mod.homMk (coefficientMap a X) (by
    change MonObj.mul ≫ coefficientMap a X =
      (condensedRingObj Λ X) ◁ coefficientMap a X ≫
        coefficientMap a X ▷ _ ≫ MonObj.mul
    rw [IsMonHom.mul_hom, MonoidalCategory.tensorHom_def', Category.assoc])
  underlying := rfl

private theorem supportMap_hom
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] (Y : Scheme.{u})
    (v : Mod.regular (condensedRingObj Λ (ProjectiveLine Y)) ⟶
      (Mod.comap (coefficientMap a (ProjectiveLine Y))).obj
        (Mod.regular (condensedRingObj Λ' (ProjectiveLine Y)))) :
    (supportMap a Y v).hom = (ProEtale.lowerStar Ab.{u + 1} (diagonalImmersion Y)).map
      v.hom := by
  change (ProEtale.lowerStar Ab.{u + 1} (diagonalImmersion Y)).map v.hom ≫ _ = _
  have h : ((CondensedRing.comapLowerStarIso a (diagonalImmersion Y)).inv.app
      (Mod.regular (condensedRingObj Λ' (ProjectiveLine Y)))).hom = 𝟙 _ := by
    change (𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫ (𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _) ≫ 𝟙 _) = 𝟙 _
    simp only [Category.id_comp]
  rw [h]
  change (ProEtale.lowerStar Ab.{u + 1} (diagonalImmersion Y)).map v.hom ≫
    𝟙 ((ProEtale.lowerStar Ab.{u + 1} (diagonalImmersion Y)).obj
      (condensedRingObj Λ' (ProjectiveLine Y))) = _
  exact Category.comp_id _

private theorem supportMap_comp
    {Λ₀ Λ₁ Λ₂ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ₀] [IsCommMonObj Λ₀] [MonObj Λ₁] [IsCommMonObj Λ₁]
    [MonObj Λ₂] [IsCommMonObj Λ₂]
    (a : Λ₀ ⟶ Λ₁) (b : Λ₁ ⟶ Λ₂) (c : Λ₀ ⟶ Λ₂)
    [IsMonHom a] [IsMonHom b] [IsMonHom c] (hcoeff : a ≫ b = c) (Y : Scheme.{u})
    (e₀₁ : Endpoint a (Mod.regular (condensedRingObj Λ₀ (ProjectiveLine Y)))
      (Mod.regular (condensedRingObj Λ₁ (ProjectiveLine Y)))
      (coefficientMap a (ProjectiveLine Y)))
    (e₁₂ : Endpoint b (Mod.regular (condensedRingObj Λ₁ (ProjectiveLine Y)))
      (Mod.regular (condensedRingObj Λ₂ (ProjectiveLine Y)))
      (coefficientMap b (ProjectiveLine Y)))
    (e₀₂ : Endpoint c (Mod.regular (condensedRingObj Λ₀ (ProjectiveLine Y)))
      (Mod.regular (condensedRingObj Λ₂ (ProjectiveLine Y)))
      (coefficientMap c (ProjectiveLine Y))) :
    (supportMap a Y e₀₁.semilinear.hom).hom ≫
        (supportMap b Y e₁₂.semilinear.hom).hom =
      (supportMap c Y e₀₂.semilinear.hom).hom := by
  simp only [supportMap_hom, e₀₁.semilinear.underlying, e₁₂.semilinear.underlying,
    e₀₂.semilinear.underlying, ← Functor.map_comp, hcoeff]

attribute [local irreducible] endpointOfHom endpoint_comp endpoint_cancel

private theorem mate_route_eq
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category* C₀] [Category* C₁] [Category* C₂]
    [Category* D₀] [Category* D₁] [Category* D₂]
    (R₀ : C₀ ⥤ D₀) (R₁ : C₁ ⥤ D₁) (R₂ : C₂ ⥤ D₂)
    (F : C₀ ⥤ C₁) (G : C₁ ⥤ C₂) (H : C₀ ⥤ C₂)
    (F' : D₀ ⥤ D₁) (G' : D₁ ⥤ D₂) (H' : D₀ ⥤ D₂)
    (A : H ≅ F ⋙ G) (A' : H' ≅ F' ⋙ G')
    (n₀₁ : R₀ ⋙ F' ⟶ F ⋙ R₁) (n₁₂ : R₁ ⋙ G' ⟶ G ⋙ R₂)
    (n₀₂ : R₀ ⋙ H' ⟶ H ⋙ R₂)
    {K₀ : C₀} {K₁ : C₁} {K₂ : C₂}
    (l₀₁ : F.obj K₀ ⟶ K₁) (l₁₂ : G.obj K₁ ⟶ K₂) (l₀₂ : H.obj K₀ ⟶ K₂)
    (hl : l₀₂ = A.hom.app K₀ ≫ G.map l₀₁ ≫ l₁₂)
    (hn : n₀₂.app K₀ ≫ R₂.map (A.hom.app K₀) =
      A'.hom.app (R₀.obj K₀) ≫ G'.map (n₀₁.app K₀) ≫ n₁₂.app (F.obj K₀)) :
    n₀₂.app K₀ ≫ R₂.map l₀₂ = A'.hom.app (R₀.obj K₀) ≫
      G'.map (n₀₁.app K₀ ≫ R₁.map l₀₁) ≫ (n₁₂.app K₁ ≫ R₂.map l₁₂) := by
  calc
    n₀₂.app K₀ ≫ R₂.map l₀₂ =
        (n₀₂.app K₀ ≫ R₂.map (A.hom.app K₀)) ≫
          R₂.map (G.map l₀₁) ≫ R₂.map l₁₂ := by
      rw [hl]
      simp only [Functor.map_comp, Category.assoc]
    _ = (A'.hom.app (R₀.obj K₀) ≫ G'.map (n₀₁.app K₀) ≫
        n₁₂.app (F.obj K₀)) ≫ R₂.map (G.map l₀₁) ≫ R₂.map l₁₂ := by rw [hn]
    _ = _ := by
      have h := n₁₂.naturality l₀₁
      dsimp only [Functor.comp_map] at h
      simp only [Functor.map_comp, Category.assoc]
      rw [← reassoc_of% h]

private theorem trace_triangle
    {Λ₀ Λ₁ Λ₂ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ₀] [IsCommMonObj Λ₀] [MonObj Λ₁] [IsCommMonObj Λ₁]
    [MonObj Λ₂] [IsCommMonObj Λ₂]
    (a : Λ₀ ⟶ Λ₁) (b : Λ₁ ⟶ Λ₂) (c : Λ₀ ⟶ Λ₂)
    [IsMonHom a] [IsMonHom b] [IsMonHom c] (hcoeff : a ≫ b = c)
    {X S : Scheme.{u}} (f : X ⟶ S)
    {M₀ : Modules Λ₀ X} {M₁ : Modules Λ₁ X} {M₂ : Modules Λ₂ X}
    {m₀₁ : M₀.X ⟶ M₁.X} {m₁₂ : M₁.X ⟶ M₂.X} {m₀₂ : M₀.X ⟶ M₂.X}
    (hline : m₀₁ ≫ m₁₂ = m₀₂)
    (c₀₁ : Endpoint a (Mod.regular (condensedRingObj Λ₀ S))
      (Mod.regular (condensedRingObj Λ₁ S)) (coefficientMap a S))
    (c₁₂ : Endpoint b (Mod.regular (condensedRingObj Λ₁ S))
      (Mod.regular (condensedRingObj Λ₂ S)) (coefficientMap b S))
    (c₀₂ : Endpoint c (Mod.regular (condensedRingObj Λ₀ S))
      (Mod.regular (condensedRingObj Λ₂ S)) (coefficientMap c S))
    (l₀₁ : Endpoint a M₀ M₁ m₀₁) (l₁₂ : Endpoint b M₁ M₂ m₁₂)
    (l₀₂ : Endpoint c M₀ M₂ m₀₂)
    (R₀ : DiagonalRightDerived (CondensedRing.lowerStar Λ₀ f))
    (R₁ : DiagonalRightDerived (CondensedRing.lowerStar Λ₁ f))
    (R₂ : DiagonalRightDerived (CondensedRing.lowerStar Λ₂ f))
    (t₀ : R₀.R.obj (((DerivedCategory.singleFunctor _ 0).obj M₀)⟦(2 : ℤ)⟧) ⟶ unit Λ₀ S)
    (t₁ : R₁.R.obj (((DerivedCategory.singleFunctor _ 0).obj M₁)⟦(2 : ℤ)⟧) ⟶ unit Λ₁ S)
    (t₂ : R₂.R.obj (((DerivedCategory.singleFunctor _ 0).obj M₂)⟦(2 : ℤ)⟧) ⟶ unit Λ₂ S)
    (h₀₁ : TraceCompatibility a f c₀₁ l₀₁ R₀ R₁ t₀ t₁)
    (s₁₂ : RestrictionSquare b f R₁ R₂) (s₀₂ : RestrictionSquare c f R₀ R₂)
    (hmate : ∀ K : DerivedCategory (Modules Λ₀ X),
      (s₀₂.mate c).app K ≫ R₂.R.map ((scalarCompIso a b c hcoeff X).hom.app K) =
        (scalarCompIso a b c hcoeff S).hom.app (R₀.R.obj K) ≫
          (derivedScalars b S).map ((h₀₁.square.mate a).app K) ≫
          (s₁₂.mate b).app ((derivedScalars a X).obj K)) :
    (IsIso ((s₀₂.mate c).app
        (((DerivedCategory.singleFunctor _ 0).obj M₀)⟦(2 : ℤ)⟧)) ∧
      (derivedScalars c S).map t₀ ≫ c₀₂.iso.hom =
        (s₀₂.mate c).app _ ≫ R₂.R.map (l₀₂.shift c) ≫ t₂) ↔
    (IsIso ((s₁₂.mate b).app
        (((DerivedCategory.singleFunctor _ 0).obj M₁)⟦(2 : ℤ)⟧)) ∧
      (derivedScalars b S).map t₁ ≫ c₁₂.iso.hom =
        (s₁₂.mate b).app _ ≫ R₂.R.map (l₁₂.shift b) ≫ t₂) := by
  let K₀ := ((DerivedCategory.singleFunctor (Modules Λ₀ X) 0).obj M₀)⟦(2 : ℤ)⟧
  let K₁ := ((DerivedCategory.singleFunctor (Modules Λ₁ X) 0).obj M₁)⟦(2 : ℤ)⟧
  let k₀₁ := (h₀₁.square.mate a).app K₀ ≫ R₁.R.map (l₀₁.shift a)
  let k₁₂ := (s₁₂.mate b).app K₁ ≫ R₂.R.map (l₁₂.shift b)
  let k₀₂ := (s₀₂.mate c).app K₀ ≫ R₂.R.map (l₀₂.shift c)
  have hshift₀₁ : IsIso (l₀₁.shift a) := by unfold Endpoint.shift; infer_instance
  have hshift₁₂ : IsIso (l₁₂.shift b) := by unfold Endpoint.shift; infer_instance
  have hshift₀₂ : IsIso (l₀₂.shift c) := by unfold Endpoint.shift; infer_instance
  have : IsIso ((h₀₁.square.mate a).app K₀) := h₀₁.comparison_iso
  have : IsIso k₀₁ := by dsimp only [k₀₁]; infer_instance
  have hk : k₀₂ = (scalarCompIso a b c hcoeff S).hom.app (R₀.R.obj K₀) ≫
      (derivedScalars b S).map k₀₁ ≫ k₁₂ :=
    mate_route_eq R₀.R R₁.R R₂.R _ _ _ _ _ _
      (scalarCompIso a b c hcoeff X) (scalarCompIso a b c hcoeff S)
      (h₀₁.square.mate a) (s₁₂.mate b) (s₀₂.mate c)
      (l₀₁.shift a) (l₁₂.shift b) (l₀₂.shift c)
      (endpoint_equations a b c hcoeff l₀₁ l₁₂ l₀₂ hline).2 (hmate K₀)
  have hu := (endpoint_equations a b c hcoeff c₀₁ c₁₂ c₀₂
    (by rw [← coefficientMap_comp, hcoeff])).1
  have ht := triangle_eq_iff (derivedScalars a S) (derivedScalars b S)
    (derivedScalars c S) (scalarCompIso a b c hcoeff S)
    k₀₁ k₁₂ k₀₂ c₀₁.iso.hom c₁₂.iso.hom c₀₂.iso.hom hk hu t₀ t₁ t₂
    (by simpa only [k₀₁, Category.assoc] using h₀₁.trace)
  have hi : IsIso ((s₀₂.mate c).app K₀) ↔ IsIso ((s₁₂.mate b).app K₁) := by
    calc
      IsIso ((s₀₂.mate c).app K₀) ↔ IsIso k₀₂ :=
        (isIso_comp_right_iff _ (R₂.R.map (l₀₂.shift c))).symm
      _ ↔ IsIso k₁₂ := by
        rw [hk, isIso_comp_left_iff, isIso_comp_left_iff]
      _ ↔ IsIso ((s₁₂.mate b).app K₁) :=
        isIso_comp_right_iff _ (R₂.R.map (l₁₂.shift b))
  simpa only [k₀₂, k₁₂, Category.assoc] using and_congr hi ht

/-- Compatibility along a composite coefficient route is equivalent to compatibility
along its second leg, once compatibility along its first leg is fixed. This is a
formal statement about three diagrams, with no finiteness or colimit assertion.
The second line map is required to be semilinear at both line endpoints.

Source: blueprint latest, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md, paragraph (2), compatibility of scalar routes.
(blueprint: lem-diagonal-scalar-compatibility-triangle).

Proof: Compose the derived scalar/restriction adjunctions and identify the composite
restriction with restriction along a followed by b. Uniqueness of left adjoints gives
the scalar associator normalized by these units. The prescribed coefficient and line
map equations and the supplied semilinearity identify the regular, line and supported
endpoints along the two routes:
the ordinary semilinear maps are equal, and injectivity of the derived Hom adjunction
identifies their normalized derived homs. Derive the ordinary restriction/direct-image
squares using their full units. Their composition agrees with the composite-coefficient
square by uniqueness of the universal right-derived transformation. Taking scalar
mates gives the corresponding composition equation for the direct-image mates.
In the forward direction solve these composition equations for the second endpoint
and mate, cancelling the isomorphisms for the first leg. Their inverses and the
composite isomorphisms prove that the second endpoints and the mate on the shifted
line are invertible. Substitute the class and trace equations for the first leg into
those for the composite and cancel the first endpoint isomorphisms. This gives the
second class and trace equations. In the reverse direction compose the two endpoint
isomorphisms and scalar mates, substitute both class and trace squares and use
naturality of the scalar associator. Full-unit normalization and adjunction
injectivity give exactly the required endpoint and restriction normalizations.
The argument includes identity maps, zero rings, empty schemes and nonflat maps;
only the supplied semilinearity and the endpoint and mate isomorphisms recorded
in the compatibilities are used. Semilinearity cannot be deduced merely from the
composite map: an additive map of a field extension can fix its base field without
being linear over the extension, so it is retained as an explicit hypothesis. -/
theorem scalarCompatibility_triangle
    {Λ₀ Λ₁ Λ₂ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ₀] [IsCommMonObj Λ₀] [MonObj Λ₁] [IsCommMonObj Λ₁]
    [MonObj Λ₂] [IsCommMonObj Λ₂]
    (a : Λ₀ ⟶ Λ₁) (b : Λ₁ ⟶ Λ₂) (c : Λ₀ ⟶ Λ₂)
    [IsMonHom a] [IsMonHom b] [IsMonHom c] (Y : Scheme.{u})
    (L₀ : ∀ X : Scheme.{u}, Modules Λ₀ X)
    (L₁ : ∀ X : Scheme.{u}, Modules Λ₁ X)
    (L₂ : ∀ X : Scheme.{u}, Modules Λ₂ X)
    (m₀₁ : ∀ X : Scheme.{u}, (L₀ X).X ⟶ (L₁ X).X)
    (m₁₂ : ∀ X : Scheme.{u}, (L₁ X).X ⟶ (L₂ X).X)
    (m₀₂ : ∀ X : Scheme.{u}, (L₀ X).X ⟶ (L₂ X).X)
    (d₀ : Diagram Λ₀ Y L₀) (d₁ : Diagram Λ₁ Y L₁) (d₂ : Diagram Λ₂ Y L₂)
    (hcoeff : a ≫ b = c) (hline : ∀ X, m₀₁ X ≫ m₁₂ X = m₀₂ X)
    (h₀₁ : ScalarCompatibility a Y L₀ L₁ m₀₁ d₀ d₁)
    (sP : Semilinear b (L₁ (ProjectiveLine Y)) (L₂ (ProjectiveLine Y))
      (m₁₂ (ProjectiveLine Y)))
    (sW : Semilinear b (L₁ (diagonalSurface Y)) (L₂ (diagonalSurface Y))
      (m₁₂ (diagonalSurface Y))) :
    Nonempty (ScalarCompatibility c Y L₀ L₂ m₀₂ d₀ d₂) ↔
      Nonempty (ScalarCompatibility b Y L₁ L₂ m₁₂ d₁ d₂) := by
  obtain ⟨⟨q₁₂⟩, ⟨q₀₂⟩, hq⟩ := scalarRestriction_comp a b c hcoeff
    (ProjectiveLine Y ↘ Y) d₀.Rq d₁.Rq d₂.Rq
  obtain ⟨⟨p₁₁₂⟩, ⟨p₁₀₂⟩, hp₁⟩ := scalarRestriction_comp a b c hcoeff
    (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)) d₀.R₁ d₁.R₁ d₂.R₁
  obtain ⟨⟨p₂₁₂⟩, ⟨p₂₀₂⟩, hp₂⟩ := scalarRestriction_comp a b c hcoeff
    (pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)) d₀.R₂ d₁.R₂ d₂.R₂
  constructor
  · rintro ⟨h₀₂⟩
    let units₁₂ := fun X : Scheme.{u} ↦ endpoint_cancel a b c hcoeff
      (h₀₁.units X) (h₀₂.units X) (regularSemilinear b X)
      (by rw [← coefficientMap_comp, hcoeff])
    let lineP₁₂ := endpoint_cancel a b c hcoeff h₀₁.lineP h₀₂.lineP sP
      (hline (ProjectiveLine Y))
    let lineW₁₂ := endpoint_cancel a b c hcoeff h₀₁.lineW h₀₂.lineW sW
      (hline (diagonalSurface Y))
    have hs := supportMap_comp a b c hcoeff Y (h₀₁.units (ProjectiveLine Y))
      (units₁₂ (ProjectiveLine Y)) (h₀₂.units (ProjectiveLine Y))
    let supported₁₂ := endpoint_cancel a b c hcoeff h₀₁.supported h₀₂.supported
      ⟨supportMap b Y (units₁₂ (ProjectiveLine Y)).semilinear.hom, rfl⟩ hs
    obtain ⟨hqiso, hqtrace⟩ := (trace_triangle a b c hcoeff
      (ProjectiveLine Y ↘ Y) (hline (ProjectiveLine Y))
      (h₀₁.units Y) (units₁₂ Y) (h₀₂.units Y) h₀₁.lineP lineP₁₂ h₀₂.lineP
      d₀.Rq d₁.Rq d₂.Rq d₀.traceq d₁.traceq d₂.traceq h₀₁.q q₁₂ h₀₂.q.square
      (hq h₀₁.q.square q₁₂ h₀₂.q.square)).mp ⟨h₀₂.q.comparison_iso, h₀₂.q.trace⟩
    obtain ⟨h₁iso, h₁trace⟩ := (trace_triangle a b c hcoeff
      (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))
      (hline (diagonalSurface Y))
      (h₀₁.units (ProjectiveLine Y)) (units₁₂ (ProjectiveLine Y))
      (h₀₂.units (ProjectiveLine Y)) h₀₁.lineW lineW₁₂ h₀₂.lineW
      d₀.R₁ d₁.R₁ d₂.R₁ d₀.trace₁ d₁.trace₁ d₂.trace₁ h₀₁.p₁ p₁₁₂ h₀₂.p₁.square
      (hp₁ h₀₁.p₁.square p₁₁₂ h₀₂.p₁.square)).mp ⟨h₀₂.p₁.comparison_iso, h₀₂.p₁.trace⟩
    obtain ⟨h₂iso, h₂trace⟩ := (trace_triangle a b c hcoeff
      (pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))
      (hline (diagonalSurface Y))
      (h₀₁.units (ProjectiveLine Y)) (units₁₂ (ProjectiveLine Y))
      (h₀₂.units (ProjectiveLine Y)) h₀₁.lineW lineW₁₂ h₀₂.lineW
      d₀.R₂ d₁.R₂ d₂.R₂ d₀.trace₂ d₁.trace₂ d₂.trace₂ h₀₁.p₂ p₂₁₂ h₀₂.p₂.square
      (hp₂ h₀₁.p₂.square p₂₁₂ h₀₂.p₂.square)).mp ⟨h₀₂.p₂.comparison_iso, h₀₂.p₂.trace⟩
    have hdelta := (triangle_eq_iff
      (derivedScalars a (diagonalSurface Y)) (derivedScalars b (diagonalSurface Y))
      (derivedScalars c (diagonalSurface Y)) (scalarCompIso a b c hcoeff (diagonalSurface Y))
      h₀₁.supported.iso.hom supported₁₂.iso.hom h₀₂.supported.iso.hom
      (h₀₁.lineW.shift a) (lineW₁₂.shift b) (h₀₂.lineW.shift c)
      (endpoint_equations a b c hcoeff h₀₁.supported supported₁₂ h₀₂.supported hs).1
      (endpoint_equations a b c hcoeff h₀₁.lineW lineW₁₂ h₀₂.lineW
        (hline (diagonalSurface Y))).2
      d₀.delta d₁.delta d₂.delta h₀₁.delta).mp h₀₂.delta
    exact ⟨{
      units := units₁₂
      lineP := lineP₁₂
      lineW := lineW₁₂
      supported := supported₁₂
      q := ⟨q₁₂, hqiso, hqtrace⟩
      p₁ := ⟨p₁₁₂, h₁iso, h₁trace⟩
      p₂ := ⟨p₂₁₂, h₂iso, h₂trace⟩
      delta := hdelta }⟩
  · rintro ⟨h₁₂⟩
    let units₀₂ := fun X : Scheme.{u} ↦ endpoint_comp a b c hcoeff
      (h₀₁.units X) (h₁₂.units X) (by rw [← coefficientMap_comp, hcoeff])
    let lineP₀₂ := endpoint_comp a b c hcoeff h₀₁.lineP h₁₂.lineP
      (hline (ProjectiveLine Y))
    let lineW₀₂ := endpoint_comp a b c hcoeff h₀₁.lineW h₁₂.lineW
      (hline (diagonalSurface Y))
    have hs := supportMap_comp a b c hcoeff Y (h₀₁.units (ProjectiveLine Y))
      (h₁₂.units (ProjectiveLine Y)) (units₀₂ (ProjectiveLine Y))
    let supported₀₂ := endpoint_comp a b c hcoeff h₀₁.supported h₁₂.supported hs
    obtain ⟨hqiso, hqtrace⟩ := (trace_triangle a b c hcoeff
      (ProjectiveLine Y ↘ Y) (hline (ProjectiveLine Y))
      (h₀₁.units Y) (h₁₂.units Y) (units₀₂ Y) h₀₁.lineP h₁₂.lineP lineP₀₂
      d₀.Rq d₁.Rq d₂.Rq d₀.traceq d₁.traceq d₂.traceq h₀₁.q h₁₂.q.square q₀₂
      (hq h₀₁.q.square h₁₂.q.square q₀₂)).mpr ⟨h₁₂.q.comparison_iso, h₁₂.q.trace⟩
    obtain ⟨h₁iso, h₁trace⟩ := (trace_triangle a b c hcoeff
      (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))
      (hline (diagonalSurface Y))
      (h₀₁.units (ProjectiveLine Y)) (h₁₂.units (ProjectiveLine Y))
      (units₀₂ (ProjectiveLine Y)) h₀₁.lineW h₁₂.lineW lineW₀₂
      d₀.R₁ d₁.R₁ d₂.R₁ d₀.trace₁ d₁.trace₁ d₂.trace₁ h₀₁.p₁ h₁₂.p₁.square p₁₀₂
      (hp₁ h₀₁.p₁.square h₁₂.p₁.square p₁₀₂)).mpr ⟨h₁₂.p₁.comparison_iso, h₁₂.p₁.trace⟩
    obtain ⟨h₂iso, h₂trace⟩ := (trace_triangle a b c hcoeff
      (pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))
      (hline (diagonalSurface Y))
      (h₀₁.units (ProjectiveLine Y)) (h₁₂.units (ProjectiveLine Y))
      (units₀₂ (ProjectiveLine Y)) h₀₁.lineW h₁₂.lineW lineW₀₂
      d₀.R₂ d₁.R₂ d₂.R₂ d₀.trace₂ d₁.trace₂ d₂.trace₂ h₀₁.p₂ h₁₂.p₂.square p₂₀₂
      (hp₂ h₀₁.p₂.square h₁₂.p₂.square p₂₀₂)).mpr ⟨h₁₂.p₂.comparison_iso, h₁₂.p₂.trace⟩
    have hdelta := (triangle_eq_iff
      (derivedScalars a (diagonalSurface Y)) (derivedScalars b (diagonalSurface Y))
      (derivedScalars c (diagonalSurface Y)) (scalarCompIso a b c hcoeff (diagonalSurface Y))
      h₀₁.supported.iso.hom h₁₂.supported.iso.hom supported₀₂.iso.hom
      (h₀₁.lineW.shift a) (h₁₂.lineW.shift b) (lineW₀₂.shift c)
      (endpoint_equations a b c hcoeff h₀₁.supported h₁₂.supported supported₀₂ hs).1
      (endpoint_equations a b c hcoeff h₀₁.lineW h₁₂.lineW lineW₀₂
        (hline (diagonalSurface Y))).2
      d₀.delta d₁.delta d₂.delta h₀₁.delta).mpr h₁₂.delta
    exact ⟨{
      units := units₀₂
      lineP := lineP₀₂
      lineW := lineW₀₂
      supported := supported₀₂
      q := ⟨q₀₂, hqiso, hqtrace⟩
      p₁ := ⟨p₁₀₂, h₁iso, h₁trace⟩
      p₂ := ⟨p₂₀₂, h₂iso, h₂trace⟩
      delta := hdelta }⟩

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
