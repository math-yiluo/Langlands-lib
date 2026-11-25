/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondPretraceData
import WeilConjectures.AlgebraicGeometry.RationalP1.Native.NativeSecondExtractProjection
import all WeilConjectures.AlgebraicGeometry.RationalP1.Native.NativeNormalizedSelfSquareProjection
import all WeilConjectures.CategoryTheory.Native.NativeForwardSelfSquareProjection
import all WeilConjectures.AlgebraicGeometry.RationalP1.Canonical.CanonicalSectionProjectionTransport

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward false
set_option synthInstance.maxSize 4096
open CategoryTheory MonoidalCategory
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Functor

private theorem extract_transport
    {D V : Type*} [Category D] [Category V]
    [MonoidalCategory D] [MonoidalCategory V]
    (U₁ U₂ : D ⥤ V) (Q : V ⥤ D)
    (A T M : D) (T' M' : V)
    (π : ∀ N : V, A ⊗ Q.obj N ⟶ Q.obj (U₂.obj A ⊗ N))
    (s : U₂.obj A ≅ U₁.obj A)
    (d : U₁.obj (A ⊗ T) ≅ U₁.obj A ⊗ U₁.obj T)
    (e : U₁.obj T ≅ T') (t : A ⊗ T ≅ M) (v : U₁.obj A ⊗ T' ≅ M')
    (hn : (A ◁ Q.map e.hom) ≫ π T' = π (U₁.obj T) ≫ Q.map (U₂.obj A ◁ e.hom)) :
    (A ◁ Q.map e.hom) ≫ π T' ≫
      Q.map (tensorHom s.hom (𝟙 T') ≫ v.hom ≫
        (U₁.mapIso t.symm ≪≫ d ≪≫ tensorIso (Iso.refl _) e ≪≫ v).inv) =
    π (U₁.obj T) ≫ Q.map
      ((d ≪≫ tensorIso s.symm (Iso.refl _)).inv ≫ U₁.map t.hom) := by
  rw [← Category.assoc, hn]
  simp only [Category.assoc, Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv,
    tensorIso_inv, Iso.refl_inv, v.hom_inv_id_assoc, ← Q.map_comp]
  congr 2
  simp only [← id_tensorHom, tensorHom_comp_tensorHom_assoc,
    Iso.hom_inv_id, Category.comp_id, Category.id_comp]

private theorem forward_transport
    {C D V : Type*} [Category C] [Category D] [Category V]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory V]
    (F : C ⥤ D) (P : D ⥤ C) (U₁ U₂ : D ⥤ V) (Q : V ⥤ D)
    (ex : P ⋙ F ⟶ U₁ ⋙ Q) (K : C) (T M : D) (T' M' : V)
    (π₀ : K ⊗ P.obj T ⟶ P.obj (F.obj K ⊗ T))
    (π : ∀ N : V, F.obj K ⊗ Q.obj N ⟶ Q.obj (U₂.obj (F.obj K) ⊗ N))
    (δ : F.obj (K ⊗ P.obj T) ⟶ F.obj K ⊗ F.obj (P.obj T))
    (s : U₂.obj (F.obj K) ≅ U₁.obj (F.obj K))
    (d : U₁.obj (F.obj K ⊗ T) ≅ U₁.obj (F.obj K) ⊗ U₁.obj T)
    (e : U₁.obj T ≅ T') (t : F.obj K ⊗ T ≅ M)
    (v : U₁.obj (F.obj K) ⊗ T' ≅ M')
    (hs : F.map π₀ ≫ ex.app (F.obj K ⊗ T) ≫
      Q.map (d.hom ≫ tensorHom s.inv (𝟙 (U₁.obj T))) =
      δ ≫ (F.obj K ◁ ex.app T) ≫ π (U₁.obj T))
    (hn : (F.obj K ◁ Q.map e.hom) ≫ π T' =
      π (U₁.obj T) ≫ Q.map (U₂.obj (F.obj K) ◁ e.hom)) :
    F.map π₀ ≫ F.map (P.map t.hom) ≫ ex.app M =
      δ ≫ (F.obj K ◁ (ex.app T ≫ Q.map e.hom)) ≫ π T' ≫
        Q.map (tensorHom s.hom (𝟙 T') ≫ v.hom ≫
          (U₁.mapIso t.symm ≪≫ d ≪≫ tensorIso (Iso.refl _) e ≪≫ v).inv) := by
  rw [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [extract_transport U₁ U₂ Q (F.obj K) T M T' M' π s d e t v hn]
  have hs' : F.map π₀ ≫ ex.app (F.obj K ⊗ T) ≫
      Q.map (d ≪≫ tensorIso s.symm (Iso.refl _)).hom =
      δ ≫ (F.obj K ◁ ex.app T) ≫ π (U₁.obj T) := by
    simpa only [Iso.trans_hom, tensorIso_hom, Iso.symm_hom, Iso.refl_hom] using hs
  have ht := ex.naturality t.hom
  dsimp only [Functor.comp_map] at ht
  rw [ht]
  let c := d ≪≫ tensorIso s.symm (Iso.refl _)
  have hh := congrArg (fun z ↦ z ≫ Q.map (c.inv ≫ U₁.map t.hom)) hs'
  simpa only [Category.assoc, ← Q.map_comp,
    c, Iso.hom_inv_id_assoc] using hh

private theorem forward_transport_identified
    {C D V : Type*} [Category C] [Category D] [Category V]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory V]
    (F : C ⥤ D) (P : D ⥤ C) (U₁ U₂ : D ⥤ V) (Q : V ⥤ D)
    (ex : P ⋙ F ⟶ U₁ ⋙ Q) (K : C) (T M : D) (T' M' : V)
    (π₀ : K ⊗ P.obj T ⟶ P.obj (F.obj K ⊗ T))
    (π : ∀ N : V, F.obj K ⊗ Q.obj N ⟶ Q.obj (U₂.obj (F.obj K) ⊗ N))
    (δ δ' : F.obj (K ⊗ P.obj T) ⟶ F.obj K ⊗ F.obj (P.obj T))
    (s : U₂.obj (F.obj K) ≅ U₁.obj (F.obj K))
    (d : U₁.obj (F.obj K ⊗ T) ≅ U₁.obj (F.obj K) ⊗ U₁.obj T)
    (e : U₁.obj T ≅ T') (t : F.obj K ⊗ T ≅ M)
    (v : U₁.obj (F.obj K) ⊗ T' ≅ M') (w : U₁.obj M ≅ M')
    (bM : F.obj (P.obj M) ⟶ Q.obj (U₁.obj M))
    (bT : F.obj (P.obj T) ⟶ Q.obj (U₁.obj T))
    (hδ : δ' = δ) (hM : bM = ex.app M) (hT : bT = ex.app T)
    (hw : w = U₁.mapIso t.symm ≪≫ d ≪≫ tensorIso (Iso.refl _) e ≪≫ v)
    (hs : F.map π₀ ≫ ex.app (F.obj K ⊗ T) ≫
      Q.map (d.hom ≫ tensorHom s.inv (𝟙 (U₁.obj T))) =
      δ ≫ (F.obj K ◁ ex.app T) ≫ π (U₁.obj T))
    (hn : (F.obj K ◁ Q.map e.hom) ≫ π T' =
      π (U₁.obj T) ≫ Q.map (U₂.obj (F.obj K) ◁ e.hom)) :
    F.map π₀ ≫ F.map (P.map t.hom) ≫ bM =
      δ' ≫ (F.obj K ◁ (bT ≫ Q.map e.hom)) ≫ π T' ≫
        Q.map (tensorHom s.hom (𝟙 T') ≫ v.hom ≫ w.inv) := by
  subst δ'
  subst bM
  subst bT
  subst w
  exact forward_transport F P U₁ U₂ Q ex K T M T' M' π₀ π δ s d e t v hs hn

private theorem forward_transport_bundled
    {C D V : Type*} [Category C] [Category D] [Category V]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory V]
    (F : C ⥤ D) (P : D ⥤ C) (U₁ U₂ : D ⥤ V) (Q : V ⥤ D)
    (ex : P ⋙ F ⟶ U₁ ⋙ Q) (K : C) (T M : D) (T' M' : V)
    (π₀ : K ⊗ P.obj T ⟶ P.obj (F.obj K ⊗ T))
    (π : ∀ N : V, F.obj K ⊗ Q.obj N ⟶ Q.obj (U₂.obj (F.obj K) ⊗ N))
    (δ δ' : F.obj (K ⊗ P.obj T) ⟶ F.obj K ⊗ F.obj (P.obj T))
    (s : U₂.obj (F.obj K) ≅ U₁.obj (F.obj K))
    (d : U₁.obj (F.obj K ⊗ T) ≅ U₁.obj (F.obj K) ⊗ U₁.obj T)
    (e : U₁.obj T ≅ T') (t : F.obj K ⊗ T ≅ M)
    (v : U₁.obj (F.obj K) ⊗ T' ≅ M') (w : U₁.obj M ≅ M')
    (bM : F.obj (P.obj M) ⟶ Q.obj (U₁.obj M))
    (bT : F.obj (P.obj T) ⟶ Q.obj (U₁.obj T))
    (hδ : δ' = δ) (hM : bM = ex.app M) (hT : bT = ex.app T)
    (hw : w = U₁.mapIso t.symm ≪≫ d ≪≫ tensorIso (Iso.refl _) e ≪≫ v)
    (a : F ⊣ P) (b : U₂ ⊣ Q) (sNat tNat : F ⋙ U₂ ≅ F ⋙ U₁)
    (dF : ∀ A B, F.obj (A ⊗ B) ⟶ F.obj A ⊗ F.obj B)
    (d₁ : ∀ A B, U₁.obj (A ⊗ B) ⟶ U₁.obj A ⊗ U₁.obj B)
    (d₂ : ∀ A B, U₂.obj (A ⊗ B) ⟶ U₂.obj A ⊗ U₂.obj B)
    (hp₀ : π₀ = traceProjectionFromComparison a dF K T)
    (hp₂ : ∀ N, π N = traceProjectionFromComparison b d₂ (F.obj K) N)
    (he : ex = traceAbstractMate a b tNat) (hst : sNat = tNat)
    (h : ForwardTensorSquare
      { monoidalC := inferInstance, monoidalD := inferInstance, monoidalV := inferInstance,
        tensorF := dF, tensorOne := d₁, tensorTwo := d₂ } P Q a b tNat)
    (hδ₀ : δ = dF K (P.obj T)) (hd₀ : d.hom = d₁ (F.obj K) T)
    (hs₀ : s = sNat.app K)
    (hn : (F.obj K ◁ Q.map e.hom) ≫ π T' =
      π (U₁.obj T) ≫ Q.map (U₂.obj (F.obj K) ◁ e.hom)) :
    F.map π₀ ≫ F.map (P.map t.hom) ≫ bM =
      δ' ≫ (F.obj K ◁ (bT ≫ Q.map e.hom)) ≫ π T' ≫
        Q.map (tensorHom s.hom (𝟙 T') ≫ v.hom ≫ w.inv) := by
  have hbare := substitute_forward_square F P U₁ U₂ Q a b sNat tNat ex
    dF d₁ d₂ K T π₀ (π (U₁.obj T)) hp₀ (hp₂ _) he hst h
  exact forward_transport_identified F P U₁ U₂ Q ex K T M T' M' π₀ π δ δ' s d e t v w
    bM bT hδ hM hT hw (by rw [hδ₀, hd₀, hs₀]; exact hbare) hn

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing
attribute [local implicit_reducible] ProjectionFamily
attribute [local irreducible] nativeProjectionTensorIso nativeSelfSquareExchange

private theorem second_tensor_comparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (K V : DerivedCategory (Modules Λ Y)) :
    (secondTraceTensorIso Λ Y K V).symm =
      nativeProjectionTensorIso Λ (ProjectiveLine Y ↘ Y) K V := by
  unfold secondTraceTensorIso secondTracePullMonoidal nativeProjectionTensorIso
  unfold internalMonoidal internalTensorBundle nativeTensorBundle
  apply Iso.ext_inv
  rfl
private theorem pull_twist_comparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} (f : X ⟶ S)
    (LS : Modules Λ S) (LX : Modules Λ X)
    (e : (moduleObjectDerivedPullback Λ f).obj
      (((DerivedCategory.singleFunctor (Modules Λ S) 0).obj LS) ⟦(2 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor (Modules Λ X) 0).obj LX) ⟦(2 : ℤ)⟧)
    (A : DerivedCategory (Modules Λ S)) :
    pullTwistIso Λ f LS LX e A =
      (moduleObjectDerivedPullback Λ f).mapIso (tensorShiftIso Λ S LS A).symm ≪≫
        nativeProjectionTensorIso Λ f A
          (((DerivedCategory.singleFunctor (Modules Λ S) 0).obj LS) ⟦(2 : ℤ)⟧) ≪≫
        tensorIso (Iso.refl _) e ≪≫
        tensorShiftIso Λ X LX ((moduleObjectDerivedPullback Λ f).obj A) := by
  unfold pullTwistIso nativeProjectionTensorIso
  rfl

attribute [local irreducible] coefficient line twist projectionMap tensorShiftIso
attribute [local irreducible] secondLineComparison twistProjectionMap
-- Keep the native derived constructions folded while allowing their endpoint aliases to reduce.
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory DerivedCategory.Qh
attribute [local irreducible] firstProjection secondProjection square condensedAmbientExchange

/-- The native exchange component with its module-object endpoints exposed. -/
def nativeExchange
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (M : DerivedCategory (Modules Λ (ProjectiveLine Y))) :
    (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj
      ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M) ⟶
    (moduleObjectDerivedPushforward Λ (secondProjection Y)).obj
      ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M) := by
  unfold moduleObjectDerivedPullback moduleObjectDerivedPushforward
  exact (condensedAmbientExchange Λ (square Y)).app M

private theorem exchange_component
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (M : DerivedCategory (Modules Λ (ProjectiveLine Y))) :
    (nativeSelfSquareExchange Λ (ProjectiveLine Y ↘ Y)
      (firstProjection Y) (secondProjection Y) (square Y)).app M = nativeExchange Λ Y M := by
  unfold nativeSelfSquareExchange nativeExchange
  rfl

private theorem pretrace_native
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (M : DerivedCategory (Modules Λ (ProjectiveLine Y))) :
    secondPretraceExchangeMap Λ Y M = nativeExchange Λ Y M := by
  unfold secondPretraceExchangeMap nativeExchange
  rfl

attribute [local irreducible] nativeExchange

private theorem second_tensor_inv
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (K V : DerivedCategory (Modules Λ Y)) :
    (secondTraceTensorIso Λ Y K V).inv =
      (nativeProjectionTensorIso Λ (ProjectiveLine Y ↘ Y) K V).hom :=
  congrArg Iso.hom (second_tensor_comparison Λ Y K V)

private theorem fixed_naturality
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} (f : X ⟶ S)
    (K : DerivedCategory (Modules Λ S))
    {N N' : DerivedCategory (Modules Λ X)} (n : N ⟶ N') :
    (K ◁ (moduleObjectDerivedPushforward Λ f).map n) ≫ projectionMap Λ f K N' =
      projectionMap Λ f K N ≫ (moduleObjectDerivedPushforward Λ f).map
        ((moduleObjectDerivedPullback Λ f).obj K ◁ n) := by
  exact projection_coefficient_naturality Λ f K n

private theorem fixed_projection_transpose
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} (f : X ⟶ S)
    (K : DerivedCategory (Modules Λ S)) (T : DerivedCategory (Modules Λ X)) :
    projectionMap Λ f K T = traceProjectionFromComparison (traceAdjunction Λ f)
      (fun A B ↦ (nativeProjectionTensorIso Λ f A B).hom) K T := by
  unfold projectionMap
  exact bundled_projection Λ (projection_existsUnique Λ).exists.choose
    (projection_existsUnique Λ).exists.choose_spec f K T

attribute [local irreducible] ForwardTensorSquare

attribute [local irreducible] moduleObjectDerivedPullback moduleObjectDerivedPushforward
private theorem native_twisted_self_square
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (LS : Modules Λ (ProjectiveLine Y)) (LW : Modules Λ (diagonalSurface Y))
    (e : (moduleObjectDerivedPullback Λ (firstProjection Y)).obj
      (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj LS) ⟦(2 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj LW) ⟦(2 : ℤ)⟧)
    (K : DerivedCategory (Modules Λ Y)) :
    let F := moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)
    let P := moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)
    let Q := moduleObjectDerivedPushforward Λ (secondProjection Y)
    let T := ((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj LS)
      ⟦(2 : ℤ)⟧
    F.map (projectionMap Λ (ProjectiveLine Y ↘ Y) K T) ≫
      F.map (P.map (tensorShiftIso Λ (ProjectiveLine Y) LS (F.obj K)).hom) ≫
        nativeExchange Λ Y ((twist Λ (ProjectiveLine Y) LS).obj (F.obj K)) =
    (secondTraceTensorIso Λ Y K (P.obj T)).inv ≫
      (F.obj K ◁ (secondPretraceExchangeMap Λ Y T ≫ Q.map e.hom)) ≫
      nativeSecondExtractProjection Λ Y LS LW e K := by
  rw [nativeSecondExtractProjection_eq]
  let F := moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)
  let P := moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)
  let U₁ := moduleObjectDerivedPullback Λ (firstProjection Y)
  let U₂ := moduleObjectDerivedPullback Λ (secondProjection Y)
  let Q := moduleObjectDerivedPushforward Λ (secondProjection Y)
  let T := ((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj LS)
    ⟦(2 : ℤ)⟧
  let T' := ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj LW)
    ⟦(2 : ℤ)⟧
  exact @forward_transport_bundled
    (DerivedCategory (Modules Λ Y))
    (DerivedCategory (Modules Λ (ProjectiveLine Y)))
    (DerivedCategory (Modules Λ (diagonalSurface Y)))
    inferInstance inferInstance inferInstance
    (internalMonoidal Λ Y) (internalMonoidal Λ (ProjectiveLine Y))
    (internalMonoidal Λ (diagonalSurface Y)) F P U₁ U₂ Q
    (nativeSelfSquareExchange Λ (ProjectiveLine Y ↘ Y)
      (firstProjection Y) (secondProjection Y) (square Y)) K T
    ((twist Λ (ProjectiveLine Y) LS).obj (F.obj K)) T'
    ((twist Λ (diagonalSurface Y) LW).obj (U₁.obj (F.obj K)))
    (projectionMap Λ (ProjectiveLine Y ↘ Y) K T)
    (fun N ↦ projectionMap Λ (secondProjection Y) (F.obj K) N)
    (nativeProjectionTensorIso Λ (ProjectiveLine Y ↘ Y) K (P.obj T)).hom
    (secondTraceTensorIso Λ Y K (P.obj T)).inv
    ((ambientPullbackComparison Λ (square Y)).app K)
    (nativeProjectionTensorIso Λ (firstProjection Y) (F.obj K) T) e
    (tensorShiftIso Λ (ProjectiveLine Y) LS (F.obj K))
    (tensorShiftIso Λ (diagonalSurface Y) LW (U₁.obj (F.obj K)))
    (pullTwistIso Λ (firstProjection Y) LS LW e (F.obj K))
    (nativeExchange Λ Y ((twist Λ (ProjectiveLine Y) LS).obj (F.obj K)))
    (secondPretraceExchangeMap Λ Y T)
    (second_tensor_inv Λ Y K (P.obj T))
    (exchange_component Λ Y _).symm
    ((pretrace_native Λ Y T).trans (exchange_component Λ Y T).symm)
    (pull_twist_comparison Λ (firstProjection Y) LS LW e (F.obj K))
    (traceAdjunction Λ (ProjectiveLine Y ↘ Y))
    (traceAdjunction Λ (secondProjection Y))
    (ambientPullbackComparison Λ (square Y))
    (tracePullSquare Λ (ProjectiveLine Y ↘ Y) (firstProjection Y)
      (secondProjection Y) (square Y).w)
    (fun A B ↦ (nativeProjectionTensorIso Λ (ProjectiveLine Y ↘ Y) A B).hom)
    (fun A B ↦ (nativeProjectionTensorIso Λ (firstProjection Y) A B).hom)
    (fun A B ↦ (nativeProjectionTensorIso Λ (secondProjection Y) A B).hom)
    (fixed_projection_transpose Λ (ProjectiveLine Y ↘ Y) K T)
    (fun N ↦ fixed_projection_transpose Λ (secondProjection Y) (F.obj K) N)
    (exchange_trace Λ (ProjectiveLine Y ↘ Y) (firstProjection Y)
      (secondProjection Y) (square Y))
    (comparison_trace Λ (ProjectiveLine Y ↘ Y) (firstProjection Y)
      (secondProjection Y) (square Y))
    (bundled_forward_square Λ (ProjectiveLine Y ↘ Y) (firstProjection Y)
      (secondProjection Y) (square Y)) rfl rfl rfl
    (fixed_naturality Λ (secondProjection Y) (F.obj K) e.hom)

-- Build the definitional comparison by cached heterogeneous congruence.
-- Each step is an ordinary equality proof checked by the kernel. Keeping repeated
-- instance comparisons shared avoids unfolding the native tensor constructions.
open Lean Meta Elab Tactic in
private meta def expandProjection (e : Expr) : MetaM Expr := do
  let .proj n i receiver := e.getAppFn | return e
  let some info := getStructureInfo? (← getEnv) n | return e
  let field := n ++ info.fieldNames[i]!
  return mkAppN (← mkAppM field #[receiver]) e.getAppArgs

open Lean Meta Elab Tactic in
private meta partial def structuralRefl (g : MVarId) (fuel : Nat) :
    StateRefT (ExprMap Expr) MetaM Unit :=
  g.withContext do
    let target ← instantiateMVars (← g.getType)
    if let some proof := (← get).get? target then
      g.assign proof
      return
    let h ← mkFreshExprSyntheticOpaqueMVar target
    structuralReflCore h.mvarId! fuel
    let proof ← instantiateMVars h
    if proof.hasMVar then throwError "incomplete structural congruence"
    modify fun cache => cache.insert target proof
    g.assign proof
where
  structuralReflCore (g : MVarId) (fuel : Nat) :
      StateRefT (ExprMap Expr) MetaM Unit := g.withContext do
    if fuel == 0 then throwError "structural reflexivity exhausted"
    let target ← g.getType
    let (lhs, rhs) ←
      if let some (_, lhs, rhs) := target.eq? then pure (lhs, rhs)
      else if let some (_, lhs, _, rhs) := target.heq? then pure (lhs, rhs)
      else throwError "expected equality"
    if lhs == rhs then
      if target.isHEq then g.assign (← mkHEqRefl lhs)
      else g.assign (← mkEqRefl lhs)
    else if (← isProof lhs) && (← isProof rhs) then
      let proof ← mkAppM ``proof_irrel_heq #[lhs, rhs]
      let proof ← if target.isHEq then pure proof else mkEqOfHEq proof
      g.assign proof
    else if lhs.isLambda && rhs.isLambda then
      let ge ← g.heqOfEq
      let gs ← ge.apply (← mkConstWithFreshMVarLevels ``funext)
      for h in gs do
        let (_, h) ← h.intro1
        structuralRefl h (fuel - 1)
    else if lhs.isApp && lhs.getAppFn == rhs.getAppFn then
      let gh ← g.eqOfHEq
      let ct ← mkHCongrWithArity lhs.getAppFn lhs.getAppNumArgs
      let cp ← abstractProof ct.proof
      let gs ← gh.apply cp { synthAssignedInstances := false }
      for h in gs do structuralRefl h (fuel - 1)
    else
      let lhs' ← expandProjection lhs
      let rhs' ← expandProjection rhs
      let lhs' ← if lhs' == lhs then withTransparency .all (whnf lhs) else pure lhs'
      let rhs' ← if rhs' == rhs then withTransparency .all (whnf rhs) else pure rhs'
      if lhs' == lhs && rhs' == rhs then
        g.refl
      else
        let ty ← if target.isHEq then mkHEq lhs' rhs' else mkEq lhs' rhs'
        let h ← mkFreshExprSyntheticOpaqueMVar ty
        g.assign h
        structuralRefl h.mvarId! (fuel - 1)

open Lean Meta Elab Tactic in
local elab "structural_rfl" : tactic => do
  let _ ← (structuralRefl (← getMainGoal) 100).run {}
  replaceMainGoal []

/-- The extraction composite agrees with the native generic construction. -/
private theorem second_extract_identification
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    (K : DerivedCategory (Modules (coefficient l c).X Y)) :
    secondExtractProjection l c k p hpl Y K =
      nativeSecondExtractProjection (coefficient l c).X Y
        (line l c (ProjectiveLine Y)) (line l c (diagonalSurface Y))
        (firstLineComparisonForTrace l c k p hpl Y) K := by
  structural_rfl

-- Instantiate the abstract transport with the prescribed Tate-line comparisons.
/-- The forward exchange/projection square, before adding an outside Tate factor.
There is no inverse projection, twisted projection, or invertibility assumption. -/
theorem second_exchange_projection_native
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    (K : DerivedCategory (Modules (coefficient l c).X Y)) :
    let Λ := (coefficient l c).X
    let F := moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)
    let R := moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)
    let T := ((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
      (line l c (ProjectiveLine Y))) ⟦(2 : ℤ)⟧
    F.map (projectionMap Λ (ProjectiveLine Y ↘ Y) K T) ≫
        F.map (R.map (tensorShiftIso Λ (ProjectiveLine Y)
          (line l c (ProjectiveLine Y)) (F.obj K)).hom) ≫
        nativeExchange Λ Y
          ((twist Λ (ProjectiveLine Y) (line l c (ProjectiveLine Y))).obj (F.obj K)) =
      (secondTraceTensorIso Λ Y K (R.obj T)).inv ≫
        (F.obj K ◁ secondTraceExchange l c k p hpl Y) ≫
        secondExtractProjection l c k p hpl Y K := by
  unfold secondTraceExchange
  have hExtract := second_extract_identification l c k p hpl Y K
  rw [hExtract]
  exact native_twisted_self_square (coefficient l c).X Y
    (line l c (ProjectiveLine Y)) (line l c (diagonalSurface Y))
    (firstLineComparisonForTrace l c k p hpl Y) K

end AlgebraicGeometry.ProEtale.RationalP1
