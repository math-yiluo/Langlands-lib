/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CanonicalPullbackTensorComparison
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.GlobalTensorPullbackMatesIsIso
import WeilConjectures.Algebra.Homology.KFlatResolution

/-! # Tensor compatibility of the universal pullback counit

Source: Stacks Project, cohomology.tex, Tag 079U; perfect.tex, Tag 0DJA(1).
(blueprint: lem-pc-tensor-counit-coordinate-equation).
-/

@[expose] public section

universe u w uC vC uD vD
open CategoryTheory CategoryTheory.Limits MonoidalCategory
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
noncomputable section
namespace AlgebraicGeometry

attribute [local instance] SheafOfModules.isGrothendieckAbelian
attribute [local instance] pullbackDescentModuleTensor moduleSymmetric modulePreadditive
  moduleClosed moduleGrothendieck moduleResolutions moduleDerivedMonoidal pullbackDescentQLax

attribute [local instance] Scheme.Modules.globalPullbackMatesColimits

/-- Use the cached small-colimit structure directly for each diagram.
Source: Stacks, Tag 079U (blueprint: lem-pc-tensor-counit-coordinate-equation). -/
local instance tensorCounit_colimit (S : Scheme.{u}) (J : Type) [Category.{0} J]
    (F : J ⥤ SheafOfModules.{u} (moduleRings S.toRingedSpace)) : HasColimit F :=
  ((Scheme.Modules.globalPullbackMatesColimits S).has_colimits_of_shape J).has_colimit F

/-- Tensor total complexes have their defining coproducts.
Source: Stacks, Tag 079U (blueprint: lem-pc-tensor-counit-coordinate-equation). -/
local instance tensorCounit_hasMapBifunctor (S : Scheme.{u})
    (P G : CochainComplex (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ) :
    HomologicalComplex.HasMapBifunctor P G
      (curriedTensor (SheafOfModules.{u} (moduleRings S.toRingedSpace))) (.up ℤ) := by
  intro n
  exact tensorCounit_colimit S _ _

/-- The cochain-complex presentation uses the same total coproducts.
Source: Stacks, Tag 079U (blueprint: lem-pc-tensor-counit-coordinate-equation). -/
local instance tensorCounit_cochainHasMapBifunctor (S : Scheme.{u})
    (P G : CochainComplex (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ) :
    CochainComplex.HasMapBifunctor P G
      (curriedTensor (SheafOfModules.{u} (moduleRings S.toRingedSpace))) :=
  tensorCounit_hasMapBifunctor S P G

private theorem pinnedComparison_natural
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D] [Preadditive C] [Preadditive D]
    [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalPreadditive C] [MonoidalPreadditive D]
    (F : C ⥤ D) [F.Additive]
    (e : ∀ A B : C, F.obj (A ⊗ B) ≅ F.obj A ⊗ F.obj B)
    (he : ∀ (A B A' B' : C) (a : A ⟶ A') (b : B ⟶ B'),
      F.map (a ⊗ₘ b) ≫ (e A' B').hom = (e A B).hom ≫ (F.map a ⊗ₘ F.map b))
    {P0 G0 P G : CochainComplex C ℤ}
    [HomologicalComplex.HasMapBifunctor P0 G0 (curriedTensor C) (.up ℤ)]
    [HomologicalComplex.HasMapBifunctor P G (curriedTensor C) (.up ℤ)]
    [HomologicalComplex.HasMapBifunctor
      ((F.mapHomologicalComplex (.up ℤ)).obj P0)
      ((F.mapHomologicalComplex (.up ℤ)).obj G0) (curriedTensor D) (.up ℤ)]
    [HomologicalComplex.HasMapBifunctor
      ((F.mapHomologicalComplex (.up ℤ)).obj P)
      ((F.mapHomologicalComplex (.up ℤ)).obj G) (curriedTensor D) (.up ℤ)]
    (r : P0 ⟶ P) (s : G0 ⟶ G)
    (ψ : (F.mapHomologicalComplex (.up ℤ)).obj
        (HomologicalComplex.mapBifunctor P0 G0 (curriedTensor C) (.up ℤ)) ≅
      HomologicalComplex.mapBifunctor
        ((F.mapHomologicalComplex (.up ℤ)).obj P0)
        ((F.mapHomologicalComplex (.up ℤ)).obj G0) (curriedTensor D) (.up ℤ))
    (hψ : ∀ (p q n : ℤ) (h : p + q = n),
      F.map (HomologicalComplex.ιMapBifunctor P0 G0 (curriedTensor C) (.up ℤ) p q n h) ≫
          ψ.hom.f n = (e (P0.X p) (G0.X q)).hom ≫
        HomologicalComplex.ιMapBifunctor
          ((F.mapHomologicalComplex (.up ℤ)).obj P0)
          ((F.mapHomologicalComplex (.up ℤ)).obj G0) (curriedTensor D) (.up ℤ) p q n h)
    (φ : (F.mapHomologicalComplex (.up ℤ)).obj
        (HomologicalComplex.mapBifunctor P G (curriedTensor C) (.up ℤ)) ≅
      HomologicalComplex.mapBifunctor
        ((F.mapHomologicalComplex (.up ℤ)).obj P)
        ((F.mapHomologicalComplex (.up ℤ)).obj G) (curriedTensor D) (.up ℤ))
    (hφ : ∀ (p q n : ℤ) (h : p + q = n),
      F.map (HomologicalComplex.ιMapBifunctor P G (curriedTensor C) (.up ℤ) p q n h) ≫
          φ.hom.f n = (e (P.X p) (G.X q)).hom ≫
        HomologicalComplex.ιMapBifunctor
          ((F.mapHomologicalComplex (.up ℤ)).obj P)
          ((F.mapHomologicalComplex (.up ℤ)).obj G) (curriedTensor D) (.up ℤ) p q n h) :
    (F.mapHomologicalComplex (.up ℤ)).map
        (HomologicalComplex.mapBifunctorMap r s (curriedTensor C) (.up ℤ)) ≫ φ.hom =
      ψ.hom ≫ HomologicalComplex.mapBifunctorMap
        ((F.mapHomologicalComplex (.up ℤ)).map r)
        ((F.mapHomologicalComplex (.up ℤ)).map s) (curriedTensor D) (.up ℤ) := by
  apply (cancel_epi ψ.inv).1
  simp only [← Category.assoc, ψ.inv_hom_id, Category.id_comp]
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  apply (cancel_epi
    ((e (P0.X p) (G0.X q)).hom)).1
  simp only [HomologicalComplex.comp_f, ← Category.assoc]
  erw [← hψ p q n hpq]
  have hid : ψ.hom.f n ≫ ψ.inv.f n = 𝟙 _ :=
    congrArg (fun a ↦ a.f n) ψ.hom_inv_id
  simp only [Category.assoc]
  erw [reassoc_of% hid]
  simp only [Functor.mapHomologicalComplex_map_f]
  have ht : HomologicalComplex.ιMapBifunctor P0 G0 (curriedTensor C)
        (.up ℤ) p q n hpq ≫
      (HomologicalComplex.mapBifunctorMap r s (curriedTensor C) (.up ℤ)).f n =
        (r.f p ⊗ₘ s.f q) ≫
          HomologicalComplex.ιMapBifunctor P G (curriedTensor C) (.up ℤ) p q n hpq := by
    simpa only [curriedTensor_map_app, curriedTensor_obj_map, tensorHom_def,
      Category.assoc] using
      HomologicalComplex.ι_mapBifunctorMap r s (curriedTensor C) (.up ℤ) p q n hpq
  erw [← Functor.map_comp_assoc, ht, Functor.map_comp]
  simp only [Category.assoc]
  erw [hφ p q n hpq, reassoc_of% hψ p q n hpq]
  have hv : HomologicalComplex.ιMapBifunctor
        ((F.mapHomologicalComplex (.up ℤ)).obj P0)
        ((F.mapHomologicalComplex (.up ℤ)).obj G0) (curriedTensor D) (.up ℤ) p q n hpq ≫
      (HomologicalComplex.mapBifunctorMap
        ((F.mapHomologicalComplex (.up ℤ)).map r)
        ((F.mapHomologicalComplex (.up ℤ)).map s) (curriedTensor D) (.up ℤ)).f n =
      (((F.mapHomologicalComplex (.up ℤ)).map r).f p ⊗ₘ
        ((F.mapHomologicalComplex (.up ℤ)).map s).f q) ≫
      HomologicalComplex.ιMapBifunctor
        ((F.mapHomologicalComplex (.up ℤ)).obj P)
        ((F.mapHomologicalComplex (.up ℤ)).obj G) (curriedTensor D) (.up ℤ) p q n hpq := by
    simpa only [curriedTensor_map_app, curriedTensor_obj_map, tensorHom_def,
      Category.assoc] using
      HomologicalComplex.ι_mapBifunctorMap
        ((F.mapHomologicalComplex (.up ℤ)).map r)
        ((F.mapHomologicalComplex (.up ℤ)).map s) (curriedTensor D) (.up ℤ) p q n hpq
  erw [hv]
  simp only [Functor.mapHomologicalComplex_map_f]
  simpa only [Category.assoc] using
    congrArg (fun a ↦ a ≫ HomologicalComplex.ιMapBifunctor
      ((F.mapHomologicalComplex (.up ℤ)).obj P)
      ((F.mapHomologicalComplex (.up ℤ)).obj G) (curriedTensor D) (.up ℤ) p q n hpq)
      (he (P0.X p) (G0.X q) (P.X p) (G.X q) (r.f p) (s.f q))


private theorem modelMap_natural
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (X : Scheme.{u})
    (P G P' G' : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (r : P ⟶ P') (s : G ⟶ G') :
    let := SheafOfModules.monoidalCategory X.sheaf
    let := SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
    let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf
    (DerivedCategory.Q.map r ⊗ₘ DerivedCategory.Q.map s) ≫
        pullbackTensorModelMap X P' G' =
      pullbackTensorModelMap X P G ≫ DerivedCategory.Q.map
        (HomologicalComplex.mapBifunctorMap r s (curriedTensor _) (.up ℤ)) := by
  let := pullbackDescentModuleTensor X
  let := moduleSymmetric X
  let := modulePreadditive X
  let := moduleClosed X
  let := moduleGrothendieck X
  let := moduleResolutions X
  let := moduleDerivedMonoidal X
  let := pullbackDescentQLax X
  exact Functor.LaxMonoidal.μ_natural DerivedCategory.Q r s

private theorem tensorCounit_counit_natural
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X T : Scheme.{u}} (k : T ⟶ X)
    (A B : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (a : A ⟶ B) :
    (derivedPullback k).map (DerivedCategory.Q.map a) ≫
        (SingleComplexBaseChange.counit k).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj B) =
      (SingleComplexBaseChange.counit k).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj A) ≫
        DerivedCategory.Q.map
          (((Scheme.Modules.tensorPullback k).mapHomologicalComplex (.up ℤ)).map a) :=
  (SingleComplexBaseChange.counit k).naturality
    ((HomotopyCategory.quotient _ (.up ℤ)).map a)

private theorem tensorCounit_resolution_transfer
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [MonoidalCategory C] [MonoidalCategory D] {L : C ⥤ D}
    {A₀ A B₀ B U₀ U : C} {A₀' A' B₀' B' W₀ W V₀ V : D}
    {r : A₀ ⟶ A} {s : B₀ ⟶ B} {t : U₀ ⟶ U}
    {r' : A₀' ⟶ A'} {s' : B₀' ⟶ B'} {t' : W₀ ⟶ W} {v : V₀ ⟶ V}
    {μ₀ : A₀ ⊗ B₀ ⟶ U₀} {μ : A ⊗ B ⟶ U}
    {ε₀ : L.obj U₀ ⟶ W₀} {ε : L.obj U ⟶ W}
    {φ₀ : W₀ ⟶ V₀} {φ : W ⟶ V}
    {τ₀ : L.obj (A₀ ⊗ B₀) ⟶ L.obj A₀ ⊗ L.obj B₀}
    {τ : L.obj (A ⊗ B) ⟶ L.obj A ⊗ L.obj B}
    {εA₀ : L.obj A₀ ⟶ A₀'} {εA : L.obj A ⟶ A'}
    {εB₀ : L.obj B₀ ⟶ B₀'} {εB : L.obj B ⟶ B'}
    {ν₀ : A₀' ⊗ B₀' ⟶ V₀} {ν : A' ⊗ B' ⟶ V}
    [Epi (L.map (r ⊗ₘ s))]
    (hμ : (r ⊗ₘ s) ≫ μ = μ₀ ≫ t)
    (hε : L.map t ≫ ε = ε₀ ≫ t')
    (hφ : t' ≫ φ = φ₀ ≫ v)
    (hτ : L.map (r ⊗ₘ s) ≫ τ = τ₀ ≫ (L.map r ⊗ₘ L.map s))
    (hA : L.map r ≫ εA = εA₀ ≫ r')
    (hB : L.map s ≫ εB = εB₀ ≫ s')
    (hν : (r' ⊗ₘ s') ≫ ν = ν₀ ≫ v)
    (heq : L.map μ₀ ≫ ε₀ ≫ φ₀ = τ₀ ≫ (εA₀ ⊗ₘ εB₀) ≫ ν₀) :
    L.map μ ≫ ε ≫ φ = τ ≫ (εA ⊗ₘ εB) ≫ ν := by
  apply (cancel_epi (L.map (r ⊗ₘ s))).1
  rw [← Functor.map_comp_assoc, hμ, Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hε, hφ, reassoc_of% hτ]
  rw [tensorHom_comp_tensorHom_assoc, hA, hB, ← tensorHom_comp_tensorHom_assoc, hν]
  exact (reassoc_of% heq) v

/-- The shared pullback counit is compatible with the localization tensor maps,
without a K-flatness assumption on either argument. The chain comparison is
specified on every tensor summand, so its underlying map is uniquely determined.

Source: Stacks Project, cohomology.tex, Tag 079U; perfect.tex, Tag 0DJA(1).
Proof: first suppose both complexes are K-flat. The canonical comparison predicate
supplies a chain isomorphism and its coordinate equation. The prescribed equations
on the coproduct summands determine the chain map uniquely: apply the inverse of
one comparison and check the resulting endomorphism on every tensor summand. The
invertible module tensor comparison cancels, giving the identity on each summand.
Thus that coordinate equation holds for the specified comparison.
For arbitrary P and G, choose K-flat resolutions P0 -> P and G0 -> G, as in Stacks
06YS. Their images under Q are isomorphisms. The localization tensor map is natural
in both factors. Pullback of the total tensor complex has the chain comparison
specified by the module tensor isomorphisms; its summand equations and module
naturality show that it too is natural in both factors. Naturality of the shared
counit applies to the tensor resolution map and to each separate resolution map.
Write r:P0 -> P, s:G0 -> G, t=Tot(r tensor s), and
v=Tot(k*r tensor k*s). For the comparison phi0 at P0,G0, the summand equations give
k*(t);phi = phi0;v. Put d=Lk*(Qr tensor Qs). Naturality of the localization map
and of the counit gives
  d;Lk*(mu(P,G));epsilon(H);Q(phi)
    = Lk*(mu(P0,G0));epsilon(H0);Q(phi0);Q(v).
Naturality of tau, the two factor counits, and the target localization map gives
  d;tau(QP,QG);(epsilon(P) tensor epsilon(G));mu(k*P,k*G)
    = tau(QP0,QG0);(epsilon(P0) tensor epsilon(G0));mu(k*P0,k*G0);Q(v).
The right sides agree by the K-flat equation. Since Qr and Qs are isomorphisms,
d is an isomorphism and cancels. No quasi-isomorphism assumption on either ordinary
pulled-back resolution map is used. This gives the displayed equation.
(blueprint: lem-pc-tensor-counit-coordinate-equation). -/
theorem tensorCounit_coordinateEquation
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X T : Scheme.{u}} (k : T ⟶ X)
    [@MonoidalPreadditive _ _ _ (SheafOfModules.monoidalCategory X.sheaf)]
    (P G : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (τ : ∀ A B : schemeDerivedCategory X,
      (derivedPullback k).obj (A ⊗ B) ⟶
        (derivedPullback k).obj A ⊗ (derivedPullback k).obj B)
    (hτ : IsCanonicalPullbackTensorComparison k τ) :
    letI := SheafOfModules.monoidalCategory X.sheaf
    letI := SheafOfModules.monoidalCategory T.sheaf
    letI := Classical.choice (SheafOfModules.tensorClosed T.sheaf).1
    letI := SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
    letI := SheafOfModules.preservesZeroMorphisms_curriedTensor T.sheaf
    letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf
    letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj T.sheaf
    ∀ φ : ((Scheme.Modules.tensorPullback k).mapHomologicalComplex (.up ℤ)).obj
        (pullbackTensorTotal X P G) ≅
      pullbackTensorTotal T
        (((Scheme.Modules.tensorPullback k).mapHomologicalComplex (.up ℤ)).obj P)
        (((Scheme.Modules.tensorPullback k).mapHomologicalComplex (.up ℤ)).obj G),
      (∀ (p q n : ℤ) (h : p + q = n),
        (Scheme.Modules.tensorPullback k).map
            (HomologicalComplex.ιMapBifunctor P G (curriedTensor _) (.up ℤ) p q n h) ≫
          φ.hom.f n =
        ((Classical.choose (Scheme.Modules.module_pullback_tensor k)) (P.X p) (G.X q)).hom ≫
          HomologicalComplex.ιMapBifunctor
            (((Scheme.Modules.tensorPullback k).mapHomologicalComplex (.up ℤ)).obj P)
            (((Scheme.Modules.tensorPullback k).mapHomologicalComplex (.up ℤ)).obj G)
            (curriedTensor (SheafOfModules.{u} (moduleRings T.toRingedSpace)))
            (.up ℤ) p q n h) →
      (derivedPullback k).map (pullbackTensorModelMap X P G) ≫
          cast (by rfl) ((SingleComplexBaseChange.counit k).app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj (pullbackTensorTotal X P G))) ≫
          DerivedCategory.Q.map φ.hom =
        τ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj G) ≫
          cast (by rfl) ((SingleComplexBaseChange.counit k).app
              ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ⊗ₘ
            (SingleComplexBaseChange.counit k).app
              ((HomotopyCategory.quotient _ (.up ℤ)).obj G)) ≫
          pullbackTensorModelMap T
            (((Scheme.Modules.tensorPullback k).mapHomologicalComplex (.up ℤ)).obj P)
            (((Scheme.Modules.tensorPullback k).mapHomologicalComplex (.up ℤ)).obj G) := by
  classical
  dsimp only
  let := pullbackDescentModuleTensor X
  let := pullbackDescentModuleTensor T
  let := modulePreadditive X
  let := modulePreadditive T
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor T.sheaf
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj T.sheaf
  have : (curriedTensor T.Modules).PreservesZeroMorphisms :=
    SheafOfModules.preservesZeroMorphisms_curriedTensor T.sheaf
  have (M : T.Modules) : ((curriedTensor T.Modules).obj M).PreservesZeroMorphisms :=
    SheafOfModules.preservesZeroMorphisms_curriedTensor_obj T.sheaf M
  intro φ hφ
  obtain ⟨P0, r, hP0, _, hr, _⟩ :=
    CochainComplex.exists_isKFlatResolution (R := X.sheaf) P
  obtain ⟨G0, s, hG0, _, hs, _⟩ :=
    CochainComplex.exists_isKFlatResolution (R := X.sheaf) G
  have : QuasiIso r := hr
  have : QuasiIso s := hs
  dsimp only [IsCanonicalPullbackTensorComparison] at hτ
  obtain ⟨ψ, hψ, heq⟩ := hτ.1 P0 G0 hP0 hG0
  have : (Scheme.Modules.tensorPullback k).Additive :=
    SingleComplexBaseChange.tensorPullbackAdditive.{u, w} k
  let F := (Scheme.Modules.tensorPullback k).mapHomologicalComplex (.up ℤ)
  let t : pullbackTensorTotal X P0 G0 ⟶ pullbackTensorTotal X P G :=
    HomologicalComplex.mapBifunctorMap r s
      (curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace))) (.up ℤ)
  let v : pullbackTensorTotal T (F.obj P0) (F.obj G0) ⟶
      pullbackTensorTotal T (F.obj P) (F.obj G) :=
    HomologicalComplex.mapBifunctorMap (F.map r) (F.map s)
      (curriedTensor (SheafOfModules.{u} (moduleRings T.toRingedSpace))) (.up ℤ)
  have hchain : F.map t ≫ φ.hom = ψ.hom ≫ v :=
    pinnedComparison_natural
      (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))
      (D := SheafOfModules.{u} (moduleRings T.toRingedSpace))
      (Scheme.Modules.tensorPullback k)
      (Classical.choose (Scheme.Modules.module_pullback_tensor k))
      (Classical.choose_spec (Scheme.Modules.module_pullback_tensor k)).1 r s ψ hψ φ hφ
  have hε (A B : CochainComplex
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) (a : A ⟶ B) :
      (derivedPullback k).map (DerivedCategory.Q.map a) ≫
          (SingleComplexBaseChange.counit k).app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj B) =
        (SingleComplexBaseChange.counit k).app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj A) ≫
          DerivedCategory.Q.map (F.map a) :=
    tensorCounit_counit_natural k A B a
  simp only [cast_eq] at heq ⊢
  exact tensorCounit_resolution_transfer
    (modelMap_natural X P0 G0 P G r s)
    (hε _ _ t)
    (by simpa only [Functor.map_comp] using
      congrArg (fun f ↦ (DerivedCategory.Q.{w}
        (C := SheafOfModules.{u} (moduleRings T.toRingedSpace))).map f) hchain)
    (hτ.2 _ _ _ _ (DerivedCategory.Q.map r) (DerivedCategory.Q.map s))
    (hε _ _ r) (hε _ _ s)
    (modelMap_natural T (F.obj P0) (F.obj G0) (F.obj P) (F.obj G) (F.map r) (F.map s))
    heq


end AlgebraicGeometry
