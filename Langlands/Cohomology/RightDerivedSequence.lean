import Langlands.Cohomology.DerivedPlusNaturality
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle

/-!
# Long exact sequence of right derived functors

Let `F : C ⥤ D` be an additive functor between abelian categories, where `C` has enough
injectives, and let `S` be a short exact sequence in `C`. Mathlib's distinguished triangle
`S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ S.X₁⟦1⟧` of objects in degree zero lies in the bounded below
derived category. The triangulated functor `F.rightDerivedFunctorPlus` sends it to a
distinguished triangle of derived complexes. Its cohomology sequence, transported along
`DerivedPlus.homologyNatIso`, is the long exact sequence
`⋯ ⟶ R^n F(S.X₁) ⟶ R^n F(S.X₂) ⟶ R^n F(S.X₃) ⟶ R^(n+1) F(S.X₁) ⟶ ⋯`
of the classical right derived functors `F.rightDerived n`.

This file defines the connecting morphisms `rightDerivedδ F hS n₀ n₁ h` for `n₀ + 1 = n₁`.
It proves that consecutive maps compose to zero, exactness at each term, naturality of the
connecting morphisms in morphisms of short exact sequences, and that
`(F.rightDerived 0).map S.f` is a monomorphism.
-/

noncomputable section

namespace Langlands.Cohomology.DerivedPlus

open CategoryTheory CategoryTheory.Limits Pretriangulated

universe w w' v v' u u'

section Single

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
variable {S : ShortComplex C} (hS : S.ShortExact)

/-- The connecting morphism of the triangle of a short exact sequence, in the bounded
below derived category. -/
def singleδPlus : (DerivedCategory.Plus.singleFunctor C 0).obj S.X₃ ⟶
    ((DerivedCategory.Plus.singleFunctor C 0).obj S.X₁)⟦(1 : ℤ)⟧ :=
  DerivedCategory.Plus.ι.preimage (hS.singleδ ≫
    ((DerivedCategory.Plus.ι (C := C)).commShiftIso (1 : ℤ)).inv.app
      ((DerivedCategory.Plus.singleFunctor C 0).obj S.X₁))

/-- The image of `singleδPlus hS` in the derived category. -/
theorem ι_map_singleδPlus :
    DerivedCategory.Plus.ι.map (singleδPlus hS) =
      hS.singleδ ≫ ((DerivedCategory.Plus.ι (C := C)).commShiftIso (1 : ℤ)).inv.app
        ((DerivedCategory.Plus.singleFunctor C 0).obj S.X₁) :=
  Functor.map_preimage _ _

/-- The triangle of a short exact sequence, in the bounded below derived category. -/
def singleTrianglePlus : Triangle (DerivedCategory.Plus C) :=
  Triangle.mk ((DerivedCategory.Plus.singleFunctor C 0).map S.f)
    ((DerivedCategory.Plus.singleFunctor C 0).map S.g) (singleδPlus hS)

set_option backward.isDefEq.respectTransparency false in
/-- The image of `singleTrianglePlus hS` in the derived category is Mathlib's
`hS.singleTriangle`. -/
def ιMapSingleTrianglePlusIso :
    DerivedCategory.Plus.ι.mapTriangle.obj (singleTrianglePlus hS) ≅ hS.singleTriangle :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    ((Category.comp_id _).trans (Category.id_comp _).symm) (by
      change (DerivedCategory.Plus.ι.map (singleδPlus hS) ≫
          ((DerivedCategory.Plus.ι (C := C)).commShiftIso (1 : ℤ)).hom.app
            ((DerivedCategory.Plus.singleFunctor C 0).obj S.X₁)) ≫
          (shiftFunctor (DerivedCategory C) (1 : ℤ)).map (𝟙 _) = 𝟙 _ ≫ hS.singleδ
      refine (Category.assoc _ _ _).trans
        ((congrArg (· ≫ _) (ι_map_singleδPlus hS)).trans ?_)
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (hS.singleδ ≫ ·) ((Iso.inv_hom_id_app_assoc
        ((DerivedCategory.Plus.ι (C := C)).commShiftIso (1 : ℤ))
          ((DerivedCategory.Plus.singleFunctor C 0).obj S.X₁) _).trans
        ((shiftFunctor (DerivedCategory C) (1 : ℤ)).map_id
          (DerivedCategory.Plus.ι.obj
            ((DerivedCategory.Plus.singleFunctor C 0).obj S.X₁))))).trans ?_
      exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- The triangle of a short exact sequence is distinguished in the bounded below derived
category. -/
theorem singleTrianglePlus_distinguished : singleTrianglePlus hS ∈ distTriang _ :=
  isomorphic_distinguished _ hS.singleTriangle_distinguished _ (ιMapSingleTrianglePlusIso hS)

section Map

variable {S₁ S₂ : ShortComplex C} (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂)

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of `singleδPlus` in morphisms of short exact sequences. -/
@[reassoc]
theorem singleδPlus_naturality :
    singleδPlus h₁ ≫ ((DerivedCategory.Plus.singleFunctor C 0).map φ.τ₁)⟦(1 : ℤ)⟧' =
      (DerivedCategory.Plus.singleFunctor C 0).map φ.τ₃ ≫ singleδPlus h₂ := by
  apply DerivedCategory.Plus.ι.map_injective
  have hc : h₁.singleδ ≫ ((DerivedCategory.singleFunctor C 0).map φ.τ₁)⟦(1 : ℤ)⟧' =
      (DerivedCategory.singleFunctor C 0).map φ.τ₃ ≫ h₂.singleδ :=
    (ShortComplex.ShortExact.singleTriangle.map h₁ h₂ φ).comm₃
  have hn := (DerivedCategory.Plus.ι (C := C)).commShiftIso_inv_naturality
    ((DerivedCategory.Plus.singleFunctor C 0).map φ.τ₁) (1 : ℤ)
  rw [Functor.map_comp, Functor.map_comp, ι_map_singleδPlus, ι_map_singleδPlus,
    Category.assoc, ← hn, ← Category.assoc]
  erw [hc]
  rw [Category.assoc]
  rfl

/-- The morphism of triangles `singleTrianglePlus h₁ ⟶ singleTrianglePlus h₂` induced by a
morphism of short exact sequences. -/
def singleTrianglePlusMap : singleTrianglePlus h₁ ⟶ singleTrianglePlus h₂ :=
  Triangle.homMk _ _ ((DerivedCategory.Plus.singleFunctor C 0).map φ.τ₁)
    ((DerivedCategory.Plus.singleFunctor C 0).map φ.τ₂)
    ((DerivedCategory.Plus.singleFunctor C 0).map φ.τ₃)
    (by
      change (DerivedCategory.Plus.singleFunctor C 0).map S₁.f ≫ _ = _ ≫
        (DerivedCategory.Plus.singleFunctor C 0).map S₂.f
      rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₁₂])
    (by
      change (DerivedCategory.Plus.singleFunctor C 0).map S₁.g ≫ _ = _ ≫
        (DerivedCategory.Plus.singleFunctor C 0).map S₂.g
      rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₂₃])
    (singleδPlus_naturality h₁ h₂ φ)

end Map

end Single

section Derived

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  [EnoughInjectives C]
variable {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
variable (F : C ⥤ D) [F.Additive]
variable {S : ShortComplex C} (hS : S.ShortExact)

/-- The triangle of derived complexes attached to a short exact sequence, in the derived
category of `D`. -/
def derivedTriangle : Triangle (DerivedCategory D) :=
  DerivedCategory.Plus.ι.mapTriangle.obj
    (F.rightDerivedFunctorPlus.mapTriangle.obj (singleTrianglePlus hS))

/-- The triangle of derived complexes of a short exact sequence is distinguished. -/
theorem derivedTriangle_distinguished : derivedTriangle F hS ∈ distTriang _ :=
  F.rightDerivedFunctorPlus.map_distinguished _ (singleTrianglePlus_distinguished hS)

/-- The connecting morphism on the cohomology of derived complexes attached to a short
exact sequence `S`, for `n₀ + 1 = n₁`. -/
def derivedδ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (derivedComplex F ⋙ DerivedCategory.Plus.homologyFunctor D n₀).obj S.X₃ ⟶
      (derivedComplex F ⋙ DerivedCategory.Plus.homologyFunctor D n₁).obj S.X₁ :=
  DerivedCategory.HomologySequence.δ (derivedTriangle F hS) n₀ n₁ h

include hS in
/-- Two consecutive maps on the cohomology of derived complexes compose to zero. -/
theorem derived_map_comp_map (n : ℤ) :
    (derivedComplex F ⋙ DerivedCategory.Plus.homologyFunctor D n).map S.f ≫
      (derivedComplex F ⋙ DerivedCategory.Plus.homologyFunctor D n).map S.g = 0 := by
  change (DerivedCategory.homologyFunctor D n).map (derivedTriangle F hS).mor₁ ≫
    (DerivedCategory.homologyFunctor D n).map (derivedTriangle F hS).mor₂ = 0
  rw [← Functor.map_comp, comp_distTriang_mor_zero₁₂ _ (derivedTriangle_distinguished F hS),
    Functor.map_zero]

/-- The map induced by `S.g` followed by the connecting morphism is zero. -/
@[reassoc]
theorem derived_map_comp_δ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (derivedComplex F ⋙ DerivedCategory.Plus.homologyFunctor D n₀).map S.g ≫
      derivedδ F hS n₀ n₁ h = 0 :=
  DerivedCategory.HomologySequence.comp_δ _ (derivedTriangle_distinguished F hS) _ _ h

/-- The connecting morphism followed by the map induced by `S.f` is zero. -/
@[reassoc]
theorem derivedδ_comp_map (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    derivedδ F hS n₀ n₁ h ≫
      (derivedComplex F ⋙ DerivedCategory.Plus.homologyFunctor D n₁).map S.f = 0 :=
  DerivedCategory.HomologySequence.δ_comp _ (derivedTriangle_distinguished F hS) _ _ h

/-- Exactness of the cohomology of derived complexes at the term of `S.X₂`. -/
theorem derived_exact₂ (n : ℤ) :
    (ShortComplex.mk _ _ (derived_map_comp_map F hS n)).Exact :=
  DerivedCategory.HomologySequence.exact₂ _ (derivedTriangle_distinguished F hS) n

/-- Exactness of the cohomology of derived complexes at the term of `S.X₃`. -/
theorem derived_exact₃ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (ShortComplex.mk _ _ (derived_map_comp_δ F hS n₀ n₁ h)).Exact :=
  DerivedCategory.HomologySequence.exact₃ _ (derivedTriangle_distinguished F hS) n₀ n₁ h

/-- Exactness of the cohomology of derived complexes at the term of `S.X₁`. -/
theorem derived_exact₁ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (ShortComplex.mk _ _ (derivedδ_comp_map F hS n₀ n₁ h)).Exact :=
  DerivedCategory.HomologySequence.exact₁ _ (derivedTriangle_distinguished F hS) n₀ n₁ h

/-- The connecting morphism `(F.rightDerived n₀).obj S.X₃ ⟶ (F.rightDerived n₁).obj S.X₁`
of a short exact sequence `S`, for `n₀ + 1 = n₁`. -/
def rightDerivedδ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (F.rightDerived n₀).obj S.X₃ ⟶ (F.rightDerived n₁).obj S.X₁ :=
  (homologyNatIso F n₀).inv.app S.X₃ ≫ derivedδ F hS n₀ n₁ (by omega) ≫
    (homologyNatIso F n₁).hom.app S.X₁

/-- `homologyNatIso` intertwines `derivedδ` and `rightDerivedδ`. -/
@[reassoc]
theorem homologyNatIso_hom_app_comp_rightDerivedδ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (homologyNatIso F n₀).hom.app S.X₃ ≫ rightDerivedδ F hS n₀ n₁ h =
      derivedδ F hS n₀ n₁ (by omega) ≫ (homologyNatIso F n₁).hom.app S.X₁ := by
  rw [rightDerivedδ, Iso.hom_inv_id_app_assoc]

omit [HasDerivedCategory C] [HasDerivedCategory D] in
/-- Right derived functors send zero morphisms to zero morphisms. -/
theorem rightDerived_map_zero (n : ℕ) (X Y : C) :
    (F.rightDerived n).map (0 : X ⟶ Y) = 0 := by
  rw [F.rightDerived_map_eq n 0 (P := injectiveResolution X) (Q := injectiveResolution Y) 0
    (by rw [comp_zero, Functor.map_zero, zero_comp]), Functor.map_zero, zero_comp, comp_zero]

omit [HasDerivedCategory C] [HasDerivedCategory D] in
/-- `(F.rightDerived n).map S.f ≫ (F.rightDerived n).map S.g = 0`. -/
theorem rightDerived_map_comp_map (n : ℕ) :
    (F.rightDerived n).map S.f ≫ (F.rightDerived n).map S.g = 0 := by
  rw [← Functor.map_comp, S.zero, rightDerived_map_zero]

/-- `(F.rightDerived n₀).map S.g` followed by the connecting morphism is zero. -/
@[reassoc]
theorem rightDerived_map_comp_δ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (F.rightDerived n₀).map S.g ≫ rightDerivedδ F hS n₀ n₁ h = 0 := by
  rw [rightDerivedδ, ← Category.assoc, (homologyNatIso F n₀).inv.naturality S.g,
    Category.assoc, ← Category.assoc ((derivedComplex F ⋙ _).map S.g),
    derived_map_comp_δ, zero_comp, comp_zero]

/-- The connecting morphism followed by `(F.rightDerived n₁).map S.f` is zero. -/
@[reassoc]
theorem rightDerivedδ_comp_map (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    rightDerivedδ F hS n₀ n₁ h ≫ (F.rightDerived n₁).map S.f = 0 := by
  rw [rightDerivedδ, Category.assoc, Category.assoc, ← (homologyNatIso F n₁).hom.naturality S.f,
    ← Category.assoc (derivedδ F hS _ _ _), derivedδ_comp_map, zero_comp, comp_zero]

include hS in
/-- Exactness of `R^n F(S.X₁) ⟶ R^n F(S.X₂) ⟶ R^n F(S.X₃)`. -/
theorem rightDerived_exact₂ (n : ℕ) :
    (ShortComplex.mk _ _ (rightDerived_map_comp_map F (S := S) n)).Exact :=
  ShortComplex.exact_of_iso
    (ShortComplex.isoMk ((homologyNatIso F n).app S.X₁) ((homologyNatIso F n).app S.X₂)
      ((homologyNatIso F n).app S.X₃) ((homologyNatIso F n).hom.naturality S.f).symm
      ((homologyNatIso F n).hom.naturality S.g).symm)
    (derived_exact₂ F hS n)

/-- Exactness of `R^n₀ F(S.X₂) ⟶ R^n₀ F(S.X₃) ⟶ R^n₁ F(S.X₁)`. -/
theorem rightDerived_exact₃ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (ShortComplex.mk _ _ (rightDerived_map_comp_δ F hS n₀ n₁ h)).Exact :=
  ShortComplex.exact_of_iso
    (ShortComplex.isoMk ((homologyNatIso F n₀).app S.X₂) ((homologyNatIso F n₀).app S.X₃)
      ((homologyNatIso F n₁).app S.X₁) ((homologyNatIso F n₀).hom.naturality S.g).symm
      (homologyNatIso_hom_app_comp_rightDerivedδ F hS n₀ n₁ h))
    (derived_exact₃ F hS n₀ n₁ (by omega))

/-- Exactness of `R^n₀ F(S.X₃) ⟶ R^n₁ F(S.X₁) ⟶ R^n₁ F(S.X₂)`. -/
theorem rightDerived_exact₁ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (ShortComplex.mk _ _ (rightDerivedδ_comp_map F hS n₀ n₁ h)).Exact :=
  ShortComplex.exact_of_iso
    (ShortComplex.isoMk ((homologyNatIso F n₀).app S.X₃) ((homologyNatIso F n₁).app S.X₁)
      ((homologyNatIso F n₁).app S.X₂)
      (homologyNatIso_hom_app_comp_rightDerivedδ F hS n₀ n₁ h)
      ((homologyNatIso F n₁).hom.naturality S.f).symm)
    (derived_exact₁ F hS n₀ n₁ (by omega))

/-- The connecting morphism is an epimorphism when `R^n₁ F(S.X₂)` is zero. -/
theorem epi_rightDerivedδ_of_isZero (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (h₂ : IsZero ((F.rightDerived n₁).obj S.X₂)) : Epi (rightDerivedδ F hS n₀ n₁ h) :=
  (rightDerived_exact₁ F hS n₀ n₁ h).epi_f (h₂.eq_of_tgt _ _)

/-- The connecting morphism is a monomorphism when `R^n₀ F(S.X₂)` is zero. -/
theorem mono_rightDerivedδ_of_isZero (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (h₂ : IsZero ((F.rightDerived n₀).obj S.X₂)) : Mono (rightDerivedδ F hS n₀ n₁ h) :=
  (rightDerived_exact₃ F hS n₀ n₁ h).mono_g (h₂.eq_of_src _ _)

/-- The connecting morphism is an isomorphism when `R^n₀ F(S.X₂)` and `R^n₁ F(S.X₂)` are
zero. -/
theorem isIso_rightDerivedδ_of_isZero (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (h₂ : IsZero ((F.rightDerived n₀).obj S.X₂)) (h₂' : IsZero ((F.rightDerived n₁).obj S.X₂)) :
    IsIso (rightDerivedδ F hS n₀ n₁ h) :=
  have := epi_rightDerivedδ_of_isZero F hS n₀ n₁ h h₂'
  have := mono_rightDerivedδ_of_isZero F hS n₀ n₁ h h₂
  isIso_of_mono_of_epi _

include hS in
/-- `(F.rightDerived 0).map S.f` is a monomorphism. -/
theorem mono_rightDerived_zero_map : Mono ((F.rightDerived 0).map S.f) := by
  have hz : derivedδ F hS (-1) 0 (by norm_num) = 0 :=
    (isZero_homology_of_neg F S.X₃ (by norm_num)).eq_of_src _ _
  have hm : Mono ((derivedComplex F ⋙ DerivedCategory.Plus.homologyFunctor D ((0 : ℕ) : ℤ)).map
      S.f) :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff _
      (derivedTriangle_distinguished F hS) (-1) 0).2 hz
  have e : (F.rightDerived 0).map S.f = (homologyNatIso F 0).inv.app S.X₁ ≫
      (derivedComplex F ⋙ DerivedCategory.Plus.homologyFunctor D ((0 : ℕ) : ℤ)).map S.f ≫
        (homologyNatIso F 0).hom.app S.X₂ := by
    rw [(homologyNatIso F 0).hom.naturality, Iso.inv_hom_id_app_assoc]
  rw [e]
  infer_instance

include hS in
/-- `(F.rightDerived 0).map S.g` is an epimorphism when `R^1 F(S.X₁)` is zero. -/
theorem epi_rightDerived_zero_map_of_isZero (h₁ : IsZero ((F.rightDerived 1).obj S.X₁)) :
    Epi ((F.rightDerived 0).map S.g) :=
  (rightDerived_exact₃ F hS 0 1 rfl).epi_f (h₁.eq_of_tgt _ _)

include hS in
/-- A left exact functor sends `S` to a short exact sequence when `R^1 F(S.X₁)` is zero. -/
theorem shortExact_map_of_isZero_rightDerived_one [PreservesFiniteLimits F]
    (h₁ : IsZero ((F.rightDerived 1).obj S.X₁)) : (S.map F).ShortExact :=
  ShortComplex.shortExact_of_iso
    (ShortComplex.isoMk (F.rightDerivedZeroIsoSelf.app S.X₁)
      (F.rightDerivedZeroIsoSelf.app S.X₂) (F.rightDerivedZeroIsoSelf.app S.X₃)
      (F.rightDerivedZeroIsoSelf.hom.naturality S.f).symm
      (F.rightDerivedZeroIsoSelf.hom.naturality S.g).symm)
    (ShortComplex.ShortExact.mk' (rightDerived_exact₂ F hS 0) (mono_rightDerived_zero_map F hS)
      (epi_rightDerived_zero_map_of_isZero F hS h₁))

section Map

variable {S₁ S₂ : ShortComplex C} (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂)

/-- Naturality of `derivedδ` in morphisms of short exact sequences. -/
@[reassoc]
theorem derivedδ_naturality (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (derivedComplex F ⋙ DerivedCategory.Plus.homologyFunctor D n₀).map φ.τ₃ ≫
        derivedδ F h₂ n₀ n₁ h =
      derivedδ F h₁ n₀ n₁ h ≫
        (derivedComplex F ⋙ DerivedCategory.Plus.homologyFunctor D n₁).map φ.τ₁ :=
  (DerivedCategory.homologyFunctor D 0).homologySequenceδ_naturality
    (DerivedCategory.Plus.ι.mapTriangle.map
      (F.rightDerivedFunctorPlus.mapTriangle.map (singleTrianglePlusMap h₁ h₂ φ))) n₀ n₁ h

/-- Naturality of the connecting morphisms `rightDerivedδ` in morphisms of short exact
sequences. -/
@[reassoc]
theorem rightDerivedδ_naturality (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    rightDerivedδ F h₁ n₀ n₁ h ≫ (F.rightDerived n₁).map φ.τ₁ =
      (F.rightDerived n₀).map φ.τ₃ ≫ rightDerivedδ F h₂ n₀ n₁ h := by
  simp only [rightDerivedδ, Category.assoc]
  rw [← (homologyNatIso F n₁).hom.naturality φ.τ₁, ← Category.assoc (derivedδ F h₁ _ _ _),
    ← derivedδ_naturality, Category.assoc, ← Category.assoc ((homologyNatIso F n₀).inv.app _),
    ← (homologyNatIso F n₀).inv.naturality φ.τ₃, Category.assoc]

end Map

end Derived

end Langlands.Cohomology.DerivedPlus
