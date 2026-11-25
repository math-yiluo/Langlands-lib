/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
import WeilConjectures.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy
public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy

/-! # Resolution homology square for the identity scheme morphism

Source: Stacks Project, Cohomology of Sheaves, Remark 01FB; Derived Categories, Tag 013S.
(blueprint: lem-weil-pbc-module-cohomology-fmap-identity-resolution-homology).
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

-- Keep extension by zero and resolution descent independent of the concrete module category.
private theorem identity_resolution_homotopy {C : Type*} [Category* C] [Abelian C]
    {G F : C} (ψ : G ⟶ F) (I : InjectiveResolution F) (J : InjectiveResolution G)
    {K : CochainComplex C ℕ} (hK : ∀ n, Injective (K.X n))
    (β : J.cocomplex ⟶ K) (l : I.cocomplex ⟶ K)
    (h : J.ι.f 0 ≫ β.f 0 = ψ ≫ I.ι.f 0 ≫ l.f 0) :
    Nonempty (Homotopy β (InjectiveResolution.desc ψ I J ≫ l)) := by
  let γ := InjectiveResolution.desc ψ I J ≫ l
  have haug : J.ι ≫ β = J.ι ≫ γ := by
    apply HomologicalComplex.from_single_hom_ext
    dsimp only [γ, HomologicalComplex.comp_f]
    rw [← Category.assoc, InjectiveResolution.desc_commutes_zero, Category.assoc]
    exact h
  let : ∀ n, Injective (K.X n) := hK
  let e := ComplexShape.embeddingUpNat
  let E := e.extendFunctor C
  have : QuasiIso (E.map J.ι) :=
    (HomologicalComplex.quasiIso_extendMap_iff J.ι e).2 inferInstance
  have he : Nonempty (Homotopy (E.map J.ι ≫ E.map β) (E.map J.ι ≫ E.map γ)) := by
    rw [← E.map_comp, ← E.map_comp]
    exact ⟨(Homotopy.ofEq haug).extend e⟩
  obtain ⟨hh⟩ := CochainComplex.homotopy_of_comp_quasiIso_of_injective
    (I := K.extend e)
    ⟨0, fun n hn ↦ CochainComplex.isZero_of_isStrictlyGE _ 0 n hn⟩
    (E.map J.ι) (E.map β) (E.map γ) he
  exact ⟨hh.ofExtend⟩

private theorem complex_hom_eq_of_inv_f_comp {C : Type*} [Category* C]
    [Limits.HasZeroMorphisms C] {K L : CochainComplex C ℕ} (a : K ≅ L) (f : K ⟶ L)
    (hf : ∀ n, a.inv.f n ≫ f.f n = 𝟙 _) : f = a.hom := by
  apply (cancel_epi a.inv).1
  rw [a.inv_hom_id]
  apply HomologicalComplex.hom_ext
  intro n
  exact hf n

private theorem resolution_homology_factorization {C A : Type*}
    [Category* C] [Abelian C] [Category* A] [Abelian A]
    (Γ : C ⥤ A) [Γ.Additive] {G F : C} (ψ : G ⟶ F)
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    (P : C ⥤ C) [P.PreservesZeroMorphisms] (η : 𝟭 C ⟶ P)
    (φ : G ⟶ P.obj F) (hφ : φ = ψ ≫ η.app F)
    {K : CochainComplex C ℕ} (hK : ∀ n, Injective (K.X n))
    (l : (P.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex ⟶ K)
    (β : J.cocomplex ⟶ K)
    (a : (Γ.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex ≅
      (Γ.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        ((P.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)) (p : ℕ)
    (haug : J.ι.f 0 ≫ β.f 0 = φ ≫ P.map (I.ι.f 0) ≫ l.f 0)
    (hc : ∀ n, a.inv.f n ≫ Γ.map (η.app (I.cocomplex.X n)) = 𝟙 _) :
    let Γc := Γ.mapHomologicalComplex (ComplexShape.up ℕ)
    let H := HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) p
    H.map (Γc.map β) = H.map (Γc.map (InjectiveResolution.desc ψ I J)) ≫
      H.map (a.hom ≫ Γc.map l) := by
  dsimp only
  let c : I.cocomplex ⟶ (P.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex :=
    (η.mapHomologicalComplex (ComplexShape.up ℕ)).app I.cocomplex
  have haug' : J.ι.f 0 ≫ β.f 0 = ψ ≫ I.ι.f 0 ≫ (c ≫ l).f 0 := by
    rw [haug, hφ]
    dsimp only [c, HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex]
    simpa only [Category.assoc, Functor.id_map, CochainComplex.single₀_obj_zero] using
      congrArg (fun f ↦ ψ ≫ f ≫ l.f 0) (η.naturality (I.ι.f 0)).symm
  have hc' := complex_hom_eq_of_inv_f_comp a
    ((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).map c) hc
  obtain ⟨hh⟩ := identity_resolution_homotopy ψ I J hK β (c ≫ l) haug'
  have hhom := (Γ.mapHomotopy hh).homologyMap_eq p
  change (HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) p).map _ =
    (HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) p).map _ at hhom
  simpa only [Functor.map_comp, hc', Category.assoc] using hhom

private theorem identity_sections_inv {Z : Scheme.{u}} (M : Z.Modules)
    (a : (RingedSpace.globalSectionsFunctor Z.toRingedSpace ⋙
        forget₂ _ AddCommGrpCat.{u}).obj ((pushforward (𝟙 Z)).obj M) ⟶
      (RingedSpace.globalSectionsFunctor Z.toRingedSpace ⋙
        forget₂ _ AddCommGrpCat.{u}).obj M)
    (ha : a = (presheaf M).map
      (eqToHom (by simp) : (⊤ : Z.Opens) ⟶ (𝟙 Z) ⁻¹ᵁ (⊤ : Z.Opens)).op) :
    a ≫ (RingedSpace.globalSectionsFunctor Z.toRingedSpace ⋙ forget₂ _ AddCommGrpCat.{u}).map
      ((pushforwardId Z).inv.app M) = 𝟙 _ := by
  rw [ha]
  change (presheaf M).map _ ≫ ((pushforwardId Z).inv.app M).app ⊤ = 𝟙 _
  simp

-- Identity pushforward and the sections functor require substantial definitional reduction.
set_option backward.isDefEq.respectTransparency.types false in
/-- The horizontal map in the identity-scheme construction factors on sections homology
through the ordinary resolution descent and the vertical comparison. No derived-functor
resolution transports are part of this conclusion.
Source: Stacks Project, Cohomology of Sheaves, Remark 01FB; Derived Categories, Tag 013S.
(blueprint: lem-weil-pbc-module-cohomology-fmap-identity-resolution-homology).

Proof:
1. Let alpha be the ordinary resolution descent of psi from D.J to D.I. The inverse
   pushforward-identity comparison, applied degreewise, identifies D.I with its identity
   pushforward. Follow it by D.lambda to obtain l : D.I.cocomplex ⟶ D.K.
2. The descent augmentation equation and D.compatible imply that D.beta and alpha
   followed by l have equal composites with the augmentation of D.J. The latter is a
   quasi-isomorphism; D.K has injective terms and is bounded below. Extend by zero to
   integer indices and apply uniqueness up to homotopy (013S), then restrict back to
   natural indices. Thus beta and alpha followed by l are homotopic.
3. Apply additive global sections and then homology. This gives H(beta) = H(alpha)H(l).
   The component formula D.sections identifies D.a with global sections of the inverse
   pushforward-identity comparison: both are identity on sections, using the canonical
   restriction along id^{-1}(Z) = Z. Hence sections of l are D.a followed by sections
   of D.lambda. Substitute this equality to get the asserted factorization. The proof
   works for every D, so no independence theorem is needed.
-/
theorem moduleCohomologyFMap_identity_resolution_homology {Z : Scheme.{u}}
    (G F : SheafOfModules.{u} Z.ringCatSheaf) (ψ : G ⟶ F)
    (D : ModuleCohomologyFMapData (𝟙 Z) G F ψ) (p : ℕ) :
    let Γ := RingedSpace.globalSectionsFunctor Z.toRingedSpace ⋙ forget₂ _ AddCommGrpCat.{u}
    let Γc := Γ.mapHomologicalComplex (ComplexShape.up ℕ)
    let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p
    H.map (Γc.map D.β) =
      H.map (Γc.map (InjectiveResolution.desc ψ D.I D.J)) ≫
        H.map (D.a.hom ≫ Γc.map D.lambda) := by
  dsimp only
  let Γ := RingedSpace.globalSectionsFunctor Z.toRingedSpace ⋙ forget₂ _ AddCommGrpCat.{u}
  have : (pushforward (𝟙 Z)).PreservesZeroMorphisms :=
    inferInstanceAs (pushforward (𝟙 Z)).PreservesZeroMorphisms
  refine resolution_homology_factorization Γ ψ D.I D.J (pushforward (𝟙 Z))
    (pushforwardId Z).inv ψ ?_ D.injective D.lambda D.β D.a p D.compatible ?_
  · exact (Category.comp_id ψ).symm
  · intro n
    exact identity_sections_inv (D.I.cocomplex.X n) (D.a.inv.f n) (D.sections n)

end AlgebraicGeometry.Scheme.Modules
