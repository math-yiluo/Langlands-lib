/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AlternatingCechTotalComplex
public import WeilConjectures.AlgebraicGeometry.Coherent
import WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns
import WeilConjectures.AlgebraicGeometry.AffineOpenSectionsResolutionQuasiIso
import Mathlib.Algebra.Category.ModuleCat.Products
import WeilConjectures.Algebra.Homology.KInjectiveRestrictOpen
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
import WeilConjectures.AlgebraicGeometry.QCohAcyclicDerivedSectionsComparison

/-! # Čech totalization of a quasi-coherent resolution

Source: Stacks Project, Cohomology, Lemma 08C2.
(blueprint: lem-sc-qcoh-alternating-cech-resolution-quasi-iso)
-/

@[expose] public section

universe u


open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private def alternatingCechTermsProjection
    {X : Scheme.{u}} {r : ℕ} (U : Fin r → X.Opens)
    (G : X.Opensᵒᵖ ⥤ ModuleCat.{u}
      ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
    (k : ℕ) (t : Fin (k + 1) ↪o Fin r) :
    alternatingCechTerms U G k ⟶ G.obj (op (alternatingCechIntersection U t)) :=
  ModuleCat.ofHom (LinearMap.proj t)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def alternatingCechColumnProjection
    {X : Scheme.{u}} {r : ℕ} (U : Fin r → X.Opens)
    (F : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (k : ℕ) (t : Fin (k + 1) ↪o Fin r) :
    (((alternatingCechDoubleFunctor U).obj F).X (k : ℤ)) ⟶
      (((alternatingCechModulePresheaf (X := X) ⋙
        (CategoryTheory.evaluation X.Opensᵒᵖ
          (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))).obj
            (op (alternatingCechIntersection U t))).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj F) where
  f n := (HomologicalComplex.extendXIso
      (alternatingCechComplex U ((alternatingCechModulePresheaf (X := X)).obj (F.X n)))
        ComplexShape.embeddingUpNat (i := k) rfl).hom ≫
    alternatingCechTermsProjection U
      ((alternatingCechModulePresheaf (X := X)).obj (F.X n)) k t
  comm' n m _ := by
    change _ = (HomologicalComplex.extendMap
      (alternatingCechComplexMap U ((alternatingCechModulePresheaf (X := X)).map
        (F.d n m))) ComplexShape.embeddingUpNat).f (k : ℤ) ≫ _
    erw [HomologicalComplex.extendMap_f _ _ (i := k) rfl]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rfl

set_option backward.isDefEq.respectTransparency false in
private theorem alternatingCechColumnProjection_isIso
    {X : Scheme.{u}} {r : ℕ} (U : Fin r → X.Opens)
    (F : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (k : ℕ) :
    IsIso (Limits.Pi.lift (alternatingCechColumnProjection U F k)) := by
  classical
  suffices h : ∀ n, IsIso ((Limits.Pi.lift
      (alternatingCechColumnProjection U F k)).f n) from
    by
      have := h
      exact HomologicalComplex.Hom.isIso_of_components _
  intro n
  let C := ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))
  let E := HomologicalComplex.eval C (ComplexShape.up ℤ) n
  let P := fun t : Fin (k + 1) ↪o Fin r ↦
    (((alternatingCechModulePresheaf (X := X) ⋙
      (CategoryTheory.evaluation X.Opensᵒᵖ C).obj
        (op (alternatingCechIntersection U t))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj F)
  let e := HomologicalComplex.extendXIso
    (alternatingCechComplex U ((alternatingCechModulePresheaf (X := X)).obj (F.X n)))
      ComplexShape.embeddingUpNat (i := k) rfl
  have he : (Limits.Pi.lift (alternatingCechColumnProjection U F k)).f n ≫
      piComparison E P = e.hom ≫ (ModuleCat.piIsoPi (fun t ↦ (P t).X n)).inv := by
    apply Limits.Pi.hom_ext
    intro t
    simp only [Category.assoc, piComparison_comp_π]
    change ((Limits.Pi.lift (alternatingCechColumnProjection U F k)) ≫
      Limits.Pi.π P t).f n = _
    rw [Limits.Pi.lift_comp_π]
    erw [ModuleCat.piIsoPi_inv_kernel_ι]
    rfl
  have : IsIso ((Limits.Pi.lift (alternatingCechColumnProjection U F k)).f n ≫
      piComparison E P) := by
    rw [he]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (piComparison E P)

-- Explicit product comparisons require additional elaboration of the composite functors.
set_option backward.isDefEq.respectTransparency false in
private theorem alternatingCechColumn_quasiIso
    {X : Scheme.{u}} {r : ℕ} (U : Fin r → X.Opens)
    (hAffine : ∀ (p : ℕ) (t : Fin (p + 1) → Fin r), IsAffineOpen (⨅ k, U (t k)))
    (F J : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hF : ∀ n : ℤ, (F.X n).IsQuasicoherent)
    [J.IsKInjective] (i : F ⟶ J) [QuasiIso i] (k : ℕ) :
    QuasiIso (((alternatingCechDoubleFunctor U).map i).f (k : ℤ)) := by
  classical
  let C := ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))
  let S := fun t : Fin (k + 1) ↪o Fin r ↦
    (alternatingCechModulePresheaf (X := X) ⋙
      (CategoryTheory.evaluation X.Opensᵒᵖ C).obj
        (op (alternatingCechIntersection U t))).mapHomologicalComplex (ComplexShape.up ℤ)
  let P := fun t ↦ (S t).obj F
  let Q := fun t ↦ (S t).obj J
  let a := fun t ↦ (S t).map i
  have (t : Fin (k + 1) ↪o Fin r) : QuasiIso (a t) :=
    affineOpenSections_resolution_quasiIso X (alternatingCechIntersection U t)
      (hAffine k t) F J hF i
  have hprod : QuasiIso (Limits.Pi.map a) := by
    rw [quasiIso_iff]
    intro n
    rw [quasiIsoAt_iff_isIso_homologyMap]
    let H := HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n
    have (t : Fin (k + 1) ↪o Fin r) : IsIso (H.map (a t)) := by
      exact (quasiIsoAt_iff_isIso_homologyMap (a t) n).mp inferInstance
    have he : H.map (Limits.Pi.map a) ≫ piComparison H Q =
        piComparison H P ≫ Limits.Pi.map (fun t ↦ H.map (a t)) := by
      apply Limits.Pi.hom_ext
      intro t
      simp only [Category.assoc, piComparison_comp_π]
      erw [Limits.Pi.map_π]
      rw [← H.map_comp, Limits.Pi.map_π, H.map_comp]
      erw [piComparison_comp_π_assoc]
    change IsIso (H.map (Limits.Pi.map a))
    have : IsIso (H.map (Limits.Pi.map a) ≫ piComparison H Q) := by
      rw [he]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (piComparison H Q)
  have := alternatingCechColumnProjection_isIso U F k
  have := alternatingCechColumnProjection_isIso U J k
  have hcomm : ((alternatingCechDoubleFunctor U).map i).f (k : ℤ) ≫
      Limits.Pi.lift (alternatingCechColumnProjection U J k) =
        Limits.Pi.lift (alternatingCechColumnProjection U F k) ≫ Limits.Pi.map a := by
    apply Limits.Pi.hom_ext
    intro t
    simp only [Category.assoc, Limits.Pi.lift_comp_π]
    erw [Limits.Pi.map_π, Limits.Pi.lift_comp_π_assoc]
    apply HomologicalComplex.hom_ext
    intro n
    change (HomologicalComplex.extendMap
      (alternatingCechComplexMap U ((alternatingCechModulePresheaf (X := X)).map
        (i.f n))) ComplexShape.embeddingUpNat).f (k : ℤ) ≫ _ = _
    erw [HomologicalComplex.extendMap_f _ _ (i := k) rfl]
    dsimp only [alternatingCechColumnProjection, HomologicalComplex.comp_f]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rfl
  have : QuasiIso (((alternatingCechDoubleFunctor U).map i).f (k : ℤ) ≫
      Limits.Pi.lift (alternatingCechColumnProjection U J k)) := by
    rw [hcomm]
    infer_instance
  exact (quasiIso_iff_comp_right _
    (Limits.Pi.lift (alternatingCechColumnProjection U J k))).mp inferInstance

set_option backward.isDefEq.respectTransparency false in
private theorem alternatingCechDouble_isZero_column
    {X : Scheme.{u}} {r : ℕ} (U : Fin r → X.Opens)
    (F : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (p : ℤ) (hp : p < 0 ∨ (r : ℤ) ≤ p) :
    IsZero (((alternatingCechDoubleFunctor U).obj F).X p) := by
  rw [IsZero.iff_id_eq_zero]
  apply HomologicalComplex.hom_ext
  intro n
  apply (show IsZero ((((alternatingCechDoubleFunctor U).obj F).X p).X n) from ?_).eq_of_src
  change IsZero (((alternatingCechModuleFunctor U).obj (F.X n)).X p)
  change IsZero (((alternatingCechComplex U
    ((alternatingCechModulePresheaf (X := X)).obj (F.X n))).extend
      ComplexShape.embeddingUpNat).X p)
  rcases hp with hp | hp
  · apply HomologicalComplex.isZero_extend_X
    intro k
    change (k : ℤ) ≠ p
    omega
  · have hnonneg : 0 ≤ p := le_trans (by omega) hp
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hnonneg
    apply IsZero.of_iso _ (HomologicalComplex.extendXIso _
      ComplexShape.embeddingUpNat (i := k) rfl)
    change IsZero (alternatingCechTerms U
      ((alternatingCechModulePresheaf (X := X)).obj (F.X n)) k)
    have : IsEmpty (Fin (k + 1) ↪o Fin r) := ⟨fun t ↦ by
      have ht := Fintype.card_le_of_injective t t.injective
      simp only [Fintype.card_fin] at ht
      omega⟩
    unfold alternatingCechTerms
    exact ModuleCat.isZero_of_subsingleton _

set_option backward.isDefEq.respectTransparency false in
private theorem alternatingCechDouble_strictlyGE
    {X : Scheme.{u}} {r : ℕ} (U : Fin r → X.Opens)
    (F : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    CochainComplex.IsStrictlyGE ((alternatingCechDoubleFunctor U).obj F) 0 := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro p hp
  exact alternatingCechDouble_isZero_column U F p (Or.inl hp)

set_option backward.isDefEq.respectTransparency false in
private theorem alternatingCechDouble_strictlyLE
    {X : Scheme.{u}} {r : ℕ} (U : Fin r → X.Opens)
    (F : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    CochainComplex.IsStrictlyLE ((alternatingCechDoubleFunctor U).obj F) ((r : ℤ) - 1) := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro p hp
  exact alternatingCechDouble_isZero_column U F p (Or.inr (by omega))

/-- Čech totalization sends a quasi-coherent complex's K-injective resolution to a
quasi-isomorphism, without boundedness of the coefficient complex.

Source: Stacks Project, Cohomology, Lemma 08C2, affine-basis application using Tag 01XB.
(blueprint: lem-sc-qcoh-alternating-cech-resolution-quasi-iso).

Proof: Apply the affine-open section comparison to every increasing tuple
intersection. Project the actual extended column to its tuple section complexes;
the product of these projections is an isomorphism by the degreewise product
comparison and extensionXIso. Finite products preserve quasi-isomorphisms because
the additive homology functor preserves finite products. Naturality of the
projections therefore makes every nonnegative column map a quasi-isomorphism.
Negative columns vanish by extension by zero. For p at least r there are no
increasing (p+1)-tuples: injectivity would force p+1 at most r. Thus the double
complexes are strictly supported in columns 0 through r-1. Apply the existing
HomologicalComplex₂.total.quasiIso_map_of_finitely_many_columns, without any
boundedness in coefficient degree. The empty interval for r=0 is included.
The cover hypothesis is retained in the unchanged signature; the proof in fact
uses only affineness of the intersections. -/
theorem qcoh_alternatingCech_resolution_quasiIso
    (X : Scheme.{u}) (r : ℕ) (U : Fin r → X.Opens) (hU : iSup U = ⊤)
    (hAffine : ∀ (p : ℕ) (t : Fin (p + 1) → Fin r), IsAffineOpen (⨅ k, U (t k)))
    (F J : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hF : ∀ n : ℤ, (F.X n).IsQuasicoherent)
    [J.IsKInjective] (i : F ⟶ J) [QuasiIso i] :
    QuasiIso ((alternatingCechTotalFunctor U).map i) := by
  have _ := hU
  have := alternatingCechDouble_strictlyGE U F
  have := alternatingCechDouble_strictlyLE U F
  have := alternatingCechDouble_strictlyGE U J
  have := alternatingCechDouble_strictlyLE U J
  change QuasiIso (HomologicalComplex₂.total.map
    ((alternatingCechDoubleFunctor U).map i) (ComplexShape.up ℤ))
  apply HomologicalComplex₂.total.quasiIso_map_of_finitely_many_columns
    _ 0 ((r : ℤ) - 1)
  intro p hp _
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hp
  exact alternatingCechColumn_quasiIso U hAffine F J hF i k

end AlgebraicGeometry
