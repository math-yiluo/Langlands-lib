/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module

import WeilConjectures.AlgebraicGeometry.Modules.AffineHom
import WeilConjectures.AlgebraicGeometry.DerivedTensorQCohClosure
import WeilConjectures.AlgebraicGeometry.SelfTorAffineChartSections
import WeilConjectures.AlgebraicGeometry.SelfTorAmbientSectionCoordinates

/-! # Ambient affine self-Tor comparison

Source: Stacks Project, Tags 08DX, 06YG and 00LS.
(blueprint: lem-pc-self-tor-ambient-resolution-charts). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry


private theorem qc_single (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (M : X.Modules) [M.IsQuasicoherent] :
    schemeDerivedQCohProperty X
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M) := by
  intro n
  by_cases hn : n = 0
  · subst n
    let e := (DerivedCategory.singleFunctorCompHomologyFunctorIso
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).app M
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e.symm ‹M.IsQuasicoherent›
  · let e := (DerivedCategory.homologyFunctorFactors
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).app
        ((CochainComplex.singleFunctor _ 0).obj M)
    have hz := HomologicalComplex.isZero_single_obj_homology
      (ComplexShape.up ℤ) 0 M n hn
    have : CategoryTheory.Limits.IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj
          ((DerivedCategory.singleFunctor _ 0).obj M)) :=
      CategoryTheory.Limits.IsZero.of_iso hz e
    let F : SheafOfModules.{u} (moduleRings X.toRingedSpace) :=
      SheafOfModules.free PEmpty.{u+1}
    have hf : CategoryTheory.Limits.IsZero F := by
      rw [CategoryTheory.Limits.IsZero.iff_id_eq_zero]
      apply CategoryTheory.Limits.Sigma.hom_ext
      intro i
      exact PEmpty.elim i
    have hF : F.IsQuasicoherent := inferInstance
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (hf.iso this) hF


private theorem affine_iso_of_section_equiv {X : Scheme.{u}} (U : X.affineOpens)
    (P Q : X.Modules) [(P.restrict U.1.ι).IsQuasicoherent]
    [(Q.restrict U.1.ι).IsQuasicoherent]
    (e : Γ(P, U.1) ≃ₗ[Γ(X, U.1)] Γ(Q, U.1)) :
    ∃ t : P.over U.1 ≅ Q.over U.1,
      ∀ x, t.hom.val.app (op (Over.mk (𝟙 U.1))) x = e x := by
  let V := U.1
  have : IsAffine V.toScheme := U.2
  let e₀ : Γ(P, V.ι ''ᵁ ⊤) ≃ₗ[Γ(X, V.ι ''ᵁ ⊤)] Γ(Q, V.ι ''ᵁ ⊤) :=
    V.ι_image_top.symm ▸ e
  let χ : Γ(P.restrict V.ι, ⊤) ≃ₗ[Γ(V.toScheme, ⊤)] Γ(Q.restrict V.ι, ⊤) :=
    { toFun := e₀
      invFun := e₀.symm
      left_inv := e₀.symm_apply_apply
      right_inv := e₀.apply_symm_apply
      map_add' := e₀.map_add
      map_smul' := fun r x ↦ e₀.map_smul ((V.ι.appIso ⊤).inv r) x }
  obtain ⟨a, ha⟩ := Scheme.Modules.exists_hom_app_top_eq_of_isAffine χ.toLinearMap
  obtain ⟨b, hb⟩ := Scheme.Modules.exists_hom_app_top_eq_of_isAffine χ.symm.toLinearMap
  let t₀ : P.restrict V.ι ≅ Q.restrict V.ι :=
    { hom := a
      inv := b
      hom_inv_id := by
        apply Scheme.Modules.hom_ext_of_isAffine
        intro x
        change b.app ⊤ (a.app ⊤ x) = x
        rw [ha, hb]
        exact χ.symm_apply_apply x
      inv_hom_id := by
        apply Scheme.Modules.hom_ext_of_isAffine
        intro x
        change a.app ⊤ (b.app ⊤ x) = x
        rw [hb, ha]
        exact χ.apply_symm_apply x }
  let E := (Scheme.Modules.overEquiv V).functor
  let eP := (Scheme.Modules.overFunctorEquiv V).app P
  let eQ := (Scheme.Modules.overFunctorEquiv V).app Q
  let t := E.preimageIso (eP ≪≫ t₀ ≪≫ eQ.symm)
  have ht (x : Γ(P, V.ι ''ᵁ ⊤)) :
      t.hom.val.app (op (Over.mk (homOfLE (V.ι_image_le ⊤)))) x = e₀ x := by
    have h := congr(Scheme.Modules.Hom.app
      $(E.map_preimage (eP.hom ≫ a ≫ eQ.inv)) ⊤ x)
    change t.hom.val.app (op (Over.mk (homOfLE (V.ι_image_le ⊤)))) x = a.app ⊤ x at h
    exact h.trans (ha x)
  refine ⟨t, ?_⟩
  have transport (W : X.Opens) (h : W = V) (hWV : W ≤ V)
      (g : Γ(P, W) ≃ₗ[Γ(X, W)] Γ(Q, W)) (hg : g = h.symm ▸ e)
      (hx : ∀ x, t.hom.val.app (op (Over.mk (homOfLE hWV))) x = g x) :
      ∀ x, t.hom.val.app (op (Over.mk (𝟙 V))) x = e x := by
    subst W
    subst g
    exact hx
  exact transport _ V.ι_image_top (V.ι_image_le ⊤) e₀ rfl ht

private theorem selfTor_ambient_isQuasicoherent
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [IsClosedImmersion i] (n : ℕ) :
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let S := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (-(n : ℤ))).obj
        (S.obj B ⊗ S.obj B)).IsQuasicoherent := by
  intro B S
  have : (SheafOfModules.unit Z.ringCatSheaf).IsQuasicoherent :=
    SheafOfModules.isQuasicoherent_unit (R := Z.ringCatSheaf)
  have : B.IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom i _
  exact canonical_derivedTensor_preserve_QCoh Y
    (S.obj B) (S.obj B) (qc_single Y B) (qc_single Y B) (-(n : ℤ))

private theorem affine_iso_of_chart_coordinates {Y : Scheme.{u}} (U : Y.affineOpens)
    (M : ModuleCat.{u} (Γ(Y, U.1) : Type u)) (Q : Y.Modules) [Q.IsQuasicoherent]
    (c : M ≃ₗ[Γ(Y, U.1)] Γ(Q, U.1)) :
    let T := tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom ⋙
      Scheme.Modules.pushforward U.1.ι
    let L := (tilde.functor Γ(Y, U.1)).obj M
    ∃ t : (T.obj M).over U.1 ≅ Q.over U.1, ∀ x,
      t.hom.val.app (op (Over.mk (𝟙 U.1)))
        ((Scheme.Modules.restrictAppIso U.2.isoSpec.hom L (U.1.ι ⁻¹ᵁ U.1)).inv
          (L.val.map (homOfLE le_top).op ((tilde.adjunction.unit.app M) x))) = c x := by
  intro T L
  obtain ⟨d, hD, hd⟩ := exists_selfTor_affine_chart_sections U M
  have : ((T.obj M).restrict U.1.ι).IsQuasicoherent := hD
  have := Scheme.Modules.isQuasicoherent_restrictFunctor U.1.ι Q
  obtain ⟨t, ht⟩ := affine_iso_of_section_equiv U (T.obj M) Q (d.symm.trans c)
  refine ⟨t, fun x ↦ ?_⟩
  rw [← hd x, ht]
  exact congrArg c (d.symm_apply_apply x)

/-- The affine quotient tensor resolutions compute the ambient homology sheaf,
before any pullback to the closed subscheme.
Source: Stacks Project, Tag 08DX(2), Tag 06YG, and Tag 00LS.
(blueprint: lem-pc-self-tor-ambient-resolution-charts).

Proof: Use the natural affine section coordinates provided by
exists_selfTor_ambient_section_coordinates. The pushed-forward closed structure
sheaf is quasi-coherent, since a closed immersion is affine. Its degree-zero
single object has quasi-coherent cohomology: degree zero is the module itself
and every other degree is zero. The canonical derived tensor preserves
quasi-coherent cohomology, so Q and every open restriction of Q are quasi-coherent.

The normalized chart section equivalence identifies the affine model's sections
with algebraic self-Tor and proves quasi-coherence of its restriction to the chart.
Compose its inverse with the ambient section coordinates. On the affine chart,
extend this linear equivalence and its inverse to sheaf morphisms. Affine Hom
extensionality proves that their composites are identities. Transport the
resulting isomorphism through overEquiv; its effect on sections is the prescribed
linear equivalence. This constructs each t U with its normalization, without
assuming the original chart isomorphisms.

For V contained in U, naturality of (t U).hom moves restriction through the
chart isomorphism. Its normalization replaces the top section by c U x. The
ambient section coordinate equation gives c V (q x), and the normalization of
t V gives the required right-hand side. This handles zero modules, empty charts
and degree zero with the same equivalences and naturality equation. -/
theorem exists_selfTor_ambient_resolution_charts
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [IsClosedImmersion i] (n : ℕ) :
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let S := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let Q :=
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (-(n : ℤ))).obj
          (S.obj B ⊗ S.obj B))
    let T := fun U : Y.affineOpens ↦
      tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom ⋙
        Scheme.Modules.pushforward U.1.ι
    let s := fun (U : Y.affineOpens)
      (M : ModuleCat.{u} (Γ(Y, U.1) : Type u)) (x : M) ↦
        let L := (tilde.functor Γ(Y, U.1)).obj M
        (Scheme.Modules.restrictAppIso U.2.isoSpec.hom L
          (U.1.ι ⁻¹ᵁ U.1)).inv
          (L.val.map (homOfLE le_top).op ((tilde.adjunction.unit.app M) x))
    ∃ t : ∀ U : Y.affineOpens,
        ((T U).obj _).over (U.1) ≅ Q.over (U.1),
      ∀ (V U : Y.affineOpens) (h : V.1 ≤ U.1)
        (_hbasic : ∃ f : Γ(Y, U.1), Y.basicOpen f = V.1),
          let A := (Γ(Y, U.1) : Type u)
          let C := (Γ(Y, V.1) : Type u)
          let I := i.ker.ideal U
          let J := i.ker.ideal V
          let φ := (Y.presheaf.map (homOfLE h).op).hom
          let P := projectiveResolution (ModuleCat.of A (A ⧸ I))
          let R := projectiveResolution (ModuleCat.of C (C ⧸ J))
          let TA := (tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex
            (.down ℕ)
          let TC := (tensorRight (ModuleCat.of C (C ⧸ J))).mapHomologicalComplex
            (.down ℕ)
          ∀ (ψ : (A ⧸ I) →+* (C ⧸ J))
            (a : P.complex ⟶ ((ModuleCat.restrictScalars φ).mapHomologicalComplex
              (.down ℕ)).obj R.complex)
            (k : TA.obj P.complex ⟶ ((ModuleCat.restrictScalars φ).mapHomologicalComplex
              (.down ℕ)).obj (TC.obj R.complex)),
            (∀ x : A, ψ (Ideal.Quotient.mk I x) = Ideal.Quotient.mk J (φ x)) →
            (∀ x : P.complex.X 0, R.π.f 0 (a.f 0 x) = ψ (P.π.f 0 x)) →
            (∀ (j : ℕ) (x : P.complex.X j) (y : A ⧸ I),
              k.f j (x ⊗ₜ[A] y) = (show R.complex.X j from a.f j x) ⊗ₜ[C] (ψ y)) →
            let e := ((TC.obj R.complex).sc n).mapHomologyIso
              (ModuleCat.restrictScalars φ)
            let q := fun x ↦
              (R.isoLeftDerivedObj (tensorRight (ModuleCat.of C (C ⧸ J))) n).inv
                (e.hom (HomologicalComplex.homologyMap k n
                  ((P.isoLeftDerivedObj (tensorRight (ModuleCat.of A (A ⧸ I))) n).hom x)))
          ∀ x,
            (t U).hom.val.app (op (Over.mk (homOfLE (h))))
                (((T U).obj _).val.map (homOfLE (h)).op
                  (s U _ x)) =
              (t V).hom.val.app (op (Over.mk (𝟙 (V.1))))
                (s V _ (q x)) := by
  classical
  intro B S Q T s₀
  let M := fun U : Y.affineOpens ↦
    ((tensorRight (ModuleCat.of (Γ(Y, U.1) : Type u)
      ((Γ(Y, U.1) : Type u) ⧸ i.ker.ideal U))).leftDerived n).obj
      (ModuleCat.of (Γ(Y, U.1) : Type u) ((Γ(Y, U.1) : Type u) ⧸ i.ker.ideal U))
  let s := fun (U : Y.affineOpens) (x : M U) ↦ s₀ U (M U) x
  have : Q.IsQuasicoherent := selfTor_ambient_isQuasicoherent i n
  obtain ⟨c, hc⟩ := exists_selfTor_ambient_section_coordinates.{u, w} i n
  choose t ht using fun U ↦ affine_iso_of_chart_coordinates U (M U) Q (c U)
  refine ⟨t, ?_⟩
  intro V U h hbasic A C I J φ P R TA TC ψ a k hψ ha hk e q x
  let f : Over.mk (homOfLE h) ⟶ Over.mk (𝟙 U.1) := Over.homMk (homOfLE h)
  have hn := congr($((t U).hom.val.naturality f.op) (s U x))
  change (t U).hom.val.app (op (Over.mk (homOfLE h)))
      (((T U).obj (M U)).val.map (homOfLE h).op (s U x)) =
    Q.val.map (homOfLE h).op ((t U).hom.val.app (op (Over.mk (𝟙 U.1))) (s U x)) at hn
  rw [ht U x] at hn
  exact hn.trans ((hc V U h hbasic ψ a k hψ ha hk x).trans (ht V _).symm)


end AlgebraicGeometry
