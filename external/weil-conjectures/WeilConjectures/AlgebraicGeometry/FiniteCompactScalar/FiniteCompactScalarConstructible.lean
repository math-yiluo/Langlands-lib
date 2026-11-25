/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteCompactScalar.FiniteCompactSupportScalarTransportData
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleSheaf
import WeilConjectures.AlgebraicGeometry.FiniteCompactScalar.FiniteCompactSupportScalarTransport
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin

/-! # The intrinsic compact scalar mate on bounded constructible inputs

Source: Stacks 0GL6 and 09AL; the compact-support paragraph of
`proposition-six-operations-change-coefficients`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.FiniteCompactScalar

/-- The scalar transpose of the specified compact-support restriction comparison.
Source: Stacks 0GL6 (blueprint: lem-sf-finite-compact-scalar-constructible). -/
def intrinsicCompactScalar
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    sfIntrinsicCompactSupport c A ⋙ pbcDerivedExtend (scalarRingMap φ Y) ⟶
      pbcDerivedExtend (scalarRingMap φ X) ⋙ sfIntrinsicCompactSupport c B :=
  ((mateEquiv (pbcDerivedScalarAdjunction (scalarRingMap φ X))
    (pbcDerivedScalarAdjunction (scalarRingMap φ Y))).symm
      (TwoSquare.mk _ _ _ _ (sfCompactSupportRestriction c φ).hom))

private def scalarTransposeAux
    {C₀ C₁ D₀ D₁ : Type*}
    [Category C₀] [Category C₁] [Category D₀] [Category D₁]
    {Sx : C₀ ⥤ C₁} {Rx : C₁ ⥤ C₀}
    {Sy : D₀ ⥤ D₁} {Ry : D₁ ⥤ D₀}
    (ax : Sx ⊣ Rx) (ay : Sy ⊣ Ry)
    {P₀ : C₀ ⥤ D₀} {P₁ : C₁ ⥤ D₁}
    (r : Rx ⋙ P₀ ⟶ P₁ ⋙ Ry) : P₀ ⋙ Sy ⟶ Sx ⋙ P₁ :=
  ((mateEquiv ax ay).symm (TwoSquare.mk _ _ _ _ r))

set_option backward.isDefEq.respectTransparency true in
private theorem scalarTransposeAux_app
    {C₀ C₁ D₀ D₁ : Type*}
    [Category C₀] [Category C₁] [Category D₀] [Category D₁]
    {Sx : C₀ ⥤ C₁} {Rx : C₁ ⥤ C₀}
    {Sy : D₀ ⥤ D₁} {Ry : D₁ ⥤ D₀}
    (ax : Sx ⊣ Rx) (ay : Sy ⊣ Ry)
    {P₀ : C₀ ⥤ D₀} {P₁ : C₁ ⥤ D₁}
    (r : Rx ⋙ P₀ ⟶ P₁ ⋙ Ry) (K : C₀) :
    (scalarTransposeAux ax ay r).app K =
      (ay.homEquiv _ _).symm (P₀.map (ax.unit.app K) ≫ r.app (Sx.obj K)) := by
  simp only [Functor.comp_obj, Functor.id_obj]
  apply (ay.homEquiv _ _).injective
  erw [Equiv.apply_symm_apply]
  simpa only [Adjunction.homEquiv_unit, scalarTransposeAux, TwoSquare.mk,
    Functor.id_obj, Functor.comp_obj] using
    (unit_mateEquiv_symm ax ay (TwoSquare.mk _ _ _ _ r) K).symm

private theorem intrinsicCompactScalar_app
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : proEtaleDerivedCategory X A) :
    (intrinsicCompactScalar φ c).app K =
      ((pbcDerivedScalarAdjunction (scalarRingMap φ Y)).homEquiv _ _).symm
        ((sfIntrinsicCompactSupport c A).map
            ((pbcDerivedScalarAdjunction (scalarRingMap φ X)).unit.app K) ≫
          (sfCompactSupportRestriction c φ).hom.app
            ((pbcDerivedExtend (scalarRingMap φ X)).obj K)) := by
  exact scalarTransposeAux_app
    (pbcDerivedScalarAdjunction (scalarRingMap φ X))
    (pbcDerivedScalarAdjunction (scalarRingMap φ Y))
    (show pbcDerivedRestrict (scalarRingMap φ X) ⋙ sfIntrinsicCompactSupport c A ⟶
      sfIntrinsicCompactSupport c B ⋙ pbcDerivedRestrict (scalarRingMap φ Y) from
        (sfCompactSupportRestriction c φ).hom) K

private theorem bounded_interval
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (K : DerivedCategory C)
    (h : Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor C i).obj K)}) :
    ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((DerivedCategory.homologyFunctor C i).obj K) := by
  classical
  obtain ⟨a, ha⟩ := h.bddBelow
  obtain ⟨b, hb⟩ := h.bddAbove
  refine ⟨min a b, max a b, min_le_max, ?_⟩
  intro i hi
  by_contra hn
  rcases hi with hi | hi
  · exact (not_lt_of_ge (le_trans (min_le_left _ _) (ha hn))) hi
  · exact (not_lt_of_ge (le_trans (hb hn) (le_max_right _ _))) hi

/-- The actual intrinsic scalar transpose is invertible if its input is bounded
constructible and its scalar extension has bounded cohomology.

Source: Stacks 0GL6 and 09AL; `proposition-six-operations-change-coefficients`, compact-support
paragraph. (blueprint: lem-sf-finite-compact-scalar-constructible).

Proof: the finite-ring essential-image criterion gives a bounded constructible
etale antecedent G. The normalized site/scalar isomorphism identifies the intrinsic
realization of the etale scalar extension of G with the scalar extension of K.
Reflect its cohomological interval through the faithful exact site comparison;
this makes the etale scalar extension bounded below. Regard G and that extension
as objects of D+. The proved intrinsicCompactScalarIsoOfOrigin_hom identifies the
specified transpose at the realization of G with an isomorphism. Naturality at
the antecedent isomorphism transports invertibility to K. Finite cohomological
support includes the zero complex; no flatness of the coefficient map is used. -/
theorem intrinsicCompactScalar_isIso_of_constructible
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    [IsNoetherian c.Z] [IsNoetherian Y]
    (K : proEtaleDerivedCategory X A)
    (hK : Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
        (proEtaleRingModules X (proEtaleConstantRing X A)) i).obj K)})
    (hc : ∀ i : ℤ, IsConstructibleProEtaleModuleSheaf X A
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules X (proEtaleConstantRing X A)) i).obj K))
    (hS : Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
      (proEtaleRingModules X (proEtaleConstantRing X B)) i).obj
        ((pbcDerivedExtend (scalarRingMap φ X)).obj K))}) :
    IsIso ((intrinsicCompactScalar φ c).app K) := by
  classical
  obtain ⟨G, ⟨eG⟩⟩ := ((finiteRing_constructibleDerived_origin X A).2.2.1 K).mpr
    ⟨hc, bounded_interval K hK⟩
  obtain ⟨a, b, hab, hv⟩ := bounded_interval _ hS
  let GB := (Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) X).obj G.obj
  let eS : (ProEtale.finiteCoefficientIntrinsicDerivedComparison X B).obj GB ≅
      (pbcDerivedExtend (scalarRingMap φ X)).obj K :=
    (siteScalarIso φ X).symm.app G.obj ≪≫
      (pbcDerivedExtend (scalarRingMap φ X)).mapIso eG
  have hGB : DerivedCategory.TStructure.t.plus GB := by
    refine ⟨a, (DerivedCategory.isGE_iff GB a).mpr ?_⟩
    intro i hi
    apply ((finiteRing_constructibleDerived_origin X B).2.2.2 GB a b).mpr
      (fun j hj ↦ (hv j hj).of_iso
        ((DerivedCategory.homologyFunctor _ j).mapIso eS)) i (Or.inl hi)
  have hG : DerivedCategory.TStructure.t.plus G.obj := by
    obtain ⟨c, d, _, hvG⟩ := G.property.2
    exact ⟨c, (DerivedCategory.isGE_iff G.obj c).mpr fun i hi ↦ hvG i (Or.inl hi)⟩
  let Gplus : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) :=
    ⟨G.obj, hG⟩
  let GBplus : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} B))) :=
    ⟨GB, hGB⟩
  have hOrigin : IsIso ((intrinsicCompactScalar φ c).app
      ((ProEtale.finiteCoefficientIntrinsicDerivedComparison X A).obj G.obj)) := by
    rw [intrinsicCompactScalar_app,
      intrinsicCompactScalarIsoOfOrigin_hom φ c Gplus GBplus (Iso.refl _)]
    infer_instance
  have hn := (intrinsicCompactScalar φ c).naturality eG.hom
  have hcomp : IsIso
      ((sfIntrinsicCompactSupport c A ⋙ pbcDerivedExtend (scalarRingMap φ Y)).map eG.hom ≫
        (intrinsicCompactScalar φ c).app K) := by
    rw [hn]
    have : IsIso ((intrinsicCompactScalar φ c).app
        (((Etale.DerivedCategory.isBoundedConstructible (ULift.{u + 1, u} A) X).ι ⋙
          ProEtale.finiteCoefficientIntrinsicDerivedComparison X A).obj G)) := hOrigin
    infer_instance
  exact IsIso.of_isIso_comp_left
    ((sfIntrinsicCompactSupport c A ⋙ pbcDerivedExtend (scalarRingMap φ Y)).map eG.hom) _

end AlgebraicGeometry.Scheme.FiniteCompactScalar
