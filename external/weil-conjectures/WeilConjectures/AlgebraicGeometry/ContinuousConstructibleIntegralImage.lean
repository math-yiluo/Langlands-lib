/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
import WeilConjectures.AlgebraicGeometry.IntegralConstructibleSerre
import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralDenominators

/-! # Triangulated closure of the integral scalar-extension image

Source: Bhatt--Scholze, Lemma 6.8.12 and the full-faithfulness argument after localization
in Proposition 6.8.14(2). No full faithfulness of the integral functor is asserted.
(auxiliary; not a blueprint node)
-/

@[expose] public section

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory

universe u

open CategoryTheory
open scoped CategoryTheory.Obj CategoryTheory.Functor

open CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.MonoidalCategory CategoryTheory.MonObj CategoryTheory.Preadditive
open scoped ZeroObject

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem essImage_triangulated_of_arrow_lifting
    {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D]
    [HasShift C ℤ] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D]
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    (hF : ∀ (A B : C) (f : F.obj A ⟶ F.obj B),
      ∃ (g : A ⟶ B) (e : F.obj A ≅ F.obj A), e.hom ≫ f = F.map g) :
    F.essImage.IsTriangulated := by
  have hs : F.essImage.IsStableUnderShift ℤ :=
    { isStableUnderShiftBy := fun n ↦
        { le_shift := by
            rintro Y ⟨A, ⟨e⟩⟩
            exact ⟨A⟦n⟧, ⟨(F.commShiftIso n).app A ≪≫ (shiftFunctor D n).mapIso e⟩⟩ } }
  have hz : F.essImage.ContainsZero :=
    ⟨0, isZero_zero D, ⟨0, ⟨F.mapZeroObject⟩⟩⟩
  have hc : F.essImage.IsTriangulatedClosed₃ := .mk' (by
    rintro T hT ⟨A, ⟨eA⟩⟩ ⟨B, ⟨eB⟩⟩
    obtain ⟨g, e, hg⟩ := hF A B (eA.hom ≫ T.mor₁ ≫ eB.inv)
    obtain ⟨Z, b, c, hS⟩ := distinguished_cocone_triangle g
    refine ⟨Z, ⟨Triangle.π₃.mapIso (isoTriangleOfIso₁₂ _ _
      (F.map_distinguished _ hS) hT (e ≪≫ eA) eB ?_)⟩⟩
    change F.map g ≫ eB.hom = (e.hom ≫ eA.hom) ≫ T.mor₁
    rw [← hg]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])
  exact { toIsTriangulatedClosed₂ := .of_isTriangulatedClosed₃ }

private theorem nsmul_isIso_of_unit
    {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C]
    (n : ℕ) (hn : IsIso (n • 𝟙 (𝟙_ C))) (M : C) : IsIso (n • 𝟙 M) := by
  have h : IsIso ((tensorRight M).map (n • 𝟙 (𝟙_ C))) := inferInstance
  rw [CategoryTheory.Functor.map_nsmul, CategoryTheory.Functor.map_id] at h
  change IsIso (n • 𝟙 (𝟙_ C ⊗ M)) at h
  have h' : IsIso ((λ_ M).inv ≫ (n • 𝟙 (𝟙_ C ⊗ M)) ≫ (λ_ M).hom) := inferInstance
  simpa only [comp_nsmul, nsmul_comp, Category.comp_id, Category.id_comp, Iso.inv_hom_id] using h'

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

private theorem ell_ne_zero : (ℓ : E) ≠ 0 := by
  have h : (ℓ : ℚ_[ℓ]) ≠ 0 := by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
  simpa only [map_natCast, map_zero] using (algebraMap ℚ_[ℓ] E).injective.ne h

private theorem point_nsmul_isIso :
    IsIso (ℓ • 𝟙 (Profinite.continuousMapRingObj.{u} E)) := by
  let R := Profinite.continuousMapRingObj.{u} E
  have hm : IsIso ((sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map
      (ℓ • 𝟙 (Profinite.continuousMapRingObj E))) := by
    change IsIso (ℓ • 𝟙 R.obj)
    rw [NatTrans.isIso_iff_isIso_app]
    intro S
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    change Function.Bijective (fun x : ULift.{u + 1} C(S.unop, E) ↦ ℓ • x)
    simp only [nsmul_eq_mul]
    have h : IsUnit (ℓ : ULift.{u + 1} C(S.unop, E)) := by
      simpa only [map_natCast] using
        (((isUnit_iff_ne_zero.mpr (ell_ne_zero ℓ E)).map
          (ContinuousMap.C : E →+* C(S.unop, E))).map ULift.ringEquiv.symm.toRingHom)
    exact IsUnit.isUnit_iff_mulLeft_bijective.mp h
  exact isIso_of_reflects_iso _
    (sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1})

/-- Multiplication by ℓ is invertible on every continuous E-module.
Source: Bhatt--Scholze, Lemma 6.8.2.
(auxiliary; not a blueprint node).
Proof. Transport division by ℓ from the point to the regular coefficient module,
then tensor with the given module and conjugate by the left unitor. -/
theorem module_nsmul_isIso (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X)) :
    IsIso (ℓ • 𝟙 M) := by
  let R := condensedRingObj (Profinite.continuousMapRingObj E) X
  have : (upperStarFromPoint X).IsLeftAdjoint :=
    (pointUpperStarLowerStarAdjunction.comp
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))).isLeftAdjoint
  have : (upperStarFromPoint X).Additive :=
    rightExactFunctor_le_additiveFunctor _ _ _ (by
      rw [rightExactFunctor_iff]
      infer_instance)
  have : IsIso (ℓ • 𝟙 R) := by
    have hp := point_nsmul_isIso.{u} ℓ E
    have h : IsIso ((upperStarFromPoint X).map
        (ℓ • 𝟙 (Profinite.continuousMapRingObj E))) := inferInstance
    simpa only [CategoryTheory.Functor.map_nsmul, CategoryTheory.Functor.map_id] using h
  have : IsIso (ℓ • 𝟙 (Mod.regular R)) := by
    have hm : IsIso ((Mod.forget R).map (ℓ • 𝟙 (Mod.regular R))) := by
      change IsIso (ℓ • 𝟙 R)
      infer_instance
    exact isIso_of_reflects_iso _ (Mod.forget R)
  exact nsmul_isIso_of_unit ℓ (by assumption) M

/-- Multiplication by ℓ is invertible on every derived continuous E-module.
Source: Bhatt--Scholze, Lemma 6.8.2.
(auxiliary; not a blueprint node).
Proof. Additive cohomology carries the map to scalar multiplication on each
cohomology module; the module result and detection by cohomology conclude. -/
theorem derived_nsmul_isIso (X : Scheme.{u})
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))) :
    IsIso (ℓ • 𝟙 K) := by
  rw [DerivedCategory.isIso_iff]
  intro n
  rw [CategoryTheory.Functor.map_nsmul, CategoryTheory.Functor.map_id]
  exact module_nsmul_isIso ℓ E X _

private theorem derived_pow_nsmul_isIso (X : Scheme.{u})
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))) (n : ℕ) :
    IsIso (ℓ ^ n • 𝟙 K) := by
  induction n with
  | zero => simpa using (inferInstance : IsIso (𝟙 K))
  | succ n ih =>
    have : IsIso (ℓ • 𝟙 K) := derived_nsmul_isIso ℓ E X K
    have h : ℓ ^ (n + 1) • 𝟙 K = (ℓ ^ n • 𝟙 K) ≫ (ℓ • 𝟙 K) := by
      simp only [pow_succ, nsmul_comp, comp_nsmul, Category.id_comp, mul_smul]
      exact smul_comm _ _ _
    rw [h]
    infer_instance

variable [FiniteDimensional ℚ_[ℓ] E]

/-- The essential image of integral constructible scalar extension is triangulated.
Source: Bhatt--Scholze, Lemma 6.8.12 and Proposition 6.8.14(2).
(auxiliary; not a blueprint node)

Proof in words. Integral constructible modules form a weak Serre class by Proposition
6.8.11, so their bounded derived subcategory is closed under shifts and cones. Derived
coefficient extension is triangulated and sends zero to zero, giving zero and shift
closure of its essential image. For cone closure, take a morphism between scalar
extensions of two integral bounded constructible complexes. The localization telescope
and the bounded-below coproduct compactness of Lemma 6.8.12 identify the rational derived
Hom group with integral Hom after inverting ℓ. Thus a power of ℓ times the given morphism
is the scalar extension of an integral morphism. Complete that integral morphism to a
triangle; its cone is bounded integral constructible. Scalar extension gives a cone for
the multiplied morphism. Multiplication by that power of ℓ on the rational source is an
isomorphism, so the original morphism has an isomorphic cone. This proves cone closure,
and rotation gives the two-out-of-three formulation of triangulated closure. Transport
along the chosen endpoint isomorphisms handles every triangle whose endpoints lie in
the essential image. The coefficient telescope is the actual integralScalarExtension:
on compact profinite tests every continuous function has a single bounded denominator,
and exact pullback from the profinite point preserves that localization calculation.
This proves closure only; it does not assert that every rational object is in the image.
-/
theorem continuousConstructible_integral_image_triangulated (X : Scheme.{u})
    [TopologicalSpace.NoetherianSpace X] :
    (((ProEtale.boundedConstructible (condensedRingObj (integralCoeff ℓ E) X)).ι ⋙
      integralScalarExtension ℓ E X).essImage).IsTriangulated := by
  let R := condensedRingObj (integralCoeff ℓ E) X
  let P := boundedConstructible R
  obtain ⟨hk, hc, he⟩ := integralConstructible_serre ℓ E X
  let := hk
  let := hc
  let := he
  have : P.IsTriangulated := inferInstance
  let F := integralScalarExtension ℓ E X
  let adj := Mod.derivedExtendMapDerivedCategoryAdjunction
    (coefficientMap (integralScalarMap ℓ E) X)
  let hs : (L(Mod.extendScalars
      (coefficientMap (integralScalarMap ℓ E) X))).CommShift ℤ :=
    adj.leftAdjointCommShift ℤ
  let : F.CommShift ℤ := hs
  have : adj.CommShift ℤ := adj.commShift_of_rightAdjoint ℤ
  have : F.IsTriangulated := adj.isTriangulated_leftAdjoint
  change (P.ι ⋙ F).essImage.IsTriangulated
  apply essImage_triangulated_of_arrow_lifting
  intro A B f
  have hden : ∃ (n : ℕ) (g : A ⟶ B), ℓ ^ n • f = F.map g.hom :=
    continuousConstructible_clear_denominators ℓ E X A B f
  obtain ⟨n, g, hg⟩ := hden
  have hi : IsIso (ℓ ^ n • 𝟙 ((P.ι ⋙ F).obj A)) :=
    derived_pow_nsmul_isIso ℓ E X _ n
  refine ⟨g, asIso (ℓ ^ n • 𝟙 ((P.ι ⋙ F).obj A)), ?_⟩
  change (ℓ ^ n • 𝟙 (F.obj A.obj)) ≫ f = F.map g.hom
  simpa only [nsmul_comp, Category.id_comp] using hg

end AlgebraicGeometry.ProEtale.CondensedRing
