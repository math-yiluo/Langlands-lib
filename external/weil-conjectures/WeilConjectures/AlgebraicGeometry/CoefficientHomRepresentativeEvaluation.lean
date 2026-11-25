/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses

/-! # Canonical Hom representative evaluation on a ringed site

Source: Stacks Project, Tags 0A8X, 0A95 and 079P
(auxiliary; not a blueprint node).
The evaluation uses the actual Hom-product projections, the fixed functorial
K-injective replacement and its localization factorization.

## Main definitions

- `coefficientHomComponent`: the fixed product projection of the Hom complex.
- `coefficientHomResolution`: the existing functorial K-injective replacement.
- `coefficientHomResolutionIso`: the actual localization factorization.
- `coefficientHomResolutionInverse`: the inverse localized augmentation.
- `coefficientHomSectionEvaluation`: componentwise evaluation into that replacement.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u c v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures

section HomProjection

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})]
  (A : Sheaf J CommRingCat.{max c v u})

/-- Actual projections. Source: Stacks 0A8X
(auxiliary; not a blueprint node). -/
noncomputable def coefficientHomComponent
    (L M : CochainComplex (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ)
    (n p q : ℤ) (h : p + n = q) :
    (homComplex.{c, v, max c v u, max c v u} (R := A) L M).X n ⟶
      SheafOfModules.homObj (R := A) (L.X p) (M.X q) :=
  homComplexπ.{c, v, max c v u, max c v u} (R := A) L M n p q h

end HomProjection

section NativeProjection

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v} RingCat.{max c v})]
  (R : Sheaf J CommRingCat.{max c v})

/-- Compatibility of the cached projection presentation with the native tensor-Hom API. -/
private theorem coefficientHomComponent_eq_native
    (L M : CochainComplex (SheafOfModules.{max c v}
      ((sheafCompose J (forget₂ CommRingCat.{max c v} RingCat.{max c v})).obj R)) ℤ)
    (n p q : ℤ) (h : p + n = q) :
    coefficientHomComponent.{0, c, v} J R L M n p q h =
      homTensorCurryProjection R L M n p q h := by
  rfl


end NativeProjection

section ClosedRepresentatives

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  (A : Sheaf J CommRingCat.{max c v u})

/-- The fixed K-injective replacement already used in the recorded internal Hom.
Source: Stacks 0A95 (auxiliary; not a blueprint node). -/
noncomputable def coefficientHomResolution :
    CochainComplex (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ ⥤
    CochainComplex (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ :=
  letI :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, u}
      J A).1
  CochainComplex.kInjectiveResolutionFunctor.{max c v u} _

/-- The fixed internal-Hom localization factorization, with no choice of comparison map.
Source: Stacks 0A95 (auxiliary; not a blueprint node). -/
noncomputable def coefficientHomResolutionIso
    [HasDerivedCategory.{w} (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A))]
    (L M : CochainComplex (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ) :
    (derivedInternalHomOfUniverses.{c, v, u, w} J A).obj
        (op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj M) ≅
      DerivedCategory.Q.obj
        (homComplex.{c, v, max c v u, max c v u} (R := A) L
          ((coefficientHomResolution.{u, c, v} J A).obj M)) :=
  letI :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, u}
      J A).1
  (Localization.fac
    ((𝟭 _).prod (CochainComplex.kInjectiveResolutionFunctor.{max c v u} _) ⋙
      Functor.uncurry.obj (homComplexFunctor.{c, v, max c v u, max c v u} (R := A)) ⋙
        DerivedCategory.Q)
    (derivedInternalHomOfUniverses_inverts.{c, v, u, w} J A _
      (CochainComplex.toKInjectiveResolution.{max c v u} _)
      (fun M ↦ ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{max c v u} _ M).2,
        CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{max c v u} _ M⟩))
    (DerivedCategory.Q.op.prod DerivedCategory.Q)).app (op L, M)

/-- The inverse of the actual localized augmentation to the fixed K-injective resolution.
Source: Stacks 079P (auxiliary; not a blueprint node). -/
noncomputable def coefficientHomResolutionInverse
    [HasDerivedCategory.{w} (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A))]
    (M : CochainComplex (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ) :
    DerivedCategory.Q.obj ((coefficientHomResolution.{u, c, v} J A).obj M) ⟶
      DerivedCategory.Q.obj M :=
  letI :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, u}
      J A).1
  letI : IsIso (DerivedCategory.Q.map
      ((CochainComplex.toKInjectiveResolution.{max c v u} _).app M)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr
      (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{max c v u} _ M).2
  inv (DerivedCategory.Q.map ((CochainComplex.toKInjectiveResolution.{max c v u} _).app M))

/-- Actual evaluation of a Hom-complex section in its (q,q+p)-product factor.
Source: Stacks 0A8X, 08J9 (auxiliary; not a blueprint node). -/
noncomputable def coefficientHomSectionEvaluation
    (P L M : CochainComplex (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ)
    (φ : P ⟶ homComplex.{c, v, max c v u, max c v u} (R := A) L
          ((coefficientHomResolution.{u, c, v} J A).obj M))
    (p q k : ℤ) (h : q + p = k) (U : Cᵒᵖ)
    (x : (P.X p).val.obj U) (y : (L.X q).val.obj U) :
    (((coefficientHomResolution.{u, c, v} J A).obj M).X k).val.obj U :=
  let f := (coefficientHomComponent.{u, c, v} J A L
    ((coefficientHomResolution.{u, c, v} J A).obj M) p q k h).val.app U
      ((φ.f p).val.app U x)
  (f.app (op (Over.mk (𝟙 U.unop)))).hom y

end ClosedRepresentatives

end WeilConjectures
