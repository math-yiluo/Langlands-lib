/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
import WeilConjectures.AlgebraicGeometry.SectionCohomologyPrincipalLocalization
import WeilConjectures.AlgebraicGeometry.AffineLocalizationSheafification
import WeilConjectures.AlgebraicGeometry.HigherDirectImagePresheaf

/-! # Denominator bounds for higher direct image sections

Source: Stacks Project, Tags 01XJ (1), 09MR and 01E4.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X T : Scheme.{u}} (f : X ⟶ T) (ℱ : X.Modules)
variable [QuasiCompact f] [QuasiSeparated f] [HasInjectiveResolutions X.Modules]
  [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]

/-- A section of a higher direct image on a principal open has a denominator bound.
Source: Stacks Project, Tag 01XJ (1), via localization in Tag 09MR and Tag 01E4.
(blueprint: lem-pc-higher-direct-image-section-denominators).

Proof:
Work on an affine open W = Spec A of the base. The inverse image Y = f⁻¹W is
quasi-compact and quasi-separated, since f is qcqs and W is affine. Here H^q
means right-derived module sections, as in RingedSpace.openModuleCohomology;
no comparison with the source library's abelian-sheaf Ext model is needed.
For each a in A, its pullback b is a global function on Y, and f⁻¹D(a) = D(b).
Apply cohomology localization (Tag 09MR)
with the tensor unit as the invertible module: the restriction map identifies
H^q(D(b), ℱ) with H^q(Y, ℱ)[1/b]. Under the unit tensor identifications,
the fraction relations are [n, x] = [n+k, b^k x]. The canonical formula
x/b^n ↦ b^(-n) res(x) proves A-linearity, since restriction is linear and
b is invertible on D(b). It also proves compatibility with further principal
restrictions: both composites send each fraction to the same restricted
numerator divided by the same power. These fractions generate the localization.
Doing this for all principal opens in W identifies the cohomology presheaf on
that basis with the sections of the associated A-module H^q(Y, ℱ). This is a
sheaf on the principal-open basis (localization is exact and satisfies the
finite principal-cover equalizer condition). The higher direct image is the
sheafification of the cohomology presheaf by Tag 01E4, so this identification
also identifies its sections and restriction maps on W and D(a). It does not
use the affine sections comparison in DirectImage.Sections, whose proof needs
quasi-coherence; instead it uses the cohomology presheaf and its sheafification.
A section on D(a) is a fraction m/a^n. Multiplication by a^n gives the
restriction of m, which is the required section on W. This includes q = 0,
a = 0 (the principal open is empty), units a, the zero module, and empty W. -/
theorem higherDirectImage_section_clearDenominators (q : ℕ) (W : T.Opens)
    (hW : IsAffineOpen W) (a : Γ(T, W))
    (s : Γ((higherDirectImage f q).obj ℱ, T.basicOpen a)) :
    ∃ (n : ℕ) (t : Γ((higherDirectImage f q).obj ℱ, W)),
      ((higherDirectImage f q).obj ℱ).presheaf.map
          (homOfLE (T.basicOpen_le a)).op t =
        T.presheaf.map (homOfLE (T.basicOpen_le a)).op a ^ n • s := by
  let I := injectiveResolution ℱ
  let K := ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  let P := sectionCohomologyPresheaf K q
  let M := (higherDirectImage f q).obj ℱ
  let A := PresheafOfModules.sheafificationAdjunction (𝟙 T.ringCatSheaf.obj)
  let c : (PresheafOfModules.sheafification (𝟙 T.ringCatSheaf.obj)).obj P ⟶ M :=
    sectionCohomologyComparison K q ≫
    (I.isoRightDerivedObj (pushforward f) q).inv
  have hc : IsIso c := (higherDirectImagePresheaf f ℱ I q).1
  let θ := A.homEquiv P M c
  have hlocal : ∀ (U : T.Opens), IsAffineOpen U → ∀ b : Γ(T, U),
      let : Module Γ(T, U) (P.obj (Opposite.op (T.basicOpen b))) :=
        Module.compHom _ (T.presheaf.map (homOfLE (T.basicOpen_le b)).op).hom
      IsLocalizedModule.Away b (P.map (homOfLE (T.basicOpen_le b)).op).hom := by
    intro U hU b
    exact sectionCohomologyPresheaf_isLocalized_away f ℱ I q U hU b
  have hθ (U : T.Opens) (hU : IsAffineOpen U) : IsIso (θ.app (Opposite.op U)) := by
    have hu : IsIso ((A.unit.app P).app (Opposite.op U)) :=
      affineLocalization_sheafification_unit_isIso T P hlocal U hU
    have hcU : IsIso (((SheafOfModules.forget T.ringCatSheaf ⋙
        PresheafOfModules.restrictScalars (𝟙 T.ringCatSheaf.obj)).map c).app (Opposite.op U)) :=
      by
        exact (PresheafOfModules.evaluation T.ringCatSheaf.obj (Opposite.op U)).map_isIso
          ((SheafOfModules.forget T.ringCatSheaf ⋙
            PresheafOfModules.restrictScalars (𝟙 T.ringCatSheaf.obj)).map c)
    dsimp [θ]
    erw [Adjunction.homEquiv_unit]
    change IsIso ((A.unit.app P).app (Opposite.op U) ≫ ((SheafOfModules.forget T.ringCatSheaf ⋙
      PresheafOfModules.restrictScalars (𝟙 T.ringCatSheaf.obj)).map c).app (Opposite.op U))
    infer_instance
  have hθa := hθ (T.basicOpen a) (hW.basicOpen a)
  obtain ⟨x, hx⟩ := (ConcreteCategory.bijective_of_isIso (θ.app (Opposite.op (T.basicOpen a)))).2 s
  let : Module Γ(T, W) (P.obj (Opposite.op (T.basicOpen a))) :=
    Module.compHom _ (T.presheaf.map (homOfLE (T.basicOpen_le a)).op).hom
  have hl := hlocal W hW a
  obtain ⟨n, y, hy⟩ := IsLocalizedModule.Away.surj
    (P.map (homOfLE (T.basicOpen_le a)).op).hom a x
  refine ⟨n, θ.app (Opposite.op W) y, ?_⟩
  change M.presheaf.map (homOfLE (T.basicOpen_le a)).op (θ.app (Opposite.op W) y) = _
  erw [← PresheafOfModules.naturality_apply θ]
  erw [← hy]
  change θ.app (Opposite.op (T.basicOpen a))
    (T.presheaf.map (homOfLE (T.basicOpen_le a)).op (a ^ n) • x) = _
  change (θ.app (Opposite.op (T.basicOpen a))).hom
      (T.presheaf.map (homOfLE (T.basicOpen_le a)).op (a ^ n) • x) = _
  erw [(θ.app (Opposite.op (T.basicOpen a))).hom.map_smul, hx]
  simp only [map_pow]

end AlgebraicGeometry.Scheme.Modules
