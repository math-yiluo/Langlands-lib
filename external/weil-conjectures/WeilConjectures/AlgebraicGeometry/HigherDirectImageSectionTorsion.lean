/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
import WeilConjectures.AlgebraicGeometry.HigherImageCohomologyPresheafLocalization
import WeilConjectures.AlgebraicGeometry.AffineLocalizingPresheafSheafification
import WeilConjectures.AlgebraicGeometry.HigherDirectImagePresheaf

/-! # Power torsion for higher direct image sections

Source: Stacks Project, Tags 01XJ (1), 09MR and 01E4.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X T : Scheme.{u}} (f : X ⟶ T) (ℱ : X.Modules)
variable [QuasiCompact f] [QuasiSeparated f] [HasInjectiveResolutions X.Modules]
  [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A higher direct image section vanishing on a principal open is power torsion.
Source: Stacks Project, Tag 01XJ (1), via localization in Tag 09MR and Tag 01E4.
(blueprint: lem-pc-higher-direct-image-section-torsion).

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
If t restricts to zero on D(a), the fraction t/1 is zero in the localized
module. The zero criterion for module localization gives a^n t = 0 for some n.
This includes q = 0, a = 0 (choose n = 1), units a (then t = 0), the zero
module and empty W. This is only the kernel assertion; it gives no lifting of
sections on the principal open. -/
theorem higherDirectImage_section_pow_annihilates (q : ℕ) (W : T.Opens)
    (hW : IsAffineOpen W) (a : Γ(T, W))
    (t : Γ((higherDirectImage f q).obj ℱ, W))
    (ht : ((higherDirectImage f q).obj ℱ).presheaf.map
      (homOfLE (T.basicOpen_le a)).op t = 0) :
    ∃ n : ℕ, a ^ n • t = 0 := by
  let I := injectiveResolution ℱ
  let K := ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  let P := sectionCohomologyPresheaf K q
  let M := (higherDirectImage f q).obj ℱ
  let A := PresheafOfModules.sheafificationAdjunction (𝟙 T.ringCatSheaf.obj)
  let c := sectionCohomologyComparison K q ≫ (I.isoRightDerivedObj (pushforward f) q).inv
  let hc : IsIso c := (higherDirectImagePresheaf f ℱ I q).1
  let θ : P ⟶ (SheafOfModules.forget T.ringCatSheaf).obj M := A.homEquiv P M c
  have hP (V : T.Opens) (hV : IsAffineOpen V) (b : Γ(T, V)) :
      IsLocalizedModule.Away b (P.map (homOfLE (T.basicOpen_le b)).op).hom :=
    higherImageCohomologyPresheaf_isLocalized f ℱ I q V hV b
  have hθ (V : T.Opens) (hV : IsAffineOpen V) : IsIso (θ.app (Opposite.op V)) := by
    let hu := isIso_sheafificationUnit_app_of_affine_localizing T P hP V hV
    change IsIso (((A.unit.app P).app (Opposite.op V)) ≫
      ((SheafOfModules.forget T.ringCatSheaf).map c).app (Opposite.op V))
    have hv : IsIso (((SheafOfModules.forget T.ringCatSheaf).map c).app
        (Opposite.op V)) :=
      (PresheafOfModules.evaluation T.ringCatSheaf.obj (Opposite.op V)).map_isIso
        ((SheafOfModules.forget T.ringCatSheaf).map c)
    let : IsIso ((A.unit.app P).app (Opposite.op V)) := hu
    let : IsIso (((SheafOfModules.forget T.ringCatSheaf).map c).app
        (Opposite.op V)) := hv
    infer_instance
  have hθW := hθ W hW
  have hθD := hθ (T.basicOpen a) (hW.basicOpen a)
  obtain ⟨x, hx⟩ := (ConcreteCategory.bijective_of_isIso (θ.app (Opposite.op W))).2 t
  have hx0 : P.map (homOfLE (T.basicOpen_le a)).op x = 0 := by
    apply (ConcreteCategory.bijective_of_isIso
      (θ.app (Opposite.op (T.basicOpen a)))).1
    have hn := ConcreteCategory.congr_hom
      (θ.naturality (homOfLE (T.basicOpen_le a)).op) x
    change θ.app (Opposite.op (T.basicOpen a))
        (P.map (homOfLE (T.basicOpen_le a)).op x) =
      M.presheaf.map (homOfLE (T.basicOpen_le a)).op
        (θ.app (Opposite.op W) x) at hn
    rw [hx, ht] at hn
    simpa only [map_zero] using hn
  have := hP W hW a
  obtain ⟨⟨_, n, rfl⟩, hn⟩ :=
    (IsLocalizedModule.eq_zero_iff (.powers a)
      (P.map (homOfLE (T.basicOpen_le a)).op).hom).mp hx0
  refine ⟨n, ?_⟩
  have he := congrArg (θ.app (Opposite.op W)) hn
  change (θ.app (Opposite.op W)).hom (a ^ n • x) =
    (θ.app (Opposite.op W)).hom 0 at he
  rw [_root_.map_smul, map_zero] at he
  exact hx ▸ he

end AlgebraicGeometry.Scheme.Modules
