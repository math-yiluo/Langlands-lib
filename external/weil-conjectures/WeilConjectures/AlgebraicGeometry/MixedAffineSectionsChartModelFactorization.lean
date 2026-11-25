/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.MixedGlobalExtension
public import WeilConjectures.AlgebraicGeometry.GlobalHomAdjunctionIso
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.AlgebraicGeometry.MixedAffineSectionsExtensionUnitNormalization
import WeilConjectures.AlgebraicGeometry.MixedAffineSectionsPullbackUnitNormalization

/-! # Localization of the ordinary affine chart comparison in independent universes
Source: Stacks Project, Tags 06Z0, 08DW(2), 0AA7 and 0D5T.
(blueprint: lem-sc-mixed-affine-sections-chart-model-factorization).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w wA
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

private theorem chartModelFactorization_of_units
    {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) {X X' : C} {Y Z Z' : D} (s : X' ⟶ X) [Epi s]
    (a : L.obj X ≅ Y) (b : Z ≅ Z') (c : Y ⟶ Z') (p : X ⟶ R.obj Z)
    (h : s ≫ p ≫ R.map b.hom = s ≫ adj.homEquiv _ _ (a.hom ≫ c)) :
    (adj.homEquiv _ _).symm p ≫ b.hom = a.hom ≫ c := by
  apply (adj.homEquiv _ _).injective
  apply (cancel_epi s).1
  rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
  exact h

/-- Localization transports the ordinary unit equation to the fixed mixed
adjunction mate. No invertibility of the ordinary comparison c is assumed.
Source: Stacks Project, Tags 06Z0, 08DW(2), 0AA7 and 0D5T.
(blueprint: lem-sc-mixed-affine-sections-chart-model-factorization).

Proof: Write C = F(P), X = Gamma_S(C), and Y = tensorPullback_g(C).
The affine tilde unit identifies X with P. Thus X is K-flat. Tilde preserves
K-flatness, and restriction along the canonical spectrum isomorphism preserves
it, so C is K-flat. The left-derived counits compute extension on X and pullback
on C. The affine derived sections comparison is invertible on C and Y: for Y
use the termwise tilde/pullback isomorphism, transported through the spectrum charts,
and the affineTildeDerivedSectionsUnit_isIso comparison.
These assertions hold for arbitrary unbounded P by affine acyclicity and the
truncation argument in Tag 06Z0. Identify the fixed mixed extension with the
standard left derived extension by left-adjoint uniqueness. The source
isomorphism a is the inverse image under extension of the affine sections
comparison, followed by the extension counit. The target isomorphism b is
sections of the pullback counit followed by the inverse affine sections comparison.
Apply hc termwise and then localize. The derived adjunction unit equations factor
the two units through their left-derived counits. Substitute them in hc.
Naturality moves the right-derived sections units past those counits. The
right-derived-unit normalization of mixedGlobalSectionsDirectImageIso identifies
the localized ordinary direct-image/sections comparison with that fixed Leray
isomorphism. Cancel the invertible sections comparison maps and use the adjunction
hom-equivalence formula to obtain the displayed equality. More explicitly, suppress
only the quotient-to-homotopy factor isomorphisms, and let q denote localization.
Write s_C : q(H(C)) -> RGamma_S(q(C)), s_Y : q(J(Y)) -> RGamma_T(q(Y)),
and e_E : LE(q(X)) -> q(E(X)), e_K : Lg*(q(C)) -> q(Y).
Let r_Z : q(R(Z)) -> R(q(Z)) be the exact scalar restriction comparison.
The derived extension unit equation is
  eta_LE(q(X)) ; R(e_E) = q(eta_E(X)) ; r_E(X).
The pinned derived pullback unit equation is
  eta_Lg(q(C)) ; Rg_*(e_K) = q(eta_K(C)) ; u_DI(Y),
where u_DI is the right-derived direct-image unit. Naturality of s and the
normalized Leray equation say
  s_C ; RGamma_S(q(eta_K(C))) = q(H(eta_K(C))) ; s_DI(Y),
  s_DI(Y) ; RGamma_S(u_DI(Y)) ; Leray(q(Y)) = r_J(Y) ; R(s_Y).
Naturality of Leray at e_K now identifies the Hom-equivalent of
LE(s_C) ; n ; b.hom with q(H(eta_K(C))) ; r_J(Y).
Localizing hc, then using naturality of r at c_P, identifies this with
q(eta_E(X)) ; r_E(X) ; R(q(c_P)). The extension unit equation identifies
the latter with the Hom-equivalent of e_E ; q(c_P).
Injectivity of the extension Hom equivalence gives
LE(s_C) ; n ; b.hom = e_E ; q(c_P).
Cancel the invertible LE(s_C); with a.hom = LE(s_C) inverse followed by e_E,
this is the exact factorization in the statement. All these equations are in
module categories after their indicated localization; the sheaf units enter only
through RGamma and the normalized Leray equation. Sheaf localization and
module localization occur separately; no equality of w and wA is used. The
statement applies also to the zero transformation when hc holds; its proof uses
only hc and never that c is invertible. Empty affine schemes and P = 0 are covered
by the same equations. -/
theorem exists_mixedAffineSections_chart_model_factorization
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (R : Type u) [Ring R], HasDerivedCategory.{wA} (ModuleCat.{u} R)]
    {S T : Scheme.{u}} [IsAffine S] [IsAffine T] (g : T ⟶ S) :
    let F : ModuleCat.{u} Γ(S, ⊤) ⥤
        SheafOfModules.{u} (moduleRings S.toRingedSpace) :=
      tilde.functor Γ(S, ⊤) ⋙ Scheme.Modules.restrictFunctor S.toSpecΓ
    let H := RingedSpace.globalSectionsFunctor S.toRingedSpace
    let J := RingedSpace.globalSectionsFunctor T.toRingedSpace
    let E := ModuleCat.extendScalars.{u, u, u} g.appTop.hom
    let K : SheafOfModules.{u} (moduleRings S.toRingedSpace) ⥤
        SheafOfModules.{u} (moduleRings T.toRingedSpace) := Scheme.Modules.tensorPullback g
    ∀ (c : F ⋙ H ⋙ E ⟶ F ⋙ K ⋙ J),
      (∀ N : ModuleCat.{u} Γ(S, ⊤),
        (ModuleCat.extendRestrictScalarsAdj g.appTop.hom).unit.app (H.obj (F.obj N)) ≫
          (ModuleCat.restrictScalars.{u} g.appTop.hom).map (c.app N) =
        H.map ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).unit.app
          (F.obj N))) →
      ∀ [F.Additive] [H.Additive] [J.Additive] [E.Additive] [K.Additive]
        (P : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℤ)
        (_hP : (HomologicalComplex.quasiIso (ModuleCat.{u} Γ(S, ⊤)) (.up ℤ)).kFlat P),
      let Q := DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P)
      ∃ (a : (mixedGlobalExtension g).obj ((schemeDerivedGlobalSections S).obj Q) ≅
            DerivedCategory.Q.obj (((F ⋙ H ⋙ E).mapHomologicalComplex (.up ℤ)).obj P))
        (b : (schemeDerivedGlobalSections T).obj ((derivedPullback g).obj Q) ≅
            DerivedCategory.Q.obj (((F ⋙ K ⋙ J).mapHomologicalComplex (.up ℤ)).obj P)),
        (((mixedGlobalExtensionAdjunction g).homEquiv _ _).symm
          ((schemeDerivedGlobalSections S).map ((schemeHomPullbackAdjunction g).unit.app Q) ≫
            (mixedGlobalSectionsDirectImageIso g).hom.app ((derivedPullback g).obj Q))) ≫
              b.hom = a.hom ≫
                DerivedCategory.Q.map ((c.mapHomologicalComplex (.up ℤ)).app P) := by
  intro F H J E K c hc instF instH instJ instE instK P hP Q
  let R := ModuleCat.restrictScalars.{u} g.appTop.hom
  have : F.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive F
  have : H.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive H
  have : J.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive J
  have : E.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive E
  have : K.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive K
  have : R.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive R
  let C := (F.mapHomologicalComplex (.up ℤ)).obj P
  let d : F ⋙ H ⟶ F ⋙ K ⋙ J ⋙ R :=
    Functor.whiskerRight (Functor.whiskerLeft F
      (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).unit) H
  let X := ((F ⋙ H).mapHomologicalComplex (.up ℤ)).obj P
  let e := (ModuleCat.extendRestrictScalarsAdj g.appTop.hom).mapHomologicalComplex (.up ℤ)
  have hcP : e.unit.app X ≫
      (R.mapHomologicalComplex (.up ℤ)).map ((c.mapHomologicalComplex (.up ℤ)).app P) =
        (d.mapHomologicalComplex (.up ℤ)).app P := by
    apply HomologicalComplex.Hom.ext
    funext i
    exact hc (P.X i)
  obtain ⟨a, ha⟩ := exists_mixedAffineSections_extension_unit_normalization g P hP
  obtain ⟨b, hb⟩ := exists_mixedAffineSections_pullback_unit_normalization g P hP
  refine ⟨a, b, ?_⟩
  have : IsIso (mixedSectionsComplexUnit S C) :=
    mixedAffineChart_sectionsComplexUnit_isIso S P
  apply chartModelFactorization_of_units (mixedGlobalExtensionAdjunction g)
    (mixedSectionsComplexUnit S C)
  have ha' := ha _ ((c.mapHomologicalComplex (.up ℤ)).app P)
  rw [hcP] at ha'
  simp only [Category.assoc] at hb ⊢
  exact hb.trans ha'.symm


end AlgebraicGeometry
