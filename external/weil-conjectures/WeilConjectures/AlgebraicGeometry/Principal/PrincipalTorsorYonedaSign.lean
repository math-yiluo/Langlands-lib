/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PrincipalTorsorComparisons.PrincipalTorsorSignTypes
import WeilConjectures.AlgebraicGeometry.Principal.PrincipalTorsorNormalizedComparison
import WeilConjectures.AlgebraicGeometry.Principal.PrincipalTorsorConnectingComparison
import WeilConjectures.AlgebraicGeometry.Principal.PrincipalTorsorFramedComparison
import WeilConjectures.AlgebraicGeometry.Principal.PrincipalTorsorNormalizedNatural
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import WeilConjectures.CategoryTheory.Sites.Torsor
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.CategoryTheory.Sites.RelativeTorsorExtension
public import WeilConjectures.CategoryTheory.Sites.TorsorExtensionPresentation
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import Mathlib.CategoryTheory.Abelian.Exact
public import WeilConjectures.CategoryTheory.Sites.EtaleTorsorExtensionPresentationExists
public import WeilConjectures.CategoryTheory.Sites.ExtensionPresentationShortExact
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.AlgebraicGeometry.Relative.RelativeEtaleCohomology
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.DivisorTorsorBoundarySigns
public import WeilConjectures.AlgebraicGeometry.RelativeCone.PurityRelativeCone
public import WeilConjectures.Algebra.Homology.SmoothPurity.ClosedSupportHom
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleSupportedSections
public import WeilConjectures.SixFunctors.OpenClosed.Exact

/-! The signed torsor formula from normalized comparisons and Yoneda compatibility.

## References

* Stacks Tags 03AJ and 06XU
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite HomologicalComplex
namespace AlgebraicGeometry.Etale
private lemma principal_section_rep_unique
    (T : Scheme.{u}) (U : T.Etale)
    (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ) (q : ℕ)
    (b : (I.X q).obj.obj (op U)) (x y : (relativeSections U I).homology q)
    (hx : TorsorSectionRepresents U I q b x)
    (hy : TorsorSectionRepresents U I q b y) : x = y := by
  obtain ⟨z, hz, rfl⟩ := hx
  obtain ⟨z', hz', rfl⟩ := hy
  congr 1
  apply (AddCommGrpCat.mono_iff_injective ((relativeSections U I).iCycles q)).1
    inferInstance
  apply (ConcreteCategory.bijective_of_isIso
    ((((etaleSectionFunctor U).mapHomologicalComplex (.up ℕ)).obj I).extendXIso
      ComplexShape.embeddingUpNat rfl).hom).1
  exact hz.trans hz'.symm

private theorem principal_torsor_yoneda_sign_formula
    (C : PrincipalTorsorComparisons.{u}) (hC : C.Normalized) : C.Formula := by
  classical
  intro T Z i hi W h G P e s g hs E a b hab hE F hF hbF hFs
  obtain ⟨hpush, hframe⟩ := principalTorsorFramedComparison C hC T Z i W h G P e s g hs
    E a b hab hE F hF hbF hFs
  constructor
  · exact hpush
  · intro H K aK bK habK hK I J L α β hαβ hα hβ hsplit
    let U := Scheme.Etale.mk W.ι
    obtain ⟨e', he', hsign⟩ := divisor_torsor_boundary_signs.{u}
    obtain ⟨x₀, hx₀, hy₀, _⟩ := hsign.trivial T W G L g
    have hbclass := hframe L _ hy₀
    obtain ⟨hOpen, hop⟩ := hsign.coefficients T W (ShortComplex.mk aK bK habK) hK I J L
      α β hαβ hα hβ hsplit
    obtain ⟨x₁, hx₁, hδ, _⟩ := hop g
    refine ⟨hOpen, ?_⟩
    intro x hx
    have hxx := principal_section_rep_unique T U L.cocomplex 0
      ((L.ι.f 0).hom.app (op U) g) x x₁ hx hx₁
    rw [hxx]
    have hcomp := principalTorsorConnectingComparison C hC T Z i W h
      (ShortComplex.mk aK bK habK) hK I J L α β hαβ hα hβ hsplit hE.extClass
    rw [hbclass, map_neg, hδ] at hcomp
    rw [hcomp, map_neg]

/-- A globally framed relative torsor is the inverse-section localization pushout;
its coefficient Yoneda splice is minus the supported localization boundary.
All identifications are supplied with their cocycle normalization and naturality. -/
theorem principal_torsor_yoneda_sign :
    ∃ C : PrincipalTorsorComparisons.{u}, C.Normalized ∧ C.Natural ∧ C.Formula := by
  obtain ⟨C, hC⟩ := principalTorsorNormalizedComparison.{u}
  exact ⟨C, hC, principalTorsorNormalizedNatural C hC,
    principal_torsor_yoneda_sign_formula C hC⟩

end AlgebraicGeometry.Etale
