/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.InfPoints
import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.PointOfDerivation
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.AlgebraicGeometry.GroupScheme.DiagonalDerivationCoefficients

/-!
# Addition of tangent maps on the dual-number diagonal

Source: Stacks Project, Tag 0B2B, proof of Lemma 33.16.2, the square-zero
pushout calculation; blueprint `def-wf-lie-algebra-derivation`, the dual-number description.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry.GrpObj

set_option backward.isDefEq.respectTransparency false in
private theorem homOfDerivation_add_of_coefficients {S : Scheme.{u}} (X : Over S)
    (g : S ⟶ X.left)
    (D₁ D₂ D₃ : ((Scheme.Modules.pushforward g).obj
      (Scheme.Modules.unitModule S)).val.Derivation' X.hom.pullbackPresheafHom)
    (h : ∀ {V : (TopologicalSpace.Opens X.left)ᵒᵖ} (a : Γ(X.left, V.unop)),
      D₃.d a = D₁.d a + D₂.d a) :
    homOfDerivation X g D₃ = homOfDerivation X g D₁ + homOfDerivation X g D₂ := by
  have hdesc : (PresheafOfModulesOfCommRing.DifferentialsConstruction.isUniversal' _).desc D₃ =
      (PresheafOfModulesOfCommRing.DifferentialsConstruction.isUniversal' _).desc D₁ +
        (PresheafOfModulesOfCommRing.DifferentialsConstruction.isUniversal' _).desc D₂ := by
    apply (PresheafOfModulesOfCommRing.DifferentialsConstruction.isUniversal' _).postcomp_injective
    ext V a
    have h₁ := PresheafOfModulesOfCommRing.Derivation.congr_d
      ((PresheafOfModulesOfCommRing.DifferentialsConstruction.isUniversal' _).fac D₁) a
    have h₂ := PresheafOfModulesOfCommRing.Derivation.congr_d
      ((PresheafOfModulesOfCommRing.DifferentialsConstruction.isUniversal' _).fac D₂) a
    have h₃ := PresheafOfModulesOfCommRing.Derivation.congr_d
      ((PresheafOfModulesOfCommRing.DifferentialsConstruction.isUniversal' _).fac D₃) a
    exact h₃.trans ((h a).trans (congrArg₂ (· + ·) h₁.symm h₂.symm))
  let sh := PresheafOfModules.sheafificationAdjunction (𝟙 X.left.ringCatSheaf.obj)
  have := sh.left_adjoint_additive
  have hs : sh.homEquiv X.hom.cotangentPresheaf
      ((Scheme.Modules.pushforward g).obj (Scheme.Modules.unitModule S)) =
      PresheafOfModules.sheafificationHomEquiv (𝟙 X.left.ringCatSheaf.obj) := by
    ext a
    rfl
  unfold homOfDerivation
  rw [hdesc, ← hs]
  erw [Adjunction.homAddEquiv_symm_add, Adjunction.homAddEquiv_symm_add]
  rfl

private theorem omegaHom_transport {S : Scheme.{u}} (X : Over S)
    (v : Scheme.dualNumbersOver S ⟶ X) (g : S ⟶ X.left)
    (hv : S.dualNumbersι ≫ v.left = g) :
    (Scheme.Modules.pullbackCongr hv).inv.app X.hom.cotangentSheaf ≫ omegaHom X v =
      homOfDerivation X g (hv ▸ infDerivation X v) := by
  subst g
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_inv, NatTrans.id_app,
    Category.id_comp, omegaHom_eq_homOfDerivation]

/-- The tangent map of a map from two dual-number thickenings, restricted to the
diagonal, is the sum of its tangent maps on the axes.
Source: Stacks Project, Tag 0B2B, proof of Lemma 33.16.2.
(blueprint: lem-ag-dual-numbers-diagonal-tangent-addition)

Proof: Pull the map back to the iterated thickening using its two projections.
Its sections are double dual numbers. The two axes retain respectively the
constant and first infinitesimal coefficient and the constant and second
infinitesimal coefficient. The diagonal ring map sends both infinitesimals to
epsilon and their product to zero. Therefore its epsilon coefficient is the
sum of the two axis coefficients on every open. These coefficients are the
relative derivations defining `omegaHom`. Transport them along the three given
equalities of reductions, so they all take values in `g_* O_S`. The universal
property of relative differentials takes their sum to the sum of the induced
module morphisms. Sheafification and the pullback-pushforward adjunction also
preserve addition, giving the asserted equality. This applies over any base,
including the empty scheme, and requires no group law or smoothness. -/
theorem omegaHom_diagonal_add {S : Scheme.{u}} (X : Over S)
    (f : Scheme.dualNumbersOver S ⊗ Scheme.dualNumbersOver S ⟶ X)
    (g : S ⟶ X.left)
    (hd : S.dualNumbersι ≫
      (lift (𝟙 (Scheme.dualNumbersOver S)) (𝟙 (Scheme.dualNumbersOver S)) ≫ f).left = g)
    (h₁ : S.dualNumbersι ≫
      (lift (𝟙 (Scheme.dualNumbersOver S))
        (toUnit (Scheme.dualNumbersOver S) ≫ Scheme.dualNumbersιOver S) ≫ f).left = g)
    (h₂ : S.dualNumbersι ≫
      (lift (toUnit (Scheme.dualNumbersOver S) ≫ Scheme.dualNumbersιOver S)
        (𝟙 (Scheme.dualNumbersOver S)) ≫ f).left = g) :
    (Scheme.Modules.pullbackCongr hd).inv.app X.hom.cotangentSheaf ≫
      omegaHom X (lift (𝟙 _) (𝟙 _) ≫ f) =
    (Scheme.Modules.pullbackCongr h₁).inv.app X.hom.cotangentSheaf ≫
      omegaHom X (lift (𝟙 _) (toUnit _ ≫ Scheme.dualNumbersιOver S) ≫ f) +
    (Scheme.Modules.pullbackCongr h₂).inv.app X.hom.cotangentSheaf ≫
      omegaHom X (lift (toUnit _ ≫ Scheme.dualNumbersιOver S) (𝟙 _) ≫ f) := by
  rw [omegaHom_transport, omegaHom_transport, omegaHom_transport]
  apply homOfDerivation_add_of_coefficients
  exact infDerivation_diagonal_coefficients X f g hd h₁ h₂

end AlgebraicGeometry.GrpObj
