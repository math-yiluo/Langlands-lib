/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientCategory
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientUnitPush
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientScalars
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientEndpoints
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Scalar transport of the regular coefficient unit along any morphism

Source: current blueprint, diagonal tower coefficient changes, proof (1)--(2),
regular coefficient-unit square (blueprint: lem-sfb-diagonal-scalar-regular-unit-push).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftAdjoint
  Functor.rightAdjoint derivedScalars RestrictionSquare.mate

private theorem mate_transpose
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {E : C ⥤ D} {Res : D ⥤ C} {E' : C' ⥤ D'} {Res' : D' ⥤ C'}
    (ad : E ⊣ Res) (ad' : E' ⊣ Res')
    (R : C ⥤ C') (R' : D ⥤ D') (e : R' ⋙ Res' ≅ Res ⋙ R)
    {U : C'} {V : C} {W : D} (c : U ⟶ R.obj V) (v : E.obj V ⟶ W) :
    ad'.homEquiv _ _
        (E'.map c ≫ (Adjunction.pushHomOfComapIso ad ad' e).app V ≫ R'.map v) =
      c ≫ R.map (ad.homEquiv _ _ v) ≫ e.inv.app W := by
  have hm := unit_mateEquiv_symm ad ad'
    (TwoSquare.mk Res R' R Res' e.inv) V
  change R.map (ad.unit.app V) ≫ e.inv.app (E.obj V) =
    ad'.unit.app (R.obj V) ≫
      Res'.map ((Adjunction.pushHomOfComapIso ad ad' e).app V) at hm
  have hn := e.inv.naturality v
  change R.map (Res.map v) ≫ e.inv.app W =
    e.inv.app (E.obj V) ≫ Res'.map (R'.map v) at hn
  rw [Adjunction.homEquiv_unit, Res'.map_comp, Res'.map_comp]
  rw [← reassoc_of% (ad'.unit.naturality c), ← reassoc_of% hm]
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  rw [hn]

-- The two scalar adjunctions require conversion across dependent coefficient categories.
/-- Scalar extension preserves the canonical regular coefficient-unit adjunct for any
scheme morphism, through the normalized restriction/direct-image mate.
Source: current blueprint, diagonal tower coefficient changes, proof (1)--(2),
regular coefficient-unit square (blueprint: lem-sfb-diagonal-scalar-regular-unit-push).

Proof:
1. Write G and G' for the ordinary pushforwards, r_T for restriction, V_T and V'_T
   for regular modules, b_T for the endpoint's semilinear map, and delta for the
   ordinary restriction/pushforward comparison. The module-adjunction formula sends
   the inverse monoidal unit comparison to the structural coefficient map: on the
   pullback it is t tensor r mapped to t alpha_f(r); restricting to 1 tensor r gives
   alpha_f, and its abelian adjunct is the unit followed by f_* alpha_f.
   This is also `CondensedRing.homEquiv_εIso_inv_hom`. Thus m and m' have underlying
   maps eta_f and eta'_f. Endpoint normalization fixes the underlying maps of b_T
   to a_T. The coefficient-pushforward square and the identity underlying delta give
   m ≫ G(b_X) = b_S ≫ r_S(m') ≫ delta, by faithfulness of the module forgetful functor.
2. Write R_T for derived restriction, h for the given derived square, l_T for the
   exact restriction/single comparison, and sigma for `singlePushComparison`.
   Evaluating the full universal-unit normalization on V'_X gives
   R_S(sigma') ≫ h ≫ D(l_X) = l_S ≫ delta[0] ≫ sigma.
   This is `singlePushComparison_square`; `singlePushComparison_naturality` moves
   ordinary module arrows through sigma.
3. Under the actual scalar adjunction bijection Phi_S, the mate formula and its
   triangle identity give Phi_S(F_S(c) ≫ tau ≫ D'(v)) =
   c ≫ D(Phi_X(v)) ≫ h.inv. Indeed the unit-mate identity is
   eta_S ≫ R_S(tau) = D(eta_X) ≫ h.inv, and naturality moves c and v past it.
4. Transpose the desired equality and insert endpoint normalization
   Phi_T(e_T) = b_T[0] ≫ l_T.inv. For c = m[0] ≫ sigma and v = e_X,
   naturality of sigma and the ordinary square in step 1 rewrite the transpose as
   b_S[0] ≫ r_S(m')[0] ≫ delta[0] ≫ sigma ≫ D(l_X.inv) ≫ h.inv.
   Cancel the invertible factors in step 2 to replace the last four factors by
   l_S.inv ≫ R_S(sigma'). Naturality of l_S at m' rewrites the result as
   b_S[0] ≫ l_S.inv ≫ R_S(m'[0] ≫ sigma'), which is Phi_S(e_S ≫ A').
   Injectivity of Phi_S proves the equation. Only restriction and the supplied
   square are inverted; extension need not be exact. This includes nonflat maps,
   zero coefficient rings, empty schemes, and arbitrary scheme morphisms. -/
theorem scalar_regular_unit_push
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] {X S : Scheme.{u}} (f : X ⟶ S)
    (D : DiagonalRightDerived (CondensedRing.lowerStar Λ f))
    (D' : DiagonalRightDerived (CondensedRing.lowerStar Λ' f))
    (s : RestrictionSquare a f D D')
    (eS : Endpoint a (Mod.regular (condensedRingObj Λ S))
      (Mod.regular (condensedRingObj Λ' S)) (coefficientMap a S))
    (eX : Endpoint a (Mod.regular (condensedRingObj Λ X))
      (Mod.regular (condensedRingObj Λ' X)) (coefficientMap a X)) :
    (derivedScalars a S).map
        ((DerivedCategory.singleFunctor (Modules Λ S) 0).map
            ((CondensedRing.upperStarLowerStarAdjunction Λ f).homEquiv _ _
              (Functor.Monoidal.εIso (CondensedRing.upperStar Λ f)).inv) ≫
          singlePushComparison D (Mod.regular (condensedRingObj Λ X))) ≫
        (s.mate a).app (unit Λ X) ≫ D'.R.map eX.iso.hom =
      eS.iso.hom ≫
        (DerivedCategory.singleFunctor (Modules Λ' S) 0).map
            ((CondensedRing.upperStarLowerStarAdjunction Λ' f).homEquiv _ _
              (Functor.Monoidal.εIso (CondensedRing.upperStar Λ' f)).inv) ≫
          singlePushComparison D' (Mod.regular (condensedRingObj Λ' X)) := by
  let U := Mod.regular (condensedRingObj Λ X)
  let U' := Mod.regular (condensedRingObj Λ' X)
  let m := (CondensedRing.upperStarLowerStarAdjunction Λ f).homEquiv _ _
    (Functor.Monoidal.εIso (CondensedRing.upperStar Λ f)).inv
  let m' := (CondensedRing.upperStarLowerStarAdjunction Λ' f).homEquiv _ _
    (Functor.Monoidal.εIso (CondensedRing.upperStar Λ' f)).inv
  have hm : m ≫ (CondensedRing.lowerStar Λ f).map eX.semilinear.hom =
      eS.semilinear.hom ≫ (Mod.comap (coefficientMap a S)).map m' ≫
        (CondensedRing.comapLowerStarIso a f).hom.app U' := by
    have hm₀ : m.hom = condensedPushforwardHom Λ f :=
      CondensedRing.homEquiv_εIso_inv_hom Λ f
    have hm₁ : m'.hom = condensedPushforwardHom Λ' f :=
      CondensedRing.homEquiv_εIso_inv_hom Λ' f
    apply Mod.Hom.ext
    change m.hom ≫ (lowerStar Ab.{u + 1} f).map eX.semilinear.hom.hom =
      eS.semilinear.hom.hom ≫ m'.hom ≫
        ((CondensedRing.comapLowerStarIso a f).hom.app U').hom
    rw [hm₀, hm₁, eX.semilinear.underlying, eS.semilinear.underlying]
    rw [CondensedRing.comapLowerStarIso, Mod.comapMapModComapIso_hom_app_hom]
    exact (condensedPushforwardHom_comp_map_coefficientMap a f).trans
      (congrArg (fun h => coefficientMap a S ≫ h) (Category.comp_id _)).symm
  have hs := singlePushComparison_square
    (Mod.comap (coefficientMap a X))
    (Mod.comap (coefficientMap a S)) D' D
    (CondensedRing.comapLowerStarIso a f) s U'
  let adS : derivedScalars a S ⊣
      (Mod.comap (coefficientMap a S)).mapDerivedCategory := by
    unfold derivedScalars
    exact Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a S)
  let adX : derivedScalars a X ⊣
      (Mod.comap (coefficientMap a X)).mapDerivedCategory := by
    unfold derivedScalars
    exact Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap a X)
  have hX : adX.homEquiv _ _ eX.iso.hom =
      (DerivedCategory.singleFunctor (Modules Λ X) 0).map
          eX.semilinear.hom ≫
        ((Mod.comap (coefficientMap a X)).mapDerivedCategorySingleFunctor
          0).inv.app U' := by
    with_unfolding_all exact eX.normalization
  have hS : adS.homEquiv _ _ eS.iso.hom =
      (DerivedCategory.singleFunctor (Modules Λ S) 0).map eS.semilinear.hom ≫
        ((Mod.comap (coefficientMap a S)).mapDerivedCategorySingleFunctor 0).inv.app
          (Mod.regular (condensedRingObj Λ' S)) := by
    with_unfolding_all exact eS.normalization
  apply (adS.homEquiv (unit Λ S) _).injective
  unfold RestrictionSquare.mate
  with_unfolding_all
    change adS.homEquiv _ _
      ((derivedScalars a S).map
        ((DerivedCategory.singleFunctor (Modules Λ S) 0).map m ≫
          singlePushComparison D U) ≫
        (Adjunction.pushHomOfComapIso adX adS s.iso).app _ ≫ D'.R.map eX.iso.hom) = _
  rw [mate_transpose]
  rw [hX, adS.homEquiv_naturality_right, hS]
  simp only [m, U, U']
  apply (cancel_mono (s.iso.hom.app (unit Λ' X))).mp
  apply (cancel_mono (D.R.map
    (((Mod.comap (coefficientMap a X)).mapDerivedCategorySingleFunctor
      0).hom.app U'))).mp
  simp only [Category.assoc, Functor.map_comp]
  have hcancel :
      D.R.map (((Mod.comap (coefficientMap a X)).mapDerivedCategorySingleFunctor
        0).inv.app U') ≫
      D.R.map (((Mod.comap (coefficientMap a X)).mapDerivedCategorySingleFunctor
        0).hom.app U') = 𝟙 _ := by
    rw [← D.R.map_comp, Iso.inv_hom_id_app, D.R.map_id]
  simp only [Iso.inv_hom_id_app_assoc]
  erw [hcancel]
  erw [Category.comp_id]
  erw [hs]
  have hn := ((Mod.comap (coefficientMap a S)).mapDerivedCategorySingleFunctor 0).hom.naturality m'
  change (Mod.comap (coefficientMap a S)).mapDerivedCategory.map
      ((DerivedCategory.singleFunctor (Modules Λ' S) 0).map m') ≫
        ((Mod.comap (coefficientMap a S)).mapDerivedCategorySingleFunctor 0).hom.app _ =
    ((Mod.comap (coefficientMap a S)).mapDerivedCategorySingleFunctor 0).hom.app _ ≫
      (DerivedCategory.singleFunctor (Modules Λ S) 0).map
        ((Mod.comap (coefficientMap a S)).map m') at hn
  erw [reassoc_of% hn]
  erw [Iso.inv_hom_id_app_assoc]
  erw [← singlePushComparison_naturality D eX.semilinear.hom]
  have hsingle := congrArg (DerivedCategory.singleFunctor (Modules Λ S) 0).map hm
  simpa only [m, m', U, U', Functor.map_comp, Category.assoc] using
    congrArg (fun k => k ≫ singlePushComparison D
      ((Mod.comap (coefficientMap a X)).obj U')) hsingle

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
