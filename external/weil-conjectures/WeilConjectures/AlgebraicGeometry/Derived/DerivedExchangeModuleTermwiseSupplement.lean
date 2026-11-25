/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.Derived.DerivedExactMateSupplement

/-!
# The unbounded module exchange on K-injective representatives

Source: Stacks Project, sites-cohomology.tex, Tags 0736 and 07A7; derived.tex,
Tags 070I, 070K and 0DVC. Blueprint main-20261015, definition-derived-base-change-map, final
paragraph. (blueprint: lem-weil-pbc-derived-exchange-module-termwise).

The comparison below is the agent-formulated unbounded representative statement,
using the exact inverse-image mate of `definition-derived-base-change-map`.
The three auxiliary definitions spell out its canonical maps, without additional choices.
-/

@[expose] public section

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local irreducible] upperStar lowerStar squareUpperStarIso
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors Functor.mapDerivedCategoryFactorsh
  Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnit Functor.rightDerivedFunctorUnitQ
  Functor.rightDerivedFunctorObjQIso
  Functor.mapDerivedCategoryNatIso

private theorem factorsh_hom
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [CategoryTheory.Limits.PreservesFiniteLimits F]
    [CategoryTheory.Limits.PreservesFiniteColimits F] (K : CochainComplex C ℤ) :
    F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient C (.up ℤ)).obj K) =
      F.mapDerivedCategoryFactors.hom.app K := by
  rw [Functor.mapDerivedCategoryFactorsh_hom_app]
  simp only [DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso, Functor.mapHomotopyCategoryFactors,
    Quotient.lift.isLift_hom, Quotient.lift.isLift_inv]
  repeat erw [CategoryTheory.Functor.map_id]
  repeat erw [Category.comp_id]
  repeat erw [Category.id_comp]

private theorem factorsh_inv
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [CategoryTheory.Limits.PreservesFiniteLimits F]
    [CategoryTheory.Limits.PreservesFiniteColimits F] (K : CochainComplex C ℤ) :
    F.mapDerivedCategoryFactorsh.inv.app ((HomotopyCategory.quotient C (.up ℤ)).obj K) =
      F.mapDerivedCategoryFactors.inv.app K := by
  apply (cancel_epi (F.mapDerivedCategoryFactorsh.hom.app
    ((HomotopyCategory.quotient C (.up ℤ)).obj K))).mp
  rw [Iso.hom_inv_id_app, factorsh_hom]
  erw [Iso.hom_inv_id_app]
  rfl

private theorem unitQ_homotopy
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] (K : CochainComplex C ℤ) :
    F.rightDerivedFunctorUnitQ K =
      F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient C (.up ℤ)).obj K) := by
  simp only [Functor.rightDerivedFunctorUnitQ,
    show (DerivedCategory.quotientCompQhIso D).inv.app
      ((F.mapHomologicalComplex (.up ℤ)).obj K) = 𝟙 _ from rfl,
    show (DerivedCategory.quotientCompQhIso C).hom.app K = 𝟙 _ from rfl,
    Category.id_comp]
  erw [F.rightDerivedFunctor.map_id, Category.comp_id]

private theorem Qh_map_quotient
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {K L : CochainComplex C ℤ} (a : K ⟶ L) :
    DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map a) =
      DerivedCategory.Q.map a := by
  have h := DerivedCategory.quotientCompQhIso_hom_naturality a
  change _ ≫ 𝟙 _ = 𝟙 _ ≫ _ at h
  simpa only [Category.comp_id, Category.id_comp] using h

private theorem square_factors
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    [Abelian C] [Abelian D] [Abelian C'] [Abelian D']
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory C'] [HasDerivedCategory D']
    (G : C ⥤ C') (L : C ⥤ D) (L' : C' ⥤ D') (H : D ⥤ D')
    [G.Additive] [L.Additive] [L'.Additive] [H.Additive]
    [CategoryTheory.Limits.PreservesFiniteLimits G]
    [CategoryTheory.Limits.PreservesFiniteColimits G]
    [CategoryTheory.Limits.PreservesFiniteLimits L]
    [CategoryTheory.Limits.PreservesFiniteColimits L]
    [CategoryTheory.Limits.PreservesFiniteLimits L']
    [CategoryTheory.Limits.PreservesFiniteColimits L']
    [CategoryTheory.Limits.PreservesFiniteLimits H]
    [CategoryTheory.Limits.PreservesFiniteColimits H]
    (e : G ⋙ L' ≅ L ⋙ H) (N : HomotopyCategory C (.up ℤ)) :
    ((Functor.mapDerivedCategoryCompIso G L').hom ≫
      (Functor.mapDerivedCategoryNatIso e).hom ≫
      (Functor.mapDerivedCategoryCompIso L H).inv).app (DerivedCategory.Qh.obj N) ≫
      H.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app N) ≫
      H.mapDerivedCategoryFactorsh.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj N) =
    L'.mapDerivedCategory.map (G.mapDerivedCategoryFactorsh.hom.app N) ≫
      L'.mapDerivedCategoryFactorsh.hom.app ((G.mapHomotopyCategory (.up ℤ)).obj N) ≫
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app N) := by
  have h₁ := Functor.mapDerivedCategoryCompIso_hom_app_factorsh G L' N
  have h₂ := Functor.mapDerivedCategoryCompIso_hom_app_factorsh L H N
  have h₃ := Functor.mapDerivedCategoryNatIso_fach e N
  simp only [NatTrans.comp_app, Category.assoc]
  erw [h₂, h₃, ← h₁]
  simp only [Category.assoc]
  erw [Iso.hom_inv_id_app_assoc]

/-- The exact derived adjunction mate satisfies the right-derived unit identity on complexes.
Source: Stacks Project, derived.tex, Tag 0DVC; exact-derived mate factorization
(blueprint: lem-weil-pbc-derived-exchange-module-termwise). -/
theorem derivedExchangeUnitQ
    {C₁ C₂ C₃ C₄ : Type*} [Category C₁] [Category C₂] [Category C₃] [Category C₄]
    [Abelian C₁] [Abelian C₂] [Abelian C₃] [Abelian C₄]
    [HasDerivedCategory C₁] [HasDerivedCategory C₂]
    [HasDerivedCategory C₃] [HasDerivedCategory C₄]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C₁]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C₃]
    {L : C₂ ⥤ C₁} {R : C₁ ⥤ C₂} {L' : C₄ ⥤ C₃} {R' : C₃ ⥤ C₄}
    {G : C₂ ⥤ C₄} {H : C₁ ⥤ C₃}
    [L.Additive] [R.Additive] [L'.Additive] [R'.Additive] [G.Additive] [H.Additive]
    [CategoryTheory.Limits.PreservesFiniteLimits L]
    [CategoryTheory.Limits.PreservesFiniteColimits L]
    [CategoryTheory.Limits.PreservesFiniteLimits L']
    [CategoryTheory.Limits.PreservesFiniteColimits L']
    [CategoryTheory.Limits.PreservesFiniteLimits G]
    [CategoryTheory.Limits.PreservesFiniteColimits G]
    [CategoryTheory.Limits.PreservesFiniteLimits H]
    [CategoryTheory.Limits.PreservesFiniteColimits H]
    (adj : L ⊣ R) (adj' : L' ⊣ R') (e : G ⋙ L' ≅ L ⋙ H)
    (I : CochainComplex C₁ ℤ) :
    G.mapDerivedCategory.map (R.rightDerivedFunctorUnitQ I) ≫
      (mateEquiv adj.mapDerivedCategoryRightDerivedAdjunction
        adj'.mapDerivedCategoryRightDerivedAdjunction
        (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategoryCompIso G L' ≪≫
          Functor.mapDerivedCategoryNatIso e ≪≫
          (Functor.mapDerivedCategoryCompIso L H).symm).hom)).app
          (DerivedCategory.Q.obj I) =
    G.mapDerivedCategoryFactors.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj I) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ e.hom)) (.up ℤ)).app I) ≫
      R'.rightDerivedFunctorUnitQ ((H.mapHomologicalComplex (.up ℤ)).obj I) ≫
      R'.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.inv.app I) := by
  have h := Adjunction.derivedExact_mateEquiv_app_fac adj adj'
    (TwoSquare.mk _ _ _ _ e.hom)
    (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategoryCompIso G L' ≪≫
      Functor.mapDerivedCategoryNatIso e ≪≫ (Functor.mapDerivedCategoryCompIso L H).symm).hom)
    (by
      intro N
      simpa only [Iso.trans_hom, Iso.symm_hom] using square_factors G L L' H e N)
    ((HomotopyCategory.quotient _ _).obj I)
  erw [factorsh_hom, factorsh_inv] at h
  simp only [NatTrans.mapHomotopyCategory_app,
    HomotopyCategory.quotient_obj_as] at h
  erw [Qh_map_quotient] at h
  simp only [unitQ_homotopy]
  convert h using 1 <;> rfl

private theorem representative_comparison
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    [Abelian C] [Abelian D] [Abelian C'] [Abelian D']
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory C'] [HasDerivedCategory D']
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C']
    (F : C ⥤ D) (G : D ⥤ D') (H : C ⥤ C') (F' : C' ⥤ D')
    [F.Additive] [G.Additive] [H.Additive] [F'.Additive]
    [CategoryTheory.Limits.PreservesFiniteLimits G]
    [CategoryTheory.Limits.PreservesFiniteColimits G]
    [CategoryTheory.Limits.PreservesFiniteLimits H]
    [CategoryTheory.Limits.PreservesFiniteColimits H]
    (E : F.rightDerivedFunctor ⋙ G.mapDerivedCategory ⟶
      H.mapDerivedCategory ⋙ F'.rightDerivedFunctor)
    {K : DerivedCategory C} (I : CochainComplex C ℤ) (s : K ≅ DerivedCategory.Q.obj I)
    (J : CochainComplex C' ℤ) (t : H.mapDerivedCategory.obj K ≅ DerivedCategory.Q.obj J)
    (j : (H.mapHomologicalComplex (.up ℤ)).obj I ⟶ J)
    (α : ((F ⋙ G).mapHomologicalComplex (.up ℤ)).obj I ⟶
      ((H ⋙ F').mapHomologicalComplex (.up ℤ)).obj I)
    (hu : G.mapDerivedCategory.map (F.rightDerivedFunctorUnitQ I) ≫
      E.app (DerivedCategory.Q.obj I) =
      G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
      DerivedCategory.Q.map α ≫
      F'.rightDerivedFunctorUnitQ ((H.mapHomologicalComplex (.up ℤ)).obj I) ≫
      F'.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.inv.app I))
    (ht : DerivedCategory.Q.map j ≫ t.inv =
      H.mapDerivedCategoryFactors.inv.app I ≫ H.mapDerivedCategory.map s.inv) :
    G.mapDerivedCategoryFactors.inv.app _ ≫
      G.mapDerivedCategory.map (F.rightDerivedFunctorUnitQ I ≫
        F.rightDerivedFunctor.map s.inv) ≫ E.app K =
      DerivedCategory.Q.map (α ≫ (F'.mapHomologicalComplex (.up ℤ)).map j) ≫
        (F'.rightDerivedFunctorUnitQ J ≫ F'.rightDerivedFunctor.map t.inv) := by
  have hn := E.naturality s.inv
  dsimp only [Functor.comp_map] at hn
  have hj := F'.rightDerivedFunctorUnitQ_naturality j
  rw [Functor.map_comp, Category.assoc, hn]
  rw [reassoc_of% hu]
  erw [Iso.inv_hom_id_app_assoc]
  rw [DerivedCategory.Q.map_comp]
  erw [Category.assoc (DerivedCategory.Q.map α), reassoc_of% hj]
  erw [← F'.rightDerivedFunctor.map_comp, ← ht]
  rw [F'.rightDerivedFunctor.map_comp]

/-- The canonical direct-image comparison on a specified K-injective representative:
`Q(u_*I) ≅ Ru_*(QI) ≅ Ru_*K`, with the second arrow induced by `s.symm`.
Source: Stacks Project, derived.tex, Tags 070K and 070Y
(blueprint: lem-weil-pbc-derived-exchange-module-termwise). -/
noncomputable def moduleExchangeDirectImageIso
    (Λ : Type (u + 1)) [CommRing Λ] {U V : Scheme.{u}} (f : U ⟶ V)
    {K : DerivedCategoryModule Λ U}
    (I : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
    [I.IsKInjective] (s : K ≅ DerivedCategory.Q.obj I) :
    DerivedCategory.Q.obj (((f)_*[ModuleCat.{u + 1} Λ]).mapHomologicalComplex
      (.up ℤ) |>.obj I) ≅ (R((f)_*[ModuleCat.{u + 1} Λ])).obj K :=
  (((f)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorObjQIso I).symm ≪≫
    (R((f)_*[ModuleCat.{u + 1} Λ])).mapIso s.symm

/-- The isomorphism `t = g'⁻¹(s) ≫ φ ≫ Q(j)` associated to the replacement `j`.
Source: Stacks Project, sites-cohomology.tex, Tag 07A7, and derived.tex, Tag 070I
(blueprint: lem-weil-pbc-derived-exchange-module-termwise). -/
noncomputable def moduleExchangeReplacementIso
    (Λ : Type (u + 1)) [CommRing Λ] {X' X : Scheme.{u}} (g' : X' ⟶ X)
    {K : DerivedCategoryModule Λ X}
    {I : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ}
    (s : K ≅ DerivedCategory.Q.obj I)
    {J : CochainComplex (Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ}
    (j : (((g')^*[ModuleCat.{u + 1} Λ]).mapHomologicalComplex (.up ℤ)).obj I ⟶ J)
    [QuasiIso j] :
    (D((g')^*[ModuleCat.{u + 1} Λ])).obj K ≅ DerivedCategory.Q.obj J :=
  (D((g')^*[ModuleCat.{u + 1} Λ])).mapIso s ≪≫
    ((g')^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryFactors.app I ≪≫
    asIso (DerivedCategory.Q.map j)

/-- The complex map `e = Ex⁰_I ≫ f'_*(j)`, using the termwise module mate.
Naturality of the sheaf mate supplies the chain-map condition in every degree.
Source: Stacks Project, sites-cohomology.tex, Tags 0736 and 07A7
(blueprint: lem-weil-pbc-derived-exchange-module-termwise). -/
noncomputable def moduleExchangeRepresentativeMap
    (Λ : Type (u + 1)) [CommRing Λ] {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g)
    (I : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
    {J : CochainComplex (Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ}
    (j : (((g')^*[ModuleCat.{u + 1} Λ]).mapHomologicalComplex (.up ℤ)).obj I ⟶ J) :
    (((f)_*[ModuleCat.{u + 1} Λ] ⋙ (g)^*[ModuleCat.{u + 1} Λ]).mapHomologicalComplex
      (.up ℤ)).obj I ⟶
        (((f')_*[ModuleCat.{u + 1} Λ]).mapHomologicalComplex (.up ℤ)).obj J :=
  (NatTrans.mapHomologicalComplex
    (baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq) (.up ℤ)).app I ≫
    (((f')_*[ModuleCat.{u + 1} Λ]).mapHomologicalComplex (.up ℤ)).map j

/-- The specified unbounded module exchange is computed on any K-injective representative
and any K-injective replacement of its inverse image. The two sides are respectively
`σsrc ≫ Ex_K` and `Q(e) ≫ χ_(J,t)`, with `χ_(I,s)`, `t`, and `e` explicitly defined above.
Consequently conjugating `Q(e)` by the displayed comparison isomorphisms always yields
this fixed exchange mate. This includes bounded below injective representatives, and
requires no K-injectivity of the inverse image of `I`.

Source: Stacks Project, sites-cohomology.tex, Tags 0736 and 07A7; derived.tex,
Tags 070I, 070K, 08BJ and 0DVC; blueprint main-20261015, definition-derived-base-change-map, final
paragraph (blueprint: lem-weil-pbc-derived-exchange-module-termwise).

Proof: the composition and natural-isomorphism factorization identities normalize the
exact derived inverse-image square. Apply the general exact-derived mate identity on
homotopy complexes and identify its factors with the complex-level comparisons.
Naturality in `s.inv` transports this identity from `Q(I)` to `K`. Naturality of the
right-derived unit along `j`, and cancellation in the explicit definition of `t`,
identify the resulting right side with `Q(e) ≫ χ_(J,t)`. -/
theorem derivedExchangeModuleTermwise
    (Λ : Type (u + 1)) [CommRing Λ] {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g)
    (K : DerivedCategoryModule Λ X)
    (I : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
    [I.IsKInjective] (s : K ≅ DerivedCategory.Q.obj I)
    (J : CochainComplex (Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
    [J.IsKInjective]
    (j : (((g')^*[ModuleCat.{u + 1} Λ]).mapHomologicalComplex (.up ℤ)).obj I ⟶ J)
    [QuasiIso j] :
    ((g)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryFactors.inv.app
        ((((f)_*[ModuleCat.{u + 1} Λ]).mapHomologicalComplex (.up ℤ)).obj I) ≫
      (D((g)^*[ModuleCat.{u + 1} Λ])).map (moduleExchangeDirectImageIso Λ f I s).hom ≫
      (exactDerivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app K =
    DerivedCategory.Q.map (moduleExchangeRepresentativeMap Λ sq I j) ≫
      (moduleExchangeDirectImageIso Λ f' J (moduleExchangeReplacementIso Λ g' s j)).hom := by
  let F := (f)_*[ModuleCat.{u + 1} Λ]
  let G := (g)^*[ModuleCat.{u + 1} Λ]
  let H := (g')^*[ModuleCat.{u + 1} Λ]
  let F' := (f')_*[ModuleCat.{u + 1} Λ]
  let E := exactDerivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq
  let α := (NatTrans.mapHomologicalComplex
    (baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq) (.up ℤ)).app I
  have hu := derivedExchangeUnitQ
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f')
    (squareUpperStarIso (ModuleCat.{u + 1} Λ) sq.toCommSq) I
  change G.mapDerivedCategory.map (F.rightDerivedFunctorUnitQ I) ≫
    E.app (DerivedCategory.Q.obj I) =
      G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
      DerivedCategory.Q.map α ≫
      F'.rightDerivedFunctorUnitQ ((H.mapHomologicalComplex (.up ℤ)).obj I) ≫
      F'.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.inv.app I) at hu
  have ht : DerivedCategory.Q.map j ≫ (moduleExchangeReplacementIso Λ g' s j).inv =
      H.mapDerivedCategoryFactors.inv.app I ≫ H.mapDerivedCategory.map s.inv := by
    simp only [moduleExchangeReplacementIso, Iso.trans_inv, Functor.mapIso_inv,
      Iso.app_inv, asIso_inv]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    rfl
  dsimp only [moduleExchangeDirectImageIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [← F.rightDerivedFunctorUnitQ_eq I, ← F'.rightDerivedFunctorUnitQ_eq J]
  change G.mapDerivedCategoryFactors.inv.app _ ≫
    G.mapDerivedCategory.map (F.rightDerivedFunctorUnitQ I ≫
      F.rightDerivedFunctor.map s.inv) ≫ E.app K =
    DerivedCategory.Q.map (α ≫ (F'.mapHomologicalComplex (.up ℤ)).map j) ≫
      (F'.rightDerivedFunctorUnitQ J ≫
        F'.rightDerivedFunctor.map (moduleExchangeReplacementIso Λ g' s j).inv)
  exact representative_comparison F G H F' E I s J
    (moduleExchangeReplacementIso Λ g' s j) j α hu ht

end AlgebraicGeometry.Etale
