/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientDiagrams
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalDiagonalRightDerived
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperIntegralRationalScalarComparison
import all WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientsFiniteFree
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import all WeilConjectures.AlgebraicGeometry.Condensed.CondensedFlatCoefficientCalculus
import all WeilConjectures.AlgebraicGeometry.QlbarDirectImageComparison
import all WeilConjectures.AlgebraicGeometry.CondensedQbarScalarBasisSections
import all WeilConjectures.AlgebraicGeometry.CondensedQbarScalarBasisUnitOfSections
import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizedDirectImageComparison

/-! # Finite coefficient scalar comparisons for direct image

Source: diagonal tower coefficient changes, paragraphs (1)--(2).
(blueprint: lem-diagonal-finite-scalar-squares).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward false
set_option linter.privateModule false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl MonObj

-- The generic mate comparison elaborates several derived adjunctions.
/-- A finite point copower gives finite scalar units on schemes; the mate criterion then
reduces coefficient pushforward to additivity of the derived direct image. -/
private theorem finitePush_of_pointCopower {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a]
    [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]
    (I : Type (u + 1)) [Finite I]
    [HasCoproducts.{u + 1} (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) R)]
    (e : (∐ fun _ : I ↦ Mod.regular R) ≅ (Mod.comap a).obj (Mod.regular S)) :
    IsIso (derivedPushHom a f) := by
  classical
  obtain ⟨b, hb, hflat, hunit⟩ := scheme_basis_from_point R S a I e
  have hderived (Z : Scheme.{u})
      (M : DerivedCategory (Mod (Sheaf (ProEt.topology Z) Ab.{u + 1})
        (condensedRingObj R Z))) [HasCoproduct (fun _ : I ↦ M)] :
      IsIso (Sigma.desc fun i ↦ Mod.qbar_scalarUnitLeg
        (coefficientMap a Z) (b Z i) M) := by
    let : HasColimitsOfSize.{u + 1, u + 1}
        (Mod (Sheaf (ProEt.topology Z) Ab.{u + 1}) (condensedRingObj R Z)) :=
      IsGrothendieckAbelian.hasColimits _
    let : HasCoproducts.{u + 1}
        (Mod (Sheaf (ProEt.topology Z) Ab.{u + 1}) (condensedRingObj R Z)) :=
      fun J ↦ HasColimitsOfShape.of_small.{u + 1, u + 1} _ (Discrete J)
    exact qbar_isIso_unit _ (b Z) (fun N ↦ hunit Z N) M
  have hcomp (M : DerivedCategory
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X))) :
      IsIso ((derivedPushHom a f).app M) := by
    have : HasCoproduct (fun _ : I ↦ M) :=
      (coefficientDerivedCoproducts R X I).has_colimit _
    have : HasCoproduct (fun _ : I ↦ R((f)_*⟦R⟧).obj M) :=
      (coefficientDerivedCoproducts R Y I).has_colimit _
    have : (Mod.comap (D := Sheaf (ProEt.topology Y) Ab.{u + 1})
        (coefficientMap a Y)).ReflectsIsomorphisms :=
      Mod.restrictionReflectsIsomorphisms _
    have : (Mod.comap (D := Sheaf (ProEt.topology Y) Ab.{u + 1})
        (coefficientMap a
          Y)).mapDerivedCategory.ReflectsIsomorphisms := reflectsDerivedIsomorphisms _
    have hκ : IsIso (mateEquiv
        (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap
          a X))
        (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap
          a Y))
        (derivedPushHom a f)) := by
      unfold derivedPushHom
      exact Adjunction.isIso_mate_pushHomOfComapIso _ _ _
    refine centralUnitCopowerExplicit
      (G := R((f)_*⟦R⟧))
      (G' := R((f)_*⟦S⟧))
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap
        a X))
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap
        a Y))
      (derivedPushHom a f) hκ M I
      (fun i ↦ qbar_derivedCenter (Mod.qbar_scalarNatEndo (b X i)))
      (fun i ↦ qbar_derivedCenter (Mod.qbar_scalarNatEndo (b Y i))) ?_ ?_ ?_ ?_
    · intro i K
      exact qbar_lowerStar_derivedScalarEndo_of_eq f (b X i) (b Y i) (hb f i) K
    · simpa only [Mod.qbar_scalarUnitLeg_eq] using hderived X M
    · simpa only [Mod.qbar_scalarUnitLeg_eq] using
        hderived Y (R((f)_*⟦R⟧).obj M)
    · have : Finite I := inferInstance
      have : R((f)_*⟦R⟧).Additive := inferInstance
      have : PreservesFiniteCoproducts R((f)_*⟦R⟧) :=
        inferInstance
      have : PreservesColimitsOfShape (Discrete I)
          R((f)_*⟦R⟧) := inferInstance
      exact inferInstanceAs (IsIso (sigmaComparison
        R((f)_*⟦R⟧) (fun _ : I ↦ M)))
  exact NatIso.isIso_of_isIso_app _

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] RestrictionSquare.mate
  Functor.leftDerivedFunctor

section ModelComparison
universe a b v w
variable {A : Type a} {B : Type b} [Category.{v} A] [Category.{w} B]
  [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
  [Abelian.HasKInjectiveResolutions A]
  (F : A ⥤ B) [F.Additive]

private def modelIso (R : DiagonalRightDerived F) : F.rightDerivedFunctor ≅ R.R := by
  let := R.universal
  let := canonicalDiagonalUnit_universal F
  exact Functor.rightDerivedUnique _ _ (canonicalDiagonalUnit F) R.η
    (HomologicalComplex.quasiIso A (.up ℤ))

private theorem modelIso_fac (R : DiagonalRightDerived F) (P : CochainComplex A ℤ) :
    F.rightDerivedFunctorUnitQ P ≫ (modelIso F R).hom.app (DerivedCategory.Q.obj P) =
      R.η.app P := by
  let := R.universal
  let := canonicalDiagonalUnit_universal F
  simpa only [canonicalDiagonalUnit, modelIso, Functor.rightDerivedUnique,
    Functor.rightDerivedNatIso_hom,
    Iso.refl_hom, NatTrans.id_app, Category.id_comp] using
    Functor.rightDerivedNatTrans_app F.rightDerivedFunctor R.R
      (canonicalDiagonalUnit F) R.η (HomologicalComplex.quasiIso A (.up ℤ))
      (𝟙 _) P
end ModelComparison

section SquareNormalization
universe a₀ v₀ w₀ w₁
variable {A B C D : Type a₀}
  [Category.{v₀} A] [Category.{v₀} B] [Category.{v₀} C] [Category.{v₀} D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory.{w₀} A] [HasDerivedCategory.{w₀} B]
  [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₁} D]
  [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions C]
  (F : A ⥤ B) (G : C ⥤ D) [F.Additive] [G.Additive]
  (U : A ⥤ C) (V : B ⥤ D) [U.Additive] [V.Additive]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  [PreservesFiniteLimits V] [PreservesFiniteColimits V]
  [U.PreservesKInjectiveComplexes] (e : F ⋙ V ≅ U ⋙ G)

private theorem canonicalSquare_normalization (P : CochainComplex A ℤ) :
    V.mapDerivedCategory.map (F.rightDerivedFunctorUnitQ P) ≫
        (derived_square F G U V e).hom.app (DerivedCategory.Q.obj P) ≫
        G.rightDerivedFunctor.map (U.mapDerivedCategoryFactors.hom.app P) =
      V.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app P) ≫
        G.rightDerivedFunctorUnitQ ((U.mapHomologicalComplex (.up ℤ)).obj P) := by
  have hn := (derived_square F G U V e).hom.naturality
    ((DerivedCategory.quotientCompQhIso A).hom.app P)
  have hu : U.mapDerivedCategoryFactorsh.inv.app
        ((HomotopyCategory.quotient _ _).obj P) ≫
      U.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso A).hom.app P) ≫
        U.mapDerivedCategoryFactors.hom.app P =
      (DerivedCategory.quotientCompQhIso C).hom.app
        ((U.mapHomologicalComplex (.up ℤ)).obj P) := by
    rw [← cancel_epi (U.mapDerivedCategoryFactorsh.hom.app _),
      Iso.hom_inv_id_app_assoc, U.mapDerivedCategoryFactorsh_hom_app]
    simp [Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv]
  have hv : V.mapDerivedCategory.map
        ((DerivedCategory.quotientCompQhIso B).inv.app
          ((F.mapHomologicalComplex (.up ℤ)).obj P)) ≫
      V.mapDerivedCategoryFactorsh.hom.app
        ((F.mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient _ _).obj P)) =
      V.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
        (DerivedCategory.quotientCompQhIso D).inv.app
          ((V.mapHomologicalComplex (.up ℤ)).obj
            ((F.mapHomologicalComplex (.up ℤ)).obj P)) := by
    erw [V.mapDerivedCategoryFactorsh_hom_app]
    simp [Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv,
      ← Functor.map_comp, ← Category.assoc, HomotopyCategory.quotient_obj_as]
  have he := (DerivedCategory.quotientCompQhIso D).inv.naturality
    ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app P)
  simp only [Functor.rightDerivedFunctorUnitQ, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn]
  erw [reassoc_of% (square_fac F G U V e
    ((HomotopyCategory.quotient _ _).obj P))]
  rw [← Functor.map_comp, ← Functor.map_comp, hu, ← Category.assoc, hv]
  simp only [Category.assoc, NatTrans.mapHomotopyCategory_app,
    HomotopyCategory.quotient_obj_as]
  erw [← reassoc_of% he]
  rfl

private theorem transportedSquare_normalization
    (R : DiagonalRightDerived G) (P : CochainComplex A ℤ) :
    V.mapDerivedCategory.map (F.rightDerivedFunctorUnitQ P) ≫
        (derived_square F G U V e ≪≫
          Functor.isoWhiskerLeft U.mapDerivedCategory (modelIso G R)).hom.app
            (DerivedCategory.Q.obj P) ≫
        R.R.map (U.mapDerivedCategoryFactors.hom.app P) =
      V.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app P) ≫
        R.η.app ((U.mapHomologicalComplex (.up ℤ)).obj P) := by
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Category.assoc]
  erw [← (modelIso G R).hom.naturality
    (U.mapDerivedCategoryFactors.hom.app P)]
  have hn := congrArg
    (fun k : V.mapDerivedCategory.obj
        (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P)) ⟶
      G.rightDerivedFunctor.obj
        (DerivedCategory.Q.obj ((U.mapHomologicalComplex (.up ℤ)).obj P)) ↦
      k ≫ (modelIso G R).hom.app
      (DerivedCategory.Q.obj ((U.mapHomologicalComplex (.up ℤ)).obj P)))
    (canonicalSquare_normalization F G U V e P)
  simpa only [Functor.comp_obj, Category.assoc, modelIso_fac] using hn

private def transportedSquare (R : DiagonalRightDerived G) :
    DiagonalTrace.ExactSquareOfUniverses F G U V (canonicalDiagonalRightDerived F) R e where
  iso := derived_square F G U V e ≪≫
    Functor.isoWhiskerLeft U.mapDerivedCategory (modelIso G R)
  normalization := transportedSquare_normalization F G U V e R
end SquareNormalization

private theorem pushHom_modelIso
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {U : B ⥤ A} {L' : C ⥤ D} {U' : D ⥤ C}
    (adj : L ⊣ U) (adj' : L' ⊣ U') {G G' : A ⥤ C} {H : B ⥤ D}
    (κ : H ⋙ U' ≅ U ⋙ G) (e : G ≅ G') (K : A) :
    (Adjunction.pushHomOfComapIso adj adj'
      (κ ≪≫ Functor.isoWhiskerLeft U e)).app K =
      L'.map (e.inv.app K) ≫ (Adjunction.pushHomOfComapIso adj adj' κ).app K := by
  have h₀ := unit_mateEquiv_symm adj adj' (TwoSquare.mk _ _ _ _ κ.inv) K
  change G.map (adj.unit.app K) ≫ κ.inv.app (L.obj K) =
    adj'.unit.app (G.obj K) ≫
      U'.map ((Adjunction.pushHomOfComapIso adj adj' κ).app K) at h₀
  have h₁ := unit_mateEquiv_symm adj adj'
    (TwoSquare.mk _ _ _ _ (κ ≪≫ Functor.isoWhiskerLeft U e).inv) K
  change G'.map (adj.unit.app K) ≫
      (κ ≪≫ Functor.isoWhiskerLeft U e).inv.app (L.obj K) =
    adj'.unit.app (G'.obj K) ≫ U'.map
      ((Adjunction.pushHomOfComapIso adj adj'
        (κ ≪≫ Functor.isoWhiskerLeft U e)).app K) at h₁
  apply (adj'.homEquiv (G'.obj K) (H.obj (L.obj K))).injective
  rw [adj'.homEquiv_naturality_left, adj'.homEquiv_unit, adj'.homEquiv_unit]
  rw [← h₁, ← h₀]
  simpa only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
    Functor.whiskerLeft_app, Functor.comp_obj, Functor.id_obj, Category.assoc] using
    congrArg (fun k ↦ k ≫ κ.inv.app (L.obj K)) (e.inv.naturality (adj.unit.app K))

private theorem pushHom_modelIso_isIso
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {U : B ⥤ A} {L' : C ⥤ D} {U' : D ⥤ C}
    (adj : L ⊣ U) (adj' : L' ⊣ U') {G G' : A ⥤ C} {H : B ⥤ D}
    (κ : H ⋙ U' ≅ U ⋙ G) (e : G ≅ G') (K : A)
    [IsIso ((Adjunction.pushHomOfComapIso adj adj' κ).app K)] :
    IsIso ((Adjunction.pushHomOfComapIso adj adj'
      (κ ≪≫ Functor.isoWhiskerLeft U e)).app K) := by
  rw [pushHom_modelIso]
  infer_instance

section ScalarSquares
variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]
  [∀ T : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a T))]
  {X S : Scheme.{u}} (f : X ⟶ S)

private def flatRestrictionSquare
    (R : DiagonalRightDerived (CondensedRing.lowerStar Λ f)) :
    RestrictionSquare a f R
      (canonicalDiagonalRightDerived (CondensedRing.lowerStar Λ' f)) := by
  exact transportedSquare
    (CondensedRing.lowerStar Λ' f) (CondensedRing.lowerStar Λ f)
    (Mod.comap (coefficientMap a X)) (Mod.comap (coefficientMap a S))
    (CondensedRing.comapLowerStarIso a f) R

private theorem flatRestrictionSquare_mate_isIso
    (R : DiagonalRightDerived (CondensedRing.lowerStar Λ f))
    (K : DerivedCategory (Modules Λ X))
    [IsIso ((CondensedRing.derivedPushHom a f).app K)] :
    IsIso (((flatRestrictionSquare a f R).mate a).app K) := by
  let adjX := Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X)
  let adjS := Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a S)
  let κ := CondensedRing.derivedComapLowerStarIso a f
  let e := modelIso (CondensedRing.lowerStar Λ f) R
  let : IsIso ((Adjunction.pushHomOfComapIso adjX adjS κ).app K) :=
    inferInstanceAs (IsIso ((CondensedRing.derivedPushHom a f).app K))
  unfold RestrictionSquare.mate flatRestrictionSquare transportedSquare
  change IsIso ((Adjunction.pushHomOfComapIso adjX adjS
    (κ ≪≫ Functor.isoWhiskerLeft
      (Mod.comap (coefficientMap a X)).mapDerivedCategory e)).app K)
  exact pushHom_modelIso_isIso adjX adjS κ e K

end ScalarSquares

private theorem integralPointBasis (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) :
    ∃ n : ℕ, Nonempty (Mod.finiteFree (Profinite.continuousMapRingObj.{u} ℤ_[l]) n ≅
      (Mod.comap (integralMap l E)).obj
        (Mod.regular (Profinite.padicIntegersRingObj.{u} l E.1))) := by
  classical
  let h : bottomField l ≤ E :=
    show (⊥ : IntermediateField ℚ_[l] (PadicAlgCl l)) ≤ E.1 from bot_le
  obtain ⟨b⟩ := (cartesianCoefficients_finiteFree.{u} l h).1
  let : Algebra (PadicAlgCl.integers l (bottomField l).1)
      (PadicAlgCl.integers l E.1) := (finiteCoefficientIntegersMap l h).toAlgebra
  obtain ⟨θ, _⟩ := continuous_basis_iso.{u}
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ |>.subtype_mk _)
    (finiteCoefficientDegree l h) b (integral_coordinates_continuous l h b)
  obtain ⟨e, eInt, _, heInt, _, _, _, _, q, z, _, _, hz, _⟩ :=
    Profinite.base_coefficient_condensed_identification.{u} l
  let z' : Profinite.continuousMapRingObj.{u} ℤ_[l] ≅
      Profinite.padicIntegersRingObj.{u} l (bottomField l).1 :=
    (Mon.forget _).mapIso z
  have hz' : z'.hom = integralMap l (bottomField l) := by
    ext T a
    apply ULift.ext
    apply ContinuousMap.ext
    intro x
    have hz₀ := hz T.unop a.down x
    change _ = padicIntToIntegers l (bottomField l).1 (a.down x)
    rw [← heInt]
    exact hz₀
  have hs : integralMap l E = z'.hom ≫ finiteCoefficientIntegersPointMap l h := by
    refine Eq.trans ?_ (congrArg
      (fun k : Profinite.continuousMapRingObj.{u} ℤ_[l] ⟶
          Profinite.padicIntegersRingObj.{u} l (bottomField l).1 ↦
        k ≫ finiteCoefficientIntegersPointMap l h) hz'.symm)
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext T
    apply ConcreteCategory.hom_ext
    intro a
    apply ULift.ext
    apply ContinuousMap.ext
    intro x
    rfl
  let : IsMonHom z'.symm.hom := inferInstanceAs (IsMonHom z.inv.hom)
  let : IsMonHom (Iso.refl (Profinite.padicIntegersRingObj.{u} l E.1)).hom :=
    inferInstanceAs (IsMonHom (𝟙 (Profinite.padicIntegersRingObj.{u} l E.1)))
  have ez := Mod.freeRestrictedRegularIsoOfRingIso
    (finiteCoefficientIntegersPointMap l h) (integralMap l E)
    z'.symm (Iso.refl _) (by simpa only [Iso.refl_inv, Iso.symm_inv, Category.comp_id] using hs)
    (finiteCoefficientDegree l h) θ.symm
  exact ⟨finiteCoefficientDegree l h, ⟨ez.symm⟩⟩

attribute [local irreducible] CondensedRing.derivedPushHom
  CondensedRing.derivedComapLowerStarIso Mod.extendScalars

private theorem integralScalarComparison_isIso (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) {X S : Scheme.{u}} (f : X ⟶ S) :
    ∃ hf : ∀ T : Scheme.{u}, PreservesFiniteLimits
      (Mod.extendScalars (coefficientMap (integralMap l E) T)),
      letI := hf
      IsIso (CondensedRing.derivedPushHom (integralMap l E) f) := by
  classical
  obtain ⟨n, ⟨θ⟩⟩ := integralPointBasis.{u} l E
  have hf (T : Scheme.{u}) : PreservesFiniteLimits
      (Mod.extendScalars (coefficientMap (integralMap l E) T)) := by
    obtain ⟨e, _⟩ := pullback_basis_iso
      (Profinite.continuousMapRingObj.{u} ℤ_[l])
      (Profinite.padicIntegersRingObj.{u} l E.1) (integralMap l E) n θ T
    exact finite_free_flat T _ _ _ n e
  let := hf
  let : HasColimitsOfSize.{u + 1, u + 1}
      (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
        (Profinite.continuousMapRingObj.{u} ℤ_[l])) := IsGrothendieckAbelian.hasColimits _
  let : HasCoproducts.{u + 1}
      (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
        (Profinite.continuousMapRingObj.{u} ℤ_[l])) :=
    fun J ↦ HasColimitsOfShape.of_small.{u + 1, u + 1} _ (Discrete J)
  let I := ULift.{u + 1} (Fin n)
  let θ' : (∐ fun _ : I ↦ Mod.regular (Profinite.continuousMapRingObj.{u} ℤ_[l])) ≅
      (Mod.comap (integralMap l E)).obj
        (Mod.regular (Profinite.padicIntegersRingObj.{u} l E.1)) :=
    Sigma.reindex Equiv.ulift
      (fun _ : Fin n ↦ Mod.regular (Profinite.continuousMapRingObj.{u} ℤ_[l])) ≪≫
        (biproduct.isoCoproduct _).symm ≪≫ θ
  exact ⟨hf, CondensedRing.finitePush_of_pointCopower f _ _ (integralMap l E) I θ'⟩

/-- The finite-free and localization direct-image comparisons are invertible on
the shifted root lines. No class, trace or integration identity is included.

Source: blueprint latest, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md, paragraphs (1)--(2).
(blueprint: lem-diagonal-finite-scalar-squares).

Proof: For integral extension choose a finite Z_l basis of O_E. The corresponding
ordinary scalar functors are exact finite-biproduct functors. Exact restriction
commutes with ordinary direct image through comapLowerStarIso. Restriction
preserves K-injectives because its left adjoint is exact. Derive this ordinary
square with its full universal unit; uniqueness of right derivation transports
it to any of the given right-derived models R. This gives the required
RestrictionSquare with exactly its normalization equation on all complexes.
Under scalar restriction its mate is the finite-biproduct direct-image
comparison. Additivity of right-derived direct image makes it invertible.
Restriction reflects isomorphisms, so the displayed integral mate is invertible.

For rationalization scalar extension is exact localization at ell, as given by
the regular coefficient telescope. Restriction again preserves K-injectives,
so the same universal-unit construction supplies the normalized square.
After restriction the scalar mate on the shifted root line is the canonical
comparison for the ell-multiplication telescope on the line in degree -2.
Every complex of this telescope vanishes below -2. Since f is qcqs, bounded
continuity makes its direct-image comparison an isomorphism on every homology
sheaf. Exact filtered colimits identify the target with localization, hence
with the rational scalar image. Homology detects isomorphisms in the derived
category and restriction reflects them, proving the rational assertion.
Both identifications agree with the stated mate: transposing by the scalar
adjunction reduces them to the full-unit normalization already imposed.
The zero line and the identity finite extension satisfy the same equations;
no invertibility assumption on ell is needed to obtain the degree bound. -/
theorem diagonalFinite_scalarSquares
    (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f] :
    (∀ R : DiagonalRightDerived
        (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f),
      ∃ s : RestrictionSquare (integralMap l E) f R
          (canonicalDiagonalRightDerived
            (CondensedRing.lowerStar (Profinite.padicIntegersRingObj.{u} l E.1) f)),
        IsIso ((s.mate (integralMap l E)).app
          (((DerivedCategory.singleFunctor _ 0).obj (zlLine l X))⟦(2 : ℤ)⟧))) ∧
    (∀ R : DiagonalRightDerived
        (CondensedRing.lowerStar (Profinite.padicIntegersRingObj.{u} l E.1) f),
      ∃ s : RestrictionSquare (padicIntegersRingObjToContinuousMapRingObj l E) f R
          (canonicalDiagonalRightDerived
            (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} E.1) f)),
        IsIso ((s.mate (padicIntegersRingObjToContinuousMapRingObj l E)).app
          (((DerivedCategory.singleFunctor _ 0).obj
            (spIntegralTwist X l E))⟦(2 : ℤ)⟧))) := by
  constructor
  · obtain ⟨hf, hi⟩ := integralScalarComparison_isIso l E f
    let := hf
    let := hi
    intro R
    refine ⟨flatRestrictionSquare (integralMap l E) f R, ?_⟩
    exact flatRestrictionSquare_mate_isIso (integralMap l E) f R _
  · have hf : ∀ T : Scheme.{u}, PreservesFiniteLimits
        (Mod.extendScalars
          (coefficientMap (padicIntegersRingObjToContinuousMapRingObj l E) T)) :=
      fun T ↦ (padicIntegers_invertEll T l E).choose_spec.2.choose_spec.2.2.choose_spec.2.2.2
    let := hf
    intro R
    let K := (((DerivedCategory.singleFunctor _ 0).obj
      (spIntegralTwist X l E))⟦(2 : ℤ)⟧)
    have hK : DerivedCategory.TStructure.t.plus K := by
      exact ⟨-2, DerivedCategory.TStructure.t.isGE_shift _ 0 2 (-2)⟩
    have : IsIso ((CondensedRing.derivedPushHom
        (padicIntegersRingObjToContinuousMapRingObj l E) f).app K) :=
      CondensedRing.localizedDirectImageComparison_isIso l E f K hK
    exact ⟨flatRestrictionSquare (padicIntegersRingObjToContinuousMapRingObj l E) f R,
      flatRestrictionSquare_mate_isIso
        (padicIntegersRingObjToContinuousMapRingObj l E) f R K⟩

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
