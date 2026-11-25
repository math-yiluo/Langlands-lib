/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicFreeTensorCone
public import WeilConjectures.AlgebraicGeometry.Adic.AdicOrdinaryTensorDiagram
import all WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulFiniteQuotientComparison
import WeilConjectures.AlgebraicGeometry.CompletedConstantAlgebraFlatQuotients
import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.CategoryTheory.ConstantModuleDerivedProjection.ConstantModuleOrdinaryRealization
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionConstraintCoherence
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Ordinary completed realization and the quotient coefficient tensors

Source: Stacks Project, Tag 09C6; Modules on Sites, Tags 093J--093M.
This comparison takes place entirely in the abelian module categories.
(blueprint: lem-weil-pbc-finite-perfect-adic-ordinary-coefficient-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped TensorProduct
-- Only the binary tensor comparison and its naturality are needed below.
private structure TensorComparison {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) where
  iso : ∀ M N, F.obj (M ⊗ N) ≅ F.obj M ⊗ F.obj N
  natural : ∀ {M M' N N'} (f : M ⟶ M') (g : N ⟶ N'),
    F.map (f ⊗ₘ g) ≫ (iso M' N').hom =
      (iso M N).hom ≫ (F.map f ⊗ₘ F.map g)

private def TensorComparison.comp
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
    {F : C ⥤ D} {G : D ⥤ E} (f : TensorComparison F) (g : TensorComparison G) :
    TensorComparison (F ⋙ G) where
  iso M N := G.mapIso (f.iso M N) ≪≫ g.iso (F.obj M) (F.obj N)
  natural a b := by
    simp only [Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom, ← G.map_comp_assoc]
    rw [f.natural]
    simp only [G.map_comp, Category.assoc]
    rw [g.natural]

private def TensorComparison.ofMonoidal
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.Monoidal] :
    TensorComparison F where
  iso M N := (Functor.Monoidal.μIso F M N).symm
  natural f g := (Functor.OplaxMonoidal.δ_natural F f g).symm

private def TensorComparison.ofObjectEq
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) (G : C → D) (h : ∀ M, F.obj M = G M)
    (gmap : ∀ {M N}, (M ⟶ N) → (G M ⟶ G N))
    (hmap : ∀ {M N} (f : M ⟶ N),
      F.map f = eqToHom (h M) ≫ gmap f ≫ eqToHom (h N).symm)
    (e : ∀ M N, G (M ⊗ N) ≅ G M ⊗ G N)
    (he : ∀ {M M' N N'} (f : M ⟶ M') (g : N ⟶ N'),
      gmap (f ⊗ₘ g) ≫ (e M' N').hom =
        (e M N).hom ≫ (gmap f ⊗ₘ gmap g)) : TensorComparison F where
  iso M N := eqToIso (h (M ⊗ N)) ≪≫ e M N ≪≫
    ((eqToIso (h M)).symm ⊗ᵢ (eqToIso (h N)).symm)
  natural f g := by
    simp only [Iso.trans_hom, tensorIso_hom, Iso.symm_hom, eqToIso.hom, eqToIso.inv]
    rw [hmap]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [reassoc_of% he f g]
    rw [hmap f, hmap g]
    simp only [tensorHom_comp_tensorHom, eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp]

private theorem TensorComparison.natural_inv
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D]
    {F : C ⥤ D} (t : TensorComparison F)
    {M M' N N'} (f : M ⟶ M') (g : N ⟶ N') :
    (t.iso M N).inv ≫ F.map (f ⊗ₘ g) =
      (F.map f ⊗ₘ F.map g) ≫ (t.iso M' N').inv := by
  apply (cancel_mono (t.iso M' N').hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [t.natural, Iso.inv_hom_id_assoc]

private def TensorComparison.diagramIso
    {C D J : Type*} [Category* C] [Category* D] [Category* J]
    [MonoidalCategory C] [MonoidalCategory D]
    {F : C ⥤ D} (t : TensorComparison F)
    (Q : J ⥤ C) (B : J ⥤ D) (e : Q ⋙ F ≅ B) :
    F ⋙ curriedTensor D ⋙ (Functor.whiskeringLeft J D D).obj B ≅
      (curriedTensor C ⋙ (Functor.whiskeringLeft J C C).obj Q) ⋙
        (Functor.whiskeringRight J C D).obj F := by
  refine NatIso.ofComponents (fun M ↦ NatIso.ofComponents
    (fun n ↦ whiskerLeftIso (F.obj M) (e.app n).symm ≪≫
      (t.iso M (Q.obj n)).symm) ?_) ?_
  · rename_i M
    intro m n f
    change F.obj M ◁ B.map f ≫
        (F.obj M ◁ e.inv.app n ≫ (t.iso M (Q.obj n)).inv) =
      (F.obj M ◁ e.inv.app m ≫ (t.iso M (Q.obj m)).inv) ≫
        F.map (M ◁ Q.map f)
    rw [← Category.assoc, ← whiskerLeft_comp, e.inv.naturality,
      whiskerLeft_comp, Category.assoc, Category.assoc]
    congr 1
    have h := (t.natural_inv (𝟙 M) (Q.map f)).symm
    rw [F.map_id] at h
    simpa only [Functor.comp_obj, Functor.comp_map, id_tensorHom] using h
  · intro M N f
    apply NatTrans.ext
    funext n
    change F.map f ▷ B.obj n ≫
        (F.obj N ◁ e.inv.app n ≫ (t.iso N (Q.obj n)).inv) =
      (F.obj M ◁ e.inv.app n ≫ (t.iso M (Q.obj n)).inv) ≫
        F.map (f ▷ Q.obj n)
    rw [← whisker_exchange_assoc, Category.assoc]
    congr 1
    have h := (t.natural_inv f (𝟙 (Q.obj n))).symm
    rw [F.map_id] at h
    simpa only [Functor.comp_obj, tensorHom_id] using h

namespace AlgebraicGeometry.Scheme

-- Pin the coefficient universe of the site instead of inferring an ambient lift.
private theorem comparisonSiteSmall (X : Scheme.{t}) : EssentiallySmall.{t + 1} X.ProEt :=
  EssentiallySmall.mk' (AsSmall.equiv : X.ProEt ≌ AsSmall.{t + 1} X.ProEt)
attribute [local instance] comparisonSiteSmall

@[instance_reducible] private def constantModulesMonoidal
    (X : Scheme.{t}) (A : Type t) [CommRing A] :
    MonoidalCategory (SheafOfModules.{t + 1} (adicModuleRing X A)) :=
  CategoryTheory.ConstantScalarRestriction.ringMonoidal.{t + 1, t}
    (ProEt.topology X) (ULift.{t + 1} A)
attribute [local instance] constantModulesMonoidal

attribute [local instance] finitePerfectModelsAbLocallyBijective

attribute [local irreducible] completedAdicChangeData completedAdicRing

private theorem ordinaryScalar_exact
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A) :
    PreservesFiniteLimits (completedAdicScalarExtension X d) ∧
      PreservesFiniteColimits (completedAdicScalarExtension X d) := by
  obtain ⟨r, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp d.finitelyGenerated
  let B := ULift.{t + 1} A
  let I := Ideal.span (Set.range (fun i ↦ (ULift.up (a i) : B)))
  let : IsNoetherianRing A := d.noetherian
  let : IsNoetherianRing B := isNoetherianRing_of_surjective A B
    (ULift.ringEquiv : B ≃+* A).symm.toRingHom (ULift.ringEquiv.symm.surjective)
  exact (exactFunctor_iff _).1
    (completed_constant_algebra_flat_quotients X I (completedAdicCommRing X d)
      (completionRingIso X d r a ha) (completedAdicScalar X d)
      (completionRingIso_scalar X d r a ha)).2.1

private def coefficientLiftIso
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal) (n : ℕ) :
    ((ModuleCat.uliftFunctor.{t + 1, t} A ⋙ ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} A ≃+* A).toRingHom).obj
        (ModuleCat.of A (A ⧸ d.ideal ^ (n + 1)))) ≅
      ModuleCat.of (ULift.{t + 1} A) ((ULift.{t + 1} A) ⧸
        (Ideal.span (Set.range (fun i ↦ (ULift.up (a i) : ULift.{t + 1} A)))) ^
          (n + 1)) := by
  let e := liftedQuotientEquiv X d r a ha n
  let l : ((ULift.{t + 1} A) ⧸
        (Ideal.span (Set.range (fun i ↦ (ULift.up (a i) : ULift.{t + 1} A)))) ^
          (n + 1)) ≃ₗ[ULift.{t + 1} A] ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)) :=
    { e.toAddEquiv with
      map_smul' := by
        intro b x
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
        rfl }
  exact l.symm.toModuleIso

private theorem reconstructionUnit_eq_projection
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    reconstructionQuotientUnit X d n = finitePerfectAdicCoefficientProjection X d n := by
  apply (completedAdicFiniteModule X d n).unitHomEquiv.injective
  apply PresheafOfModules.sections_ext
  intro V
  exact ((reconstructionQuotientUnit_exists X d n).exists.choose_spec V).trans
    (map_one ((completedAdicProjection X d n).hom.app V).hom).symm

private theorem ordinaryCoefficient_iso
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A) :
    Nonempty (adicOrdinaryCoefficientDiagram d.ideal ⋙ finitePerfectAdicOrdinary X d ≅
      finitePerfectAdicCoefficientDiagram X d) := by
  classical
  obtain ⟨r, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp d.finitelyGenerated
  let I := Ideal.span (Set.range (fun i ↦ (ULift.up (a i) : ULift.{t + 1} A)))
  let L := ModuleCat.uliftFunctor.{t + 1, t} A ⋙ ModuleCat.restrictScalars.{t + 1}
    (ULift.ringEquiv : ULift.{t + 1} A ≃+* A).toRingHom
  let E := koszulConstantFunctor X A ⋙ completedAdicScalarExtension X d
  let H := finitePerfectAdicOrdinary X d
  have := (ordinaryScalar_exact X d).1
  have := (ordinaryScalar_exact X d).2
  have := (finitePerfectAdicConstant_exact X A).2.2
  have : PreservesFiniteColimits H := comp_preservesFiniteColimits _ _
  let l₀ : L.obj (ModuleCat.of A A) ≅
      ModuleCat.of (ULift.{t + 1} A) (ULift.{t + 1} A) :=
    (LinearEquiv.refl _ _).toModuleIso
  let e₀ : SheafOfModules.unit (completedAdicRing X d) ≅ H.obj (ModuleCat.of A A) :=
    completedRegularUnitIso X d ≪≫ E.mapIso l₀.symm
  choose q hq using fun n ↦ quotientModuleIso_exists X d r a ha n
  let e (n : ℕ) : H.obj (ModuleCat.of A (A ⧸ d.ideal ^ (n + 1))) ≅
      completedAdicFiniteModule X d n :=
    E.mapIso (coefficientLiftIso X d r a ha n) ≪≫ q n
  let π (n : ℕ) : ModuleCat.of A A ⟶ ModuleCat.of A (A ⧸ d.ideal ^ (n + 1)) :=
    ModuleCat.ofHom (d.ideal ^ (n + 1)).mkQ
  have hπ (n : ℕ) : Epi (π n) :=
    (ModuleCat.epi_iff_surjective _).2 (Submodule.mkQ_surjective _)
  have he (n : ℕ) : e₀.hom ≫ H.map (π n) ≫ (e n).hom =
      finitePerfectAdicCoefficientProjection X d n := by
    have halg : l₀.inv ≫ L.map (π n) ≫ (coefficientLiftIso X d r a ha n).hom =
        ModuleCat.ofHom (I ^ (n + 1)).mkQ := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply (liftedQuotientEquiv X d r a ha n).injective
      change (liftedQuotientEquiv X d r a ha n)
          ((liftedQuotientEquiv X d r a ha n).symm
            (ULift.up (Ideal.Quotient.mk (d.ideal ^ (n + 1)) x.down))) =
        (liftedQuotientEquiv X d r a ha n) (Ideal.Quotient.mk _ x)
      rw [RingEquiv.apply_symm_apply]
      rfl
    change (completedRegularUnitIso X d).hom ≫ E.map l₀.inv ≫
      E.map (L.map (π n)) ≫ E.map (coefficientLiftIso X d r a ha n).hom ≫
        (q n).hom = _
    rw [← E.map_comp_assoc, ← E.map_comp_assoc, Category.assoc, halg, hq,
      reconstructionUnit_eq_projection]
  refine ⟨NatIso.ofComponents (fun n ↦ e n.unop) ?_⟩
  intro m n f
  apply (cancel_epi (e₀.hom ≫ H.map (π m.unop))).1
  simp only [Functor.comp_map, Category.assoc]
  have hquot : π m.unop ≫ (adicOrdinaryCoefficientDiagram d.ideal).map f = π n.unop := by
    let v : (Functor.const ℕᵒᵖ).obj (ModuleCat.of A A) ⟶
        adicOrdinaryCoefficientDiagram d.ideal := NatTrans.ofOpSequence π (by
      intro k
      simp only [Functor.const_obj_map, adicOrdinaryCoefficientDiagram,
        Functor.ofOpSequence_map_homOfLE_succ]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      rfl)
    exact (v.naturality f).symm.trans (Category.id_comp _)
  rw [← H.map_comp_assoc, hquot, he]
  simpa only [Category.assoc, finitePerfectAdicCoefficientCone,
    NatTrans.ofOpSequence_app] using
    ((congrArg (fun k ↦ k ≫ (finitePerfectAdicCoefficientDiagram X d).map f)
      (he m.unop)).trans ((finitePerfectAdicCoefficientCone X d).w f)).symm

private def constantFixedUnit
    (X : Scheme.{t}) (A : Type t) [CommRing A]
    (M : ModuleCat.{t + 1} (ULift.{t + 1} A)) :
    (Functor.const X.ProEtᵒᵖ).obj M ⟶
      ((CategoryTheory.ConstantScalarRestriction.restriction
        (ProEt.topology X) (ULift.{t + 1} A)).obj
          ((koszulConstantFunctor X A).obj M)).obj where
  app U := ModuleCat.ofHom
    (X := M)
    (Y := ((CategoryTheory.ConstantScalarRestriction.restriction
      (ProEt.topology X) (ULift.{t + 1} A)).obj
        ((koszulConstantFunctor X A).obj M)).obj.obj U)
    { toFun := (toSheafify (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of M))).app U
      map_add' := map_add _
      map_smul' := by
        intro a x
        apply Eq.trans _
          (CategoryTheory.ConstantModuleDerivedProjection.restriction_scalar
            ((commutativeSiteConstantModuleFunctor (ProEt.topology X)
              (ULift.{t + 1} A)).obj M) U a _).symm
        have := (koszulConstantUnit_local X A).1
        have := (koszulConstantUnit_local X A).2
        exact ((PresheafOfModules.sheafificationAdjunction
          (koszulConstantUnit X A)).unit.app
            ((siteConstantModulePresheafGeneral (C := X.ProEt)
              (ULift.{t + 1} A)).obj M)).app U |>.hom.map_smul a x }
  naturality U V f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact ConcreteCategory.congr_hom
      ((toSheafify (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of M))).naturality f) x

private def constantFixedMap
    (X : Scheme.{t}) (A : Type t) [CommRing A]
    (M : ModuleCat.{t + 1} (ULift.{t + 1} A)) :
    (constantSheaf (ProEt.topology X) (ModuleCat.{t + 1} (ULift.{t + 1} A))).obj M ⟶
      (CategoryTheory.ConstantScalarRestriction.restriction
        (ProEt.topology X) (ULift.{t + 1} A)).obj
          ((koszulConstantFunctor X A).obj M) :=
  { hom := sheafifyLift (ProEt.topology X) (constantFixedUnit X A M)
      ((CategoryTheory.ConstantScalarRestriction.restriction
        (ProEt.topology X) (ULift.{t + 1} A)).obj
          ((koszulConstantFunctor X A).obj M)).property }

private theorem constantFixedMap_isIso
    (X : Scheme.{t}) (A : Type t) [CommRing A]
    (M : ModuleCat.{t + 1} (ULift.{t + 1} A)) : IsIso (constantFixedMap X A M) := by
  let J := ProEt.topology X
  let f := constantFixedMap X A M
  let η := toSheafify J ((Functor.const X.ProEtᵒᵖ).obj M)
  let α := constantFixedUnit X A M
  have hfac : η ≫ f.hom = α := toSheafify_sheafifyLift _ _ _
  have : Presheaf.IsLocallyInjective J α := by
    constructor
    intro U x y h
    exact Presheaf.equalizerSieve_mem J
      (toSheafify J ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of M))) x y h
  have : Presheaf.IsLocallySurjective J α := by
    constructor
    intro U x
    exact Presheaf.imageSieve_mem J
      (toSheafify J ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of M))) x
  have : Presheaf.IsLocallySurjective J η := inferInstance
  have : Presheaf.IsLocallyInjective J f.hom :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac J α hfac
  have : Presheaf.IsLocallySurjective J f.hom :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac J hfac
  exact (Sheaf.isLocallyBijective_iff_isIso f).1 ⟨inferInstance, inferInstance⟩

private def constantFixedIso
    (X : Scheme.{t}) (A : Type t) [CommRing A] :
    constantSheaf (ProEt.topology X) (ModuleCat.{t + 1} (ULift.{t + 1} A)) ≅
      koszulConstantFunctor X A ⋙ CategoryTheory.ConstantScalarRestriction.restriction
        (ProEt.topology X) (ULift.{t + 1} A) := by
  have (M : ModuleCat.{t + 1} (ULift.{t + 1} A)) := constantFixedMap_isIso X A M
  refine NatIso.ofComponents (fun M ↦ asIso (constantFixedMap X A M)) ?_
  intro M N f
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (ProEt.topology X) _ _
    (((koszulConstantFunctor X A ⋙
      CategoryTheory.ConstantScalarRestriction.restriction
        (ProEt.topology X) (ULift.{t + 1} A)).obj N).property)
  change toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj M) ≫
      sheafifyMap (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).map f) ≫
        (constantFixedMap X A N).hom =
    toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj M) ≫
      (constantFixedMap X A M).hom ≫
        ((CategoryTheory.ConstantScalarRestriction.restriction
          (ProEt.topology X) (ULift.{t + 1} A)).map
            ((koszulConstantFunctor X A).map f)).hom
  rw [← Category.assoc, ← toSheafify_naturality]
  simp only [Category.assoc, constantFixedMap, toSheafify_sheafifyLift]
  rw [← Category.assoc, toSheafify_sheafifyLift]
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact ConcreteCategory.congr_hom
    (congr_app (toSheafify_naturality (ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).map (AddCommGrpCat.ofHom f.hom.toAddMonoidHom))) U) x

@[instance_reducible] private def constantMonoidal
    (X : Scheme.{t}) (A : Type t) [CommRing A] :
    @Functor.Monoidal (ModuleCat.{t + 1} (ULift.{t + 1} A)) _ _
      (SheafOfModules.{t + 1} (adicModuleRing X A)) _ (constantModulesMonoidal X A)
      (koszulConstantFunctor X A) := by
  letI := constantModulesMonoidal X A
  let J := ProEt.topology X
  let R := ULift.{t + 1} A
  letI : MonoidalCategory (Sheaf J (ModuleCat.{t + 1} R)) :=
    CategoryTheory.ConstantScalarRestriction.fixedMonoidal.{t + 1, t} J R
  letI : (presheafToSheaf J (ModuleCat.{t + 1} R)).Monoidal :=
    (sfbSheafTensorStructure.{t, t + 1, t + 1, t + 1, t + 2}
      (A := ModuleCat.{t + 1} R) J).sheafificationMonoidal
  letI : (constantSheaf J (ModuleCat.{t + 1} R)).Monoidal :=
    inferInstanceAs (Functor.const X.ProEtᵒᵖ ⋙ presheafToSheaf J (ModuleCat.{t + 1} R)).Monoidal
  let e := (CategoryTheory.ConstantScalarRestriction.restriction.{t + 1, t} J R).asEquivalence
  letI : e.functor.Monoidal :=
    (CategoryTheory.ConstantScalarRestriction.restrictionBraided.{t + 1, t} J R).toMonoidal
  letI := e.inverseMonoidal
  exact e.monoidalOfPostcompFunctor (koszulConstantFunctor X A) (constantFixedIso X A).symm

private def liftTensorComparison (A : Type t) [CommRing A] :
    TensorComparison (ModuleCat.uliftFunctor.{t + 1, t} A ⋙
      ModuleCat.restrictScalars.{t + 1}
        (ULift.ringEquiv : ULift.{t + 1} A ≃+* A).toRingHom) where
  iso M N :=
    (show ULift.{t + 1} (M ⊗[A] N) ≃ₗ[ULift.{t + 1} A]
        (ULift.{t + 1} M ⊗[ULift.{t + 1} A] ULift.{t + 1} N) from
      { (TensorProduct.AlgebraTensorModule.uliftEquiv A A M N).toAddEquiv with
        map_smul' := fun a x ↦
          (TensorProduct.AlgebraTensorModule.uliftEquiv A A M N).map_smul a.down x
      }).toModuleIso
  natural f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rcases x with ⟨x⟩
    induction x using TensorProduct.inductionOn with
    | tmul x y => rfl
    | add x y hx hy =>
      have ha : (ULift.up (x + y) : ULift.{t + 1} _) = ULift.up x + ULift.up y := rfl
      simpa only [ha, map_add] using congrArg₂ (· + ·) hx hy

private def scalarTensorComparison
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A) :
    @TensorComparison (SheafOfModules.{t + 1} (adicModuleRing X A))
      (CompletedAdicModules X d) _ _ (constantModulesMonoidal X A)
      (completedAdicModules_monoidal X d) (completedAdicScalarExtension X d) := by
  letI := constantModulesMonoidal X A
  letI := completedAdicModules_monoidal X d
  let s := (SheafOfModules.scalarExtension_constraint_coherence.{t + 1, t, t + 1}
    (J := ProEt.topology X) (adicConstantRing X A) (completedAdicCommRing X d)
      (completedAdicScalar X d)).some
  let h := (completedAdicScalarExtensionData X d).choose_spec.choose
  refine TensorComparison.ofObjectEq (completedAdicScalarExtension X d)
    (fun M ↦ SheafOfModules.changeOfRings.{t, t + 1, t + 1}
      (completedAdicScalar X d) M) h
    (fun f ↦ SheafOfModules.changeOfRingsHom.{t, t + 1, t + 1}
      (completedAdicScalar X d) _ f) ?_
    s.tensorIso ?_
  · intro M N f
    exact (completedAdicScalarExtensionData X d).choose_spec.choose_spec.choose f
  · intro M M' N N' f g
    exact s.natural M N M' N' f g

/-- Completed scalar extension is exact and its ordinary quotient tensor comparison
is natural in the input module and in every coefficient transition.

Source: Stacks Project, Tag 09C6, the ordinary quotient tensor calculation;
Modules on Sites, Tags 093J--093M, completed constant algebra flatness and finite reduction.
(blueprint: lem-weil-pbc-finite-perfect-adic-ordinary-coefficient-comparison).

Proof: apply completed constant algebra flatness to the Noetherian ring A after
lifting it to the site's coefficient universe. Identify its constant quotient system
with the prescribed finite coefficient sheaves by the constants-to-functions maps.
These maps commute with the quotient homomorphisms. The universal property of the
limit identifies the completed rings and their projections, and the normalization
of completedAdicScalar identifies the scalar action. Flatness of that algebra makes
ordinary completed scalar extension exact; cokernels are preserved by its scalar
adjunction. Finite reduction gives H(A/I^(n+1))≅(A/I^(n+1))_T, with the prescribed
completed action. Constant realization and ordinary scalar extension commute with
tensor products. Their tensor comparisons and the preceding coefficient comparison
therefore identify H(M) tensor_(A_T) (A/I^(n+1))_T with
H(M tensor_A A/I^(n+1)). Use inverse finite reduction to represent a coefficient
section locally by t tensor a. On these pure generators the forward map sends
(s tensor m) tensor red(t tensor a) to st tensor (m tensor a); its inverse sends
s tensor (m tensor a) to (s tensor m) tensor red(1 tensor a). Balancing proves
well-definedness, and local tensor generation proves that the maps are inverse.
The same formulas commute with every module map and quotient homomorphism, so the
comparisons form the stated natural isomorphism of functors to diagrams. Carry the
ULift equivalences through the formula. No complex, derived functor, K-flatness,
boundedness, projectivity or inverse-limit exactness assertion occurs here.
For I=A or A=0 the coefficient modules are zero and the same maps apply. -/
theorem finitePerfectAdicOrdinaryCoefficient_comparison
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A) :
    (PreservesFiniteLimits (completedAdicScalarExtension X d) ∧
      PreservesFiniteColimits (completedAdicScalarExtension X d)) ∧
    Nonempty (finitePerfectAdicOrdinary X d ⋙ finitePerfectAdicTensorFunctor X d ≅
      adicOrdinaryTensorFunctor d.ideal ⋙
        (Functor.whiskeringRight ℕᵒᵖ (ModuleCat.{t} A) (CompletedAdicModules X d)).obj
          (finitePerfectAdicOrdinary X d)) := by
  let := constantModulesMonoidal X A
  let := completedAdicModules_monoidal X d
  let := constantMonoidal X A
  let tH : TensorComparison (finitePerfectAdicOrdinary X d) :=
    (liftTensorComparison A).comp
      ((TensorComparison.ofMonoidal (koszulConstantFunctor X A)).comp
        (scalarTensorComparison X d))
  obtain ⟨e⟩ := ordinaryCoefficient_iso X d
  exact ⟨ordinaryScalar_exact X d, ⟨tH.diagramIso
    (adicOrdinaryCoefficientDiagram d.ideal) (finitePerfectAdicCoefficientDiagram X d) e⟩⟩

/-- Ordinary coefficient balancing extends degreewise to a diagram of complexes.
Source: Stacks Project, Tag 09C6
(blueprint: lem-weil-pbc-finite-perfect-adic-ordinary-coefficient-comparison).
Proof: apply the ordinary natural isomorphism to complexes, using the composition
comparisons for the termwise functors; transpose the resulting complex of diagrams. -/
theorem finitePerfectAdicTensorComplexDiagram_ordinaryComparison
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (P : CochainComplex (ModuleCat.{t} A) ℤ) :
    Nonempty (finitePerfectAdicTensorComplexDiagram X d P ≅
      adicOrdinaryTensorComplexDiagram d.ideal P ⋙
        (finitePerfectAdicOrdinary X d).mapHomologicalComplex (.up ℤ)) := by
  obtain ⟨e⟩ := (finitePerfectAdicOrdinaryCoefficient_comparison X d).2
  let H := finitePerfectAdicOrdinary X d
  let O := adicOrdinaryTensorFunctor d.ideal
  let R := (Functor.whiskeringRight ℕᵒᵖ (ModuleCat.{t} A)
    (CompletedAdicModules X d)).obj H
  have : R.Additive := by dsimp [R]; infer_instance
  let ec := (Functor.mapHomologicalComplexCompIso (Iso.refl
      (H ⋙ finitePerfectAdicTensorFunctor X d)) (.up ℤ)).app P ≪≫
    (NatIso.mapHomologicalComplex e (.up ℤ)).app P ≪≫
    ((Functor.mapHomologicalComplexCompIso (Iso.refl (O ⋙ R)) (.up ℤ)).app P).symm
  exact ⟨HomologicalComplex.complexOfFunctorsToFunctorToComplex.mapIso ec⟩

end AlgebraicGeometry.Scheme
