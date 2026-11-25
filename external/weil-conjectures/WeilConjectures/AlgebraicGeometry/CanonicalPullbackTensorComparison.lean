/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedPullbackMonoidalModel
public import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.Algebra.Homology.KFlatPullback
import WeilConjectures.Algebra.Homology.HomotopyCategory.Braided

/-! # Canonical tensor comparison for derived pullback

Source: Stacks Project, Cohomology, Tag 079U; perfect.tex, Tag 0DJA(1)
(blueprint: def-pc-derived-pullback-tensor-comparison).
The comparison is the unique family satisfying `IsCanonicalPullbackTensorComparison`:
it is pinned by the actual module pullback tensor map and the shared left-derived
counit on K-flat representatives. Statements bind the comparison together with this
uniquely characterising predicate; no monoidal structure on pullback is chosen
arbitrarily and no data is chosen from a theorem.
-/

@[expose] public section

universe uTC wTC uGeneric vGeneric uCalc vCalc
open CategoryTheory CategoryTheory.Limits MonoidalCategory
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace AlgebraicGeometry

/-- The total tensor complex used in the coordinate equation below.
Source: Stacks, 079U (blueprint: def-pc-derived-pullback-tensor-comparison). -/
def pullbackTensorTotal (X : Scheme.{uTC})
    (P N : CochainComplex (SheafOfModules.{uTC} (moduleRings X.toRingedSpace)) ℤ) :
    CochainComplex (SheafOfModules.{uTC} (moduleRings X.toRingedSpace)) ℤ :=
  letI := pullbackDescentModuleTensor X
  CochainComplex.mapBifunctor P N (curriedTensor _)

/-- The canonical localization tensor map, invertible on K-flat coordinates.
It is the upstream lax monoidal map of Q for the recorded derived tensor.
Source: Stacks, 06YH and 079U
(blueprint: def-pc-derived-pullback-tensor-comparison). -/
def pullbackTensorModelMap (X : Scheme.{uTC})
    [HasDerivedCategory.{wTC} (SheafOfModules.{uTC} (moduleRings X.toRingedSpace))]
    (P N : CochainComplex (SheafOfModules.{uTC} (moduleRings X.toRingedSpace)) ℤ) :
    DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj N ⟶
      DerivedCategory.Q.obj (pullbackTensorTotal X P N) := by
  letI := pullbackDescentModuleTensor X
  letI := moduleSymmetric X
  haveI := modulePreadditive X
  letI := moduleClosed X
  haveI := moduleGrothendieck X
  haveI := moduleResolutions X
  haveI := moduleDerivedMonoidal X
  exact @Functor.LaxMonoidal.μ _ _ _ _ _ _ _ (pullbackDescentQLax X) P N

private theorem localizationTensor_isIso {C : Type uGeneric}
    [Category.{vGeneric} C] [Abelian C]
    [IsGrothendieckAbelian.{uTC} C] [HasDerivedCategory.{wTC} C]
    [HasColimitsOfSize.{0, 0} C] [MonoidalCategory C] [MonoidalClosed C]
    [MonoidalPreadditive C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]
    [Functor.HasDerivedMonoidalCategory (DerivedCategory.Qh (C := C))
      (HomotopyCategory.quasiIso C (.up ℤ))]
    (P N : CochainComplex C ℤ)
    (hP : (HomotopyCategory.quasiIso C (.up ℤ)).kFlat
      ((HomotopyCategory.quotient C (.up ℤ)).obj P)) :
    IsIso (Functor.LaxMonoidal.μ (DerivedCategory.Q (C := C)) P N) := by
  have : IsIso (Functor.LaxMonoidal.μ (DerivedCategory.Qh (C := C))
      ((HomotopyCategory.quotient C (.up ℤ)).obj P)
      ((HomotopyCategory.quotient C (.up ℤ)).obj N)) :=
    DerivedMonoidal.isIso_counit_app_app_of_kFlat_left
      (DerivedCategory.Qh (C := C)) (HomotopyCategory.quasiIso C (.up ℤ)) _ _ hP
  change IsIso (_ ≫ _ ≫ _)
  change IsIso (_ ≫ (_ ≫ _) ≫ _)
  infer_instance

private theorem tensorTransport_equation
    {C : Type uGeneric} [Category.{vGeneric} C] [MonoidalCategory C]
    {D : Type uCalc} [Category.{vCalc} D] [MonoidalCategory D]
    (L : C ⥤ D) (δ : L ≅ L) {A B U : C} {A' B' U' V : D}
    (m : L.obj A ⊗ L.obj B ≅ L.obj (A ⊗ B)) (μ : A ⊗ B ⟶ U)
    (εU ε'U : L.obj U ⟶ U') (εA ε'A : L.obj A ⟶ A')
    (εB ε'B : L.obj B ⟶ B') (ν : A' ⊗ B' ⟶ V) (φ : U' ⟶ V)
    (hU : δ.hom.app U ≫ ε'U = εU) (hA : δ.hom.app A ≫ ε'A = εA)
    (hB : δ.hom.app B ≫ ε'B = εB)
    (hmodel : m.hom ≫ L.map μ ≫ εU ≫ φ = (εA ⊗ₘ εB) ≫ ν) :
    L.map μ ≫ ε'U ≫ φ =
      (δ.inv.app (A ⊗ B) ≫ m.inv ≫ (δ.hom.app A ⊗ₘ δ.hom.app B)) ≫
        (ε'A ⊗ₘ ε'B) ≫ ν := by
  apply (cancel_epi (δ.hom.app (A ⊗ B))).1
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  simp only [Category.assoc]
  rw [← δ.hom.naturality_assoc, reassoc_of% hU,
    tensorHom_comp_tensorHom_assoc, hA, hB]
  apply (cancel_epi m.hom).1
  simpa only [← Category.assoc, Iso.hom_inv_id, Category.id_comp] using hmodel

private theorem quotient_kFlat_of_acyclic
    {C : Type uGeneric} [Category.{vGeneric} C] [Abelian C]
    [HasColimitsOfSize.{0, 0} C] [MonoidalCategory C] [MonoidalClosed C]
    [MonoidalPreadditive C] [BraidedCategory C]
    (P : CochainComplex C ℤ)
    (hP : ∀ N : CochainComplex C ℤ, N.Acyclic → (N ⊗ P).Acyclic) :
    (HomotopyCategory.quasiIso C (.up ℤ)).kFlat
      ((HomotopyCategory.quotient C (.up ℤ)).obj P) := by
  rw [HomotopyCategory.kFlat_iff_preserves_acyclic]
  intro N hN
  obtain ⟨N, rfl⟩ := N.quotient_obj_surjective
  rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hN
  have hr : HomotopyCategory.subcategoryAcyclic C
      ((HomotopyCategory.quotient C (.up ℤ)).obj N ⊗
        (HomotopyCategory.quotient C (.up ℤ)).obj P) :=
    (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2 (hP N hN)
  exact ⟨(HomotopyCategory.subcategoryAcyclic C).prop_of_iso (β_ _ _) hr, hr⟩

private theorem tensorTransport_natural
    {C : Type uGeneric} [Category.{vGeneric} C] [MonoidalCategory C]
    {D : Type uCalc} [Category.{vCalc} D] [MonoidalCategory D]
    (L : C ⥤ D) (δ : L ≅ L) (m : L.CoreMonoidal)
    {E E' K K' : C} (a : E ⟶ E') (b : K ⟶ K') :
    L.map (a ⊗ₘ b) ≫
        (δ.inv.app (E' ⊗ K') ≫ (m.μIso E' K').inv ≫
          (δ.hom.app E' ⊗ₘ δ.hom.app K')) =
      (δ.inv.app (E ⊗ K) ≫ (m.μIso E K).inv ≫ (δ.hom.app E ⊗ₘ δ.hom.app K)) ≫
        (L.map a ⊗ₘ L.map b) := by
  let := m.toMonoidal
  let := Functor.Monoidal.transport δ
  simpa only [Functor.Monoidal.transport_δ,
    Functor.CoreMonoidal.toMonoidal_toOplaxMonoidal,
    Functor.CoreMonoidal.toOplaxMonoidal_δ] using
    (Functor.OplaxMonoidal.δ_natural L a b).symm

private theorem counitTransfer_isIso
    {C : Type uGeneric} [Category.{vGeneric} C]
    {D : Type uCalc} [Category.{vCalc} D]
    {H : Type uTC} [Category.{wTC} H]
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
    (LF : D ⥤ H) (F : C ⥤ H) (ε ε' : L ⋙ LF ⟶ F)
    [LF.IsLeftDerivedFunctor ε W] [LF.IsLeftDerivedFunctor ε' W]
    (P : C) [IsIso (ε.app P)] : IsIso (ε'.app P) := by
  let δ := Functor.leftDerivedUnique LF LF ε ε' W
  have h : δ.hom.app (L.obj P) ≫ ε'.app P = ε.app P := by
    change (Functor.leftDerivedNatTrans LF LF ε ε' W (𝟙 F)).app _ ≫ _ = _
    simpa only [NatTrans.id_app, Category.comp_id] using
      Functor.leftDerivedNatTrans_app LF LF ε ε' W (𝟙 F) P
  have : IsIso (δ.hom.app (L.obj P) ≫ ε'.app P) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_left (δ.hom.app (L.obj P)) (ε'.app P)


variable [∀ Y : Scheme.{uTC},
  HasDerivedCategory.{wTC} (SheafOfModules.{uTC} (moduleRings Y.toRingedSpace))]

/-- The canonical tensor comparison is characterized on every pair of K-flat
representatives by the left-derived counits, the localization tensor maps and
termwise module pullback. The degreewise equation pins the chain isomorphism to
the canonical module tensor map on each summand, including its signs.
Source: Stacks, 079U; perfect.tex, 0DJA(1)
(blueprint: def-pc-derived-pullback-tensor-comparison). -/
def IsCanonicalPullbackTensorComparison {T X : Scheme.{uTC}} (g : T ⟶ X)
    (τ : ∀ E K : schemeDerivedCategory X,
      (derivedPullback g).obj (E ⊗ K) ⟶
        (derivedPullback g).obj E ⊗ (derivedPullback g).obj K) : Prop :=
  letI := pullbackDescentModuleTensor X
  letI := pullbackDescentModuleTensor T
  letI := modulePreadditive X
  letI := modulePreadditive T
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor T.sheaf
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj T.sheaf
  (∀ P N : CochainComplex (SheafOfModules.{uTC} (moduleRings X.toRingedSpace)) ℤ,
    P.IsKFlatTensor → N.IsKFlatTensor →
    ∃ φ : ((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj
        (pullbackTensorTotal X P N) ≅
      pullbackTensorTotal T
        (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj P)
        (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj N),
      (∀ (p q n : ℤ) (h : p + q = n),
        (Scheme.Modules.tensorPullback g).map
            (HomologicalComplex.ιMapBifunctor P N (curriedTensor _) (.up ℤ) p q n h) ≫
          φ.hom.f n =
        ((Classical.choose (Scheme.Modules.module_pullback_tensor g)) (P.X p) (N.X q)).hom ≫
          HomologicalComplex.ιMapBifunctor
            (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj P)
            (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj N)
            (curriedTensor
              (SheafOfModules.{uTC} (moduleRings T.toRingedSpace))) (.up ℤ) p q n h) ∧
      (derivedPullback g).map (pullbackTensorModelMap X P N) ≫
          cast (by rfl) ((SingleComplexBaseChange.counit g).app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj (pullbackTensorTotal X P N))) ≫
          DerivedCategory.Q.map φ.hom =
        τ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj N) ≫
          cast (by rfl) ((SingleComplexBaseChange.counit g).app
              ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ⊗ₘ
            (SingleComplexBaseChange.counit g).app
              ((HomotopyCategory.quotient _ (.up ℤ)).obj N)) ≫
          pullbackTensorModelMap T
            (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj P)
            (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj N)) ∧
    ∀ (E E' K K' : schemeDerivedCategory X) (a : E ⟶ E') (b : K ⟶ K'),
      (derivedPullback g).map (a ⊗ₘ b) ≫ τ E' K' =
        τ E K ≫ ((derivedPullback g).map a ⊗ₘ (derivedPullback g).map b)

private theorem sharedCounit_leftDerived {T X : Scheme.{uTC}} (g : T ⟶ X) :
    (derivedPullback g).IsLeftDerivedFunctor (SingleComplexBaseChange.counit g)
      (HomotopyCategory.quasiIso _ (.up ℤ)) := by
  exact Classical.choose (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition.{uTC, wTC})) g

private theorem counit_isIso {T X : Scheme.{uTC}} (g : T ⟶ X)
    (P : CochainComplex (SheafOfModules.{uTC} (moduleRings X.toRingedSpace)) ℤ)
    (hP : P.IsKFlatTensor) :
    IsIso ((SingleComplexBaseChange.counit g).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) := by
  obtain ⟨_, _, _, _, _, _, _, F, hF, hmap, hAdd, ε, hε, _, hK⟩ :=
    (derivedPullback_spec.{uTC, wTC} g)
  have hF' : F = Scheme.Modules.tensorPullback g :=
    CategoryTheory.Functor.ext hF (fun M N a ↦ hmap a)
  subst F
  change (derivedPullback g).IsLeftDerivedFunctor ε
    (HomotopyCategory.quasiIso _ (.up ℤ)) at hε
  have := sharedCounit_leftDerived g
  have := hK P hP
  exact counitTransfer_isIso DerivedCategory.Qh (HomotopyCategory.quasiIso _ (.up ℤ))
    (derivedPullback g) _ ε (SingleComplexBaseChange.counit g)
    ((HomotopyCategory.quotient _ (.up ℤ)).obj P)

private theorem modelMap_isIso (X : Scheme.{uTC})
    (P N : CochainComplex (SheafOfModules.{uTC} (moduleRings X.toRingedSpace)) ℤ)
    (hP : P.IsKFlatTensor) : IsIso (pullbackTensorModelMap X P N) := by
  let C := SheafOfModules.{uTC} (moduleRings X.toRingedSpace)
  let : MonoidalCategory C := pullbackDescentModuleTensor X
  let : SymmetricCategory C := moduleSymmetric X
  have : MonoidalPreadditive C := modulePreadditive X
  let : MonoidalClosed C := moduleClosed X
  have : IsGrothendieckAbelian.{uTC} C := moduleGrothendieck X
  have : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink.{0, 0, uTC, uTC} C
  have : Abelian.HasFunctorialFlatResolution C := moduleResolutions X
  have : Functor.HasDerivedMonoidalCategory (DerivedCategory.Qh (C := C))
      (HomotopyCategory.quasiIso C (.up ℤ)) := moduleDerivedMonoidal X
  have (M : C) : PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj M) :=
    preservesColimitsOfShape_of_natIso (F := tensorLeft M)
      (NatIso.ofComponents (fun N ↦ β_ M N) (by intros; simp [curriedTensor]))
  have (M : C) : PreservesColimitsOfShape ℤ ((curriedTensor C).obj M) := inferInstance
  have : HasExactColimitsOfShape ℤ C := inferInstance
  have (j : ℤ) : HasColimitsOfShape
      (Discrete ((ComplexShape.up ℤ).π (.up ℤ) (.up ℤ) ⁻¹' {j})) C := inferInstance
  have : (HomotopyCategory.quasiIso C (.up ℤ)).localizerMorphismKFlat.IsLeftDerivabilityStructure :=
    inferInstance
  have hk := quotient_kFlat_of_acyclic P (fun N hN ↦ hP N hN)
  have (A B : GradedObject ℤ C) : GradedObject.HasTensor A B := inferInstance
  let := HomologicalComplex.monoidalCategory C (.up ℤ)
  let : (DerivedCategory.Q (C := C)).LaxMonoidal := pullbackDescentQLax X
  change IsIso (Functor.LaxMonoidal.μ (DerivedCategory.Q (C := C)) P N)
  exact localizationTensor_isIso P N hk

/-- Transport a verified core-monoidal model to the canonical comparison predicate.
The model supplies the counit and K-flat coordinate equations; the transport is the
standard descent argument through K-flat resolutions.
Proof: identify the model's module functor with the actual tensor pullback by
functor extensionality. The left-derived universal property gives a natural
isomorphism delta from the model counit to the shared counit, satisfying
`delta ≫ shared counit = model counit`. Conjugate the inverse model tensorator
by delta inverse on the tensor input and by the tensor of delta on the outputs.
Naturality follows from naturality of delta and the tensorator. Substituting
the counit comparison into the model coordinate equation gives the required
canonical equation; the model's degreewise equation pins the same chain map.
Source: Stacks, 079U; perfect.tex, 0DJA(1)
(blueprint: def-pc-derived-pullback-tensor-comparison-model-transport). -/
theorem exists_canonical_from_model {T X : Scheme.{uTC}} (g : T ⟶ X)
    (m : (derivedPullback g).CoreMonoidal)
    (hm : IsDerivedPullbackMonoidalModel g m) :
    ∃ τ : ∀ E K : schemeDerivedCategory X,
      (derivedPullback g).obj (E ⊗ K) ⟶
        (derivedPullback g).obj E ⊗ (derivedPullback g).obj K,
      IsCanonicalPullbackTensorComparison g τ := by
  classical
  let := pullbackDescentModuleTensor X
  let := pullbackDescentModuleTensor T
  have : MonoidalPreadditive (SheafOfModules.{uTC} (moduleRings X.toRingedSpace)) :=
    modulePreadditive X
  have : MonoidalPreadditive (SheafOfModules.{uTC} (moduleRings T.toRingedSpace)) :=
    modulePreadditive T
  obtain ⟨F, hF, hmap, hAdd, mF, hμ, ε, hε, φ, hφ, heq⟩ := hm
  have hF' : F = Scheme.Modules.tensorPullback g :=
    CategoryTheory.Functor.ext hF (fun M N a ↦ hmap a)
  subst F
  have := hAdd
  have := hε
  have := sharedCounit_leftDerived g
  let δ := Functor.leftDerivedUnique (derivedPullback g) (derivedPullback g) ε
    (SingleComplexBaseChange.counit g) (HomotopyCategory.quasiIso _ (.up ℤ))
  have hδ (P : CochainComplex
      (SheafOfModules.{uTC} (moduleRings X.toRingedSpace)) ℤ) :
      δ.hom.app (DerivedCategory.Q.obj P) ≫
        (SingleComplexBaseChange.counit g).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P) =
      ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) := by
    change (Functor.leftDerivedNatTrans (derivedPullback g) (derivedPullback g) ε
      (SingleComplexBaseChange.counit g) (HomotopyCategory.quasiIso _ (.up ℤ))
      (𝟙 _)).app _ ≫ _ = _
    convert (Functor.leftDerivedNatTrans_app (derivedPullback g) (derivedPullback g) ε
      (SingleComplexBaseChange.counit g) (HomotopyCategory.quasiIso _ (.up ℤ))
      (𝟙 _) ((HomotopyCategory.quotient _ (.up ℤ)).obj P)).trans
      (Category.comp_id _) using 1 <;> rfl
  let τ := fun E K ↦ δ.inv.app (E ⊗ K) ≫ (m.μIso E K).inv ≫
    (δ.hom.app E ⊗ₘ δ.hom.app K)
  refine ⟨τ, ?_⟩
  dsimp only [IsCanonicalPullbackTensorComparison]
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor T.sheaf
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj T.sheaf
  have : (curriedTensor T.Modules).PreservesZeroMorphisms :=
    SheafOfModules.preservesZeroMorphisms_curriedTensor T.sheaf
  have (M : T.Modules) : ((curriedTensor T.Modules).obj M).PreservesZeroMorphisms :=
    SheafOfModules.preservesZeroMorphisms_curriedTensor_obj T.sheaf M
  constructor
  · intro P N hP hN
    refine ⟨φ P N, ?_, ?_⟩
    · intro p q n hpq
      convert (hφ P N p q n hpq).trans
        (congrArg (fun a ↦ a ≫ HomologicalComplex.ιMapBifunctor
          (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj P)
          (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj N)
          (curriedTensor
            (SheafOfModules.{uTC} (moduleRings T.toRingedSpace)))
          (.up ℤ) p q n hpq) (hμ (P.X p) (N.X q))) using 1 <;> first
      | rfl
      | simp only [eqToHom_refl, tensorHom_id, Category.id_comp, id_whiskerRight,
          Category.comp_id]
    · dsimp only [τ]
      apply tensorTransport_equation (derivedPullback g) δ
        (m.μIso (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj N))
        (pullbackTensorModelMap X P N)
        (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj (pullbackTensorTotal X P N)))
        _ (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))
        _ (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj N))
      · exact hδ (pullbackTensorTotal X P N)
      · exact hδ P
      · exact hδ N
      · convert heq P N hP hN using 1 <;> rfl
  · intro E E' K K' a b
    exact tensorTransport_natural (derivedPullback g) δ m a b

/-- Existence of the canonical derived tensor comparison.
Proof: choose K-flat representatives of both inputs (lem-pc-kflat-resolution).
Their tensor and pullbacks are K-flat (lem-pc-kflat-tensor-product and
lem-pc-kflat-pullback-preservation), so the localization tensor maps and the
left-derived counits are invertible. Form the chain tensor isomorphism from
lem-weil-pbc-module-pullback-tensor on every summand; naturality makes it commute
with differentials. Transport it through the counits and localization tensor
maps to obtain τ. Comparisons between K-flat resolutions and the universal
left-derived property show independence of representatives, giving the displayed
equation for every P,N (lem-pc-derived-pullback-tensor-product).
Source: Stacks, 079U; perfect.tex, 0DJA(1)
(blueprint: def-pc-derived-pullback-tensor-comparison). -/
theorem exists_canonicalPullbackTensorComparison {T X : Scheme.{uTC}} (g : T ⟶ X) :
    ∃ τ : ∀ E K : schemeDerivedCategory X,
      (derivedPullback g).obj (E ⊗ K) ⟶
        (derivedPullback g).obj E ⊗ (derivedPullback g).obj K,
      IsCanonicalPullbackTensorComparison g τ := by
  obtain ⟨m, hm⟩ := exists_derivedPullbackMonoidalModel g
  exact exists_canonical_from_model g m hm

/-- The canonical derived tensor comparison is unique: two families satisfying the
characterising predicate agree.
Proof: on K-flat representatives P, N the counits at P and N and the localization
tensor map at the K-flat pullbacks are invertible, and the chain isomorphism is pinned
on every summand, so the coordinate equation determines the value at (Q P, Q N).
Every derived object is isomorphic to Q of a K-flat complex (lem-pc-kflat-resolution),
and naturality in both inputs transports the value along these isomorphisms.
Source: Stacks, 079U (blueprint: def-pc-derived-pullback-tensor-comparison). -/
theorem IsCanonicalPullbackTensorComparison.unique {T X : Scheme.{uTC}} {g : T ⟶ X}
    {τ τ' : ∀ E K : schemeDerivedCategory X,
      (derivedPullback g).obj (E ⊗ K) ⟶
        (derivedPullback g).obj E ⊗ (derivedPullback g).obj K}
    (h : IsCanonicalPullbackTensorComparison g τ)
    (h' : IsCanonicalPullbackTensorComparison g τ') : τ = τ' := by
  classical
  let := pullbackDescentModuleTensor X
  let := pullbackDescentModuleTensor T
  have : MonoidalPreadditive (SheafOfModules.{uTC} (moduleRings X.toRingedSpace)) :=
    modulePreadditive X
  have : MonoidalPreadditive (SheafOfModules.{uTC} (moduleRings T.toRingedSpace)) :=
    modulePreadditive T
  dsimp only [IsCanonicalPullbackTensorComparison] at h h'
  have hflat (P N : CochainComplex
      (SheafOfModules.{uTC} (moduleRings X.toRingedSpace)) ℤ)
      (hP : P.IsKFlatTensor) (hN : N.IsKFlatTensor) :
      τ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj N) =
        τ' (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj N) := by
    obtain ⟨φ, hφ, heq⟩ := h.1 P N hP hN
    obtain ⟨ψ, hψ, heq'⟩ := h'.1 P N hP hN
    have hφψ : φ.inv ≫ ψ.hom = 𝟙 _ := by
      apply HomologicalComplex.hom_ext
      intro n
      apply HomologicalComplex.mapBifunctor.hom_ext
      intro p q hpq
      apply (cancel_epi
        (((Classical.choose (Scheme.Modules.module_pullback_tensor g))
          (P.X p) (N.X q)).hom)).1
      simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f, ← Category.assoc]
      rw [← hφ p q n hpq]
      have hid : φ.hom.f n ≫ φ.inv.f n = 𝟙 _ :=
        congrArg (fun a ↦ a.f n) φ.hom_inv_id
      simp only [Category.assoc, hid]
      exact (hψ p q n hpq).trans (hφ p q n hpq).symm
    have hhom : φ.hom = ψ.hom := by
      calc
        φ.hom = φ.hom ≫ (φ.inv ≫ ψ.hom) := by rw [hφψ, Category.comp_id]
        _ = ψ.hom := by simp only [← Category.assoc, φ.hom_inv_id, Category.id_comp]
    have hPull : CochainComplex.IsKFlatTensor (R := T.sheaf)
        (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj P) := by
      convert CochainComplex.isKFlat_pullback g.base T.sheaf X.sheaf ⟨g.c⟩ P hP using 1
      rfl
    have := counit_isIso g P hP
    have := counit_isIso g N hN
    have := modelMap_isIso T
      (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj P)
      (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj N) hPull
    apply (cancel_mono
      (((SingleComplexBaseChange.counit g).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ⊗ₘ
        (SingleComplexBaseChange.counit g).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj N)) ≫
        pullbackTensorModelMap T
          (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj P)
          (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj N))).1
    erw [← heq, ← heq', hhom]
  funext E K
  obtain ⟨c⟩ := SingleComplexBaseChange.nonempty_coordinates g E
    ((derivedPullback g).obj E) (𝟙 _)
  obtain ⟨d⟩ := SingleComplexBaseChange.nonempty_coordinates g K
    ((derivedPullback g).obj K) (𝟙 _)
  have hnat := h.2 _ _ _ _ c.e.hom d.e.hom
  have hnat' := h'.2 _ _ _ _ c.e.hom d.e.hom
  apply (cancel_epi ((derivedPullback g).map (c.e.hom ⊗ₘ d.e.hom))).1
  rw [hnat, hnat', hflat c.P d.P c.isKFlat d.isKFlat]


end AlgebraicGeometry
end
