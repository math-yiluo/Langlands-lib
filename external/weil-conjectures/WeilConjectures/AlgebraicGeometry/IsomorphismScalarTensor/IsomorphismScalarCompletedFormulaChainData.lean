/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IsomorphismScalarTensor.IsomorphismScalarCompletedModelBase
import all WeilConjectures.AlgebraicGeometry.SixFunctors.LimitScalarChainComparison
import all WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings

/-! # Chain-level data for the completed scalar formula

## References

* Stacks Project, Tag 03EL
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
  WeilConjectures.integralOperationsAbSheafify
  WeilConjectures.integralOperationsAbLocallyBijective
  WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [local irreducible] HasDerivedCategory.standard
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme WeilConjectures
open scoped ChangeOfRings
namespace AlgebraicGeometry.ProEtale.IsomorphismScalarTensor

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]

private theorem constantTransport_natural
    {X Y : AlgebraicGeometry.Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    {A B : CommRingCat.{max u (t + 1)}} (a : A ⟶ B) :
    (isoSectionwiseInverseImage g RingCat.{max u (t + 1)}).map
        ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
            ((constantSheaf (ProEt.topology Y) CommRingCat.{max u (t + 1)}).map a)) ≫
        isoSectionwiseConstantMap.{t, u} g B =
      isoSectionwiseConstantMap.{t, u} g A ≫
        (sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
            ((constantSheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).map a) := by
  let W := sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})
  let I := isoSectionwiseInverseImage g RingCat.{max u (t + 1)}
  let cA := isoSectionwiseConstantMap.{t, u} g A
  let cB := isoSectionwiseConstantMap.{t, u} g B
  let aY := (sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
      ((constantSheaf (ProEt.topology Y) CommRingCat.{max u (t + 1)}).map a)
  let aX := (constantSheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).map a
  change I.map aY ≫ cB = cA ≫ W.map aX
  apply (cancel_epi (inv cA)).1
  rw [IsIso.inv_hom_id_assoc]
  let f := inv cA ≫ I.map aY ≫ cB
  change f = W.map aX
  rw [← W.map_preimage f]
  apply congrArg W.map
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (ProEt.topology X) _ _
    ((constantSheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).obj B).property
  ext U x
  change (W.map (W.preimage f)).hom.app U _ = _
  rw [W.map_preimage]
  have hcA := (isoSectionwiseConstantMap_existsUnique.{t, u} g A).exists.choose_spec
  have hcB := (isoSectionwiseConstantMap_existsUnique.{t, u} g B).exists.choose_spec
  have hi := congrArg (fun k ↦ k.hom.app U) (IsIso.hom_inv_id cA)
  have hi' := ConcreteCategory.congr_hom hi
    ((toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A)).app
      (op ((proEtaleIsoPostcompose g).obj U.unop)) x)
  change (inv cA).hom.app U (cA.hom.app U _) = _ at hi'
  erw [hcA U.unop x] at hi'
  have hy := ConcreteCategory.congr_hom
    (congrArg (fun k ↦ k.app (op ((proEtaleIsoPostcompose g).obj U.unop)))
      (toSheafify_naturality (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).map a))) x
  have hx := ConcreteCategory.congr_hom
    (congrArg (fun k ↦ k.app U)
      (toSheafify_naturality (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).map a))) x
  change cB.hom.app U (aY.hom.app (op ((proEtaleIsoPostcompose g).obj U.unop))
    ((inv cA).hom.app U _)) = _
  erw [hi']
  change (toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj B)).app
      (op ((proEtaleIsoPostcompose g).obj U.unop)) (a x) =
    aY.hom.app (op ((proEtaleIsoPostcompose g).obj U.unop))
      ((toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A)).app
        (op ((proEtaleIsoPostcompose g).obj U.unop)) x) at hy
  erw [← hy, hcB U.unop (a x)]
  exact hx
private theorem scalarTransport_square
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    {X Y : AlgebraicGeometry.Scheme.{t}} (g : X ⟶ Y) [IsIso g] :
    (isoSectionwiseInverseImage g RingCat.{max u (t + 1)}).map
        ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
            (completedCoefficientMap l E L ι Y)) ≫
        inverseImageCompletedCoefficientMap l L g =
      inverseImageCompletedCoefficientMap l E g ≫
        (sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
            (completedCoefficientMap l E L ι X) := by
  let I := isoSectionwiseInverseImage g RingCat.{max u (t + 1)}
  let WX := sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})
  let WY := sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})
  have hproj (F : Type u) [Field F] [Algebra ℚ_[l] F]
      [FiniteDimensional ℚ_[l] F] (W : AlgebraicGeometry.Scheme.{t}) (n : ℕ) :
      (sheafCompose (ProEt.topology W)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
          (completedIntegralCommRingProjectionUnrestricted l F W n) =
        limit.π (integralCoefficientSheafSystem l F W) (op n) := by
    ext U x
    rfl
  have hscalar (W : AlgebraicGeometry.Scheme.{t}) (n : ℕ) :
      (sheafCompose (ProEt.topology W)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
          (completedCoefficientMap l E L ι W) ≫
          limit.π (integralCoefficientSheafSystem l L W) (op n) =
        limit.π (integralCoefficientSheafSystem l E W) (op n) ≫
          (sheafCompose (ProEt.topology W)
            (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
              (integralScalarQuotientSheafMap l E L ι W n) := by
    have h := congrArg
      (fun a ↦ (sheafCompose (ProEt.topology W)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map a)
      (completedCoefficientMap_projection l E L ι W n)
    simpa only [CategoryTheory.Functor.map_comp, hproj] using h
  have hc (F : Type u) [Field F] [Algebra ℚ_[l] F]
      [FiniteDimensional ℚ_[l] F] (n : ℕ) :
      inverseImageCompletedCoefficientMap l F g ≫
          limit.π (integralCoefficientSheafSystem l F X) (op n) =
        I.map (limit.π (integralCoefficientSheafSystem l F Y) (op n)) ≫
          inverseImageFiniteCoefficientMap l F g n := by
    exact limit.lift_π _ (op n)
  apply limit.hom_ext
  intro n
  change (I.map (WY.map (completedCoefficientMap l E L ι Y)) ≫
      inverseImageCompletedCoefficientMap l L g) ≫
      limit.π (integralCoefficientSheafSystem l L X) (op n.unop) =
    (inverseImageCompletedCoefficientMap l E g ≫
      WX.map (completedCoefficientMap l E L ι X)) ≫
      limit.π (integralCoefficientSheafSystem l L X) (op n.unop)
  rw [Category.assoc, hc L n.unop, ← Category.assoc, ← I.map_comp,
    hscalar Y n.unop, I.map_comp, Category.assoc]
  rw [Category.assoc, hscalar X n.unop]
  have hce := hc E n.unop
  erw [reassoc_of% hce]
  congr 1
  exact constantTransport_natural g _

attribute [local irreducible] completedScalarChangeData
  completedOrdinaryScalarExtension completedScalarTensorSection
  completedCoefficientMap inverseImageCompletedCoefficientMap
  completedIntegralCoefficientSheafUnrestricted

private local instance (W : Scheme.{t}) : EssentiallySmall.{max u (t + 1)} W.ProEt :=
  essentiallySmallSelf.{u, t, t + 1} _

private local instance (W : Scheme.{t}) :
    HasSheafify (ProEt.topology W) AddCommGrpCat.{max u (t + 1)} :=
  integralCoefficientAbSheafify.{t, u} W

private local instance (W : Scheme.{t}) :
    (ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{max u (t + 1)} :=
  integralCoefficientAbLocallyBijective.{t, u} W

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem completedAdjunction (W : AlgebraicGeometry.Scheme.{t}) :
    ∃ a : completedOrdinaryScalarExtension l E L ι W ⊣
      SheafOfModules.restrictScalars ((sheafCompose (ProEt.topology W)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
          (completedCoefficientMap l E L ι W)),
      ∀ (M : integralTowerModules l E W) (U : W.ProEtᵒᵖ) (x : M.val.obj U),
        (a.unit.app M).val.app U x = completedScalarTensorSection l E L ι W M U 1 x := by
  obtain ⟨_, _, h⟩ := SheafOfModules.sheafRingCoefficientOrdinaryAdjunction
    (completedCoefficientMap l E L ι W)
  obtain ⟨a, ha⟩ := h (completedOrdinaryScalarExtension l E L ι W)
    (completedOrdinaryScalarExtension_obj l E L ι W)
    (completedOrdinaryScalarExtension_map l E L ι W)
  refine ⟨a, ?_⟩
  intro M U x
  have h := ha M ((completedOrdinaryScalarExtension l E L ι W).obj M)
    (eqToHom (completedOrdinaryScalarExtension_obj l E L ι W M).symm) U x
  simp only [eqToHom_trans, eqToHom_refl] at h
  rw [Adjunction.homEquiv_id] at h
  unfold completedOrdinaryScalarExtension at *
  simpa only [completedScalarTensorSection] using h

private theorem completedTransportEquivalence
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F] :
    (inverseImageIntegralModules l F g).IsEquivalence := by
  exact scalarTransport_isEquivalence g (asIso (inverseImageCompletedCoefficientMap l F g))

private def sectionwiseRestrictionSquare
    {RY SY : Sheaf (ProEt.topology Y) RingCat.{max u (t + 1)}}
    {RX SX : Sheaf (ProEt.topology X) RingCat.{max u (t + 1)}}
    (φY : RY ⟶ SY) (φX : RX ⟶ SX)
    (cR : (isoSectionwiseInverseImage g RingCat.{max u (t + 1)}).obj RY ⟶ RX)
    (cS : (isoSectionwiseInverseImage g RingCat.{max u (t + 1)}).obj SY ⟶ SX)
    [IsIso cR] [IsIso cS]
    (hsq : (isoSectionwiseInverseImage g RingCat.{max u (t + 1)}).map φY ≫ cS =
      cR ≫ φX) :
    SheafOfModules.restrictScalars φY ⋙ isoSectionwiseModuleInverseImage g cR ≅
      isoSectionwiseModuleInverseImage g cS ⋙ SheafOfModules.restrictScalars φX := by
  let I := isoSectionwiseInverseImage g RingCat.{max u (t + 1)}
  have hi : inv cR ≫ I.map φY = φX ≫ inv cS := by
    apply (cancel_mono cS).1
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rw [hsq, IsIso.inv_hom_id_assoc]
  refine NatIso.ofComponents (fun M ↦
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun U ↦ LinearEquiv.toModuleIso
        (m₁ := (((SheafOfModules.restrictScalars φY ⋙
          isoSectionwiseModuleInverseImage g cR).obj M).val.obj U).isModule)
        (m₂ := (((isoSectionwiseModuleInverseImage g cS ⋙
          SheafOfModules.restrictScalars φX).obj M).val.obj U).isModule)
        { toFun := fun x ↦ x
          invFun := fun x ↦ x
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl
          map_add' := fun _ _ ↦ rfl
          map_smul' := ?_ }) (fun _ _ f ↦ by ext x; rfl))) (fun f ↦ by ext U x; rfl)
  intro r x
  let y : M.val.obj (op ((proEtaleIsoPostcompose g).obj U.unop)) := x
  change φY.hom.app (op ((proEtaleIsoPostcompose g).obj U.unop))
      ((inv cR).hom.app U r) • y = (inv cS).hom.app U (φX.hom.app U r) • y
  exact congrArg (fun z ↦ z • y) (congrArg (fun f ↦ f.hom.app U r) hi)

private def restrictionSquare :
    SheafOfModules.restrictScalars
        ((sheafCompose (ProEt.topology Y) (forget₂ CommRingCat RingCat)).map
          (completedCoefficientMap l E L ι Y)) ⋙ inverseImageIntegralModules l E g ≅
      inverseImageIntegralModules l L g ⋙ SheafOfModules.restrictScalars
        ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat RingCat)).map
          (completedCoefficientMap l E L ι X)) :=
  sectionwiseRestrictionSquare g _ _ _ _ (scalarTransport_square l E L ι g)

private theorem restrictionSquare_apply
    (M : integralTowerModules l L Y) (U : X.ProEtᵒᵖ)
    (x : M.val.obj (op ((proEtaleIsoPostcompose g).obj U.unop))) :
    ((restrictionSquare l E L ι g).hom.app M).val.app U x = x := by
  rfl

attribute [local irreducible] restrictionSquare scalarSquareIso

private theorem completedTensorOne :
    ∃ b : inverseImageIntegralModules l E g ⋙ completedOrdinaryScalarExtension l E L ι X ≅
        completedOrdinaryScalarExtension l E L ι Y ⋙ inverseImageIntegralModules l L g,
      ∀ (M : integralTowerModules l E Y) (U : X.ProEt)
        (p : M.val.obj (op ((proEtaleIsoPostcompose g).obj U))),
        (b.hom.app M).val.app (op U)
          (completedScalarTensorSection l E L ι X
            ((inverseImageIntegralModules l E g).obj M) (op U) 1 p) =
          completedScalarTensorSection l E L ι Y M
            (op ((proEtaleIsoPostcompose g).obj U)) 1 p := by
  let F := inverseImageIntegralModules l E g
  let G := inverseImageIntegralModules l L g
  let : F.IsEquivalence := completedTransportEquivalence l g E
  let : G.IsEquivalence := completedTransportEquivalence l g L
  obtain ⟨aX, haX⟩ := completedAdjunction l E L ι X
  obtain ⟨aY, haY⟩ := completedAdjunction l E L ι Y
  let e := restrictionSquare l E L ι g
  let b := scalarSquareIso F G aY aX e
  refine ⟨b, ?_⟩
  intro M U p
  have h := congrArg (fun f ↦ f.val.app (op U) p)
    (scalarSquareIso_unit F G aY aX e M)
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply] at h
  have h' := h.trans (restrictionSquare_apply l E L ι g
    ((completedOrdinaryScalarExtension l E L ι Y).obj M) (op U)
    (((F.map (aY.unit.app M)).val.app (op U)) p))
  change (b.hom.app M).val.app (op U) ((aX.unit.app (F.obj M)).val.app (op U) p) =
    (aY.unit.app M).val.app (op ((proEtaleIsoPostcompose g).obj U)) p at h'
  exact (congrArg ((b.hom.app M).val.app (op U))
    (haX (F.obj M) (op U) p).symm).trans
      (h'.trans (haY M (op ((proEtaleIsoPostcompose g).obj U)) p))

private theorem tensorSection_smul (W : AlgebraicGeometry.Scheme.{t})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{max u (t + 1)}} (φ : R ⟶ S)
    (M : SheafOfModules.{max u (t + 1)}
      ((sheafCompose (ProEt.topology W)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R))
    (A : SheafOfModules.{max u (t + 1)}
      ((sheafCompose (ProEt.topology W)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj S))
    (hA : A = SheafOfModules.changeOfRings.{t, t + 1, max u (t + 1)} φ M)
    (U : W.ProEtᵒᵖ) (a : S.obj.obj U) (x : M.val.obj U) :
    (eqToHom hA.symm).val.app U
        ((toSheafify (ProEt.topology W)
          (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, max u (t + 1)} φ M).presheaf).app U
            (a ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x)) =
      a • ((eqToHom hA.symm).val.app U
        ((toSheafify (ProEt.topology W)
          (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, max u (t + 1)} φ M).presheaf).app U
            ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x))) := by
  subst A
  let k := ((PresheafOfModules.sheafificationAdjunction.{max u (t + 1)}
    (𝟙 ((sheafCompose (ProEt.topology W)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj S).obj)).unit.app
    (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, max u (t + 1)} φ M)).app U ≫
      (ModuleCat.restrictScalarsId (S.obj.obj U)).hom.app _
  change k (a ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x) =
    a • k ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x)
  have ht : a ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x =
      a • ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x) := by
    change a ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x =
      (a * 1) ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x
    rw [mul_one]
  rw [ht]
  exact k.hom.map_smul a _

private theorem completedTensor_smul (W : Scheme.{t})
    (M : integralTowerModules l E W) (U : W.ProEtᵒᵖ)
    (a : (completedIntegralCommRingSheafUnrestricted l L W).obj.obj U)
    (x : M.val.obj U) :
    completedScalarTensorSection l E L ι W M U a x =
      a • completedScalarTensorSection l E L ι W M U 1 x := by
  unfold completedScalarTensorSection completedOrdinaryScalarExtension
  exact
    tensorSection_smul W (completedCoefficientMap l E L ι W) M _
      ((completedScalarChangeData l E L ι W).choose_spec.choose M) U a x

/-- The completed tensor comparison on sheaves, normalized on every pure tensor. -/
theorem completed_formula_chain_data :
    ∃ b : inverseImageIntegralModules l E g ⋙ completedOrdinaryScalarExtension l E L ι X ≅
        completedOrdinaryScalarExtension l E L ι Y ⋙ inverseImageIntegralModules l L g,
      ∀ (M : integralTowerModules l E Y) (U : X.ProEt)
        (p : M.val.obj (op ((proEtaleIsoPostcompose g).obj U)))
        (a : (completedIntegralCommRingSheafUnrestricted l L Y).obj.obj
          (op ((proEtaleIsoPostcompose g).obj U))),
        (b.hom.app M).val.app (op U)
          (completedScalarTensorSection l E L ι X
            ((inverseImageIntegralModules l E g).obj M) (op U)
            ((inverseImageCompletedCoefficientMap l L g).hom.app (op U) a) p) =
          completedScalarTensorSection l E L ι Y M
            (op ((proEtaleIsoPostcompose g).obj U)) a p := by
  obtain ⟨b, hb⟩ := completedTensorOne l E L ι g
  refine ⟨b, ?_⟩
  intro M U p a
  let c := inverseImageCompletedCoefficientMap l L g
  let z : (((inverseImageIntegralModules l L g).obj
      ((completedOrdinaryScalarExtension l E L ι Y).obj M)).val.obj (op U)) :=
    completedScalarTensorSection l E L ι Y M
      (op ((proEtaleIsoPostcompose g).obj U)) 1 p
  calc
    _ = c.hom.app (op U) a • ((b.hom.app M).val.app (op U)
        (completedScalarTensorSection l E L ι X
          ((inverseImageIntegralModules l E g).obj M) (op U) 1 p)) := by
      rw [completedTensor_smul]
      exact ((b.hom.app M).val.app (op U)).hom.map_smul _ _
    _ = c.hom.app (op U) a • z := congrArg (fun z ↦ c.hom.app (op U) a • z) (hb M U p)
    _ = a • completedScalarTensorSection l E L ι Y M
        (op ((proEtaleIsoPostcompose g).obj U)) 1 p := by
      change (inv c).hom.app (op U) (c.hom.app (op U) a) •
        completedScalarTensorSection l E L ι Y M
          (op ((proEtaleIsoPostcompose g).obj U)) 1 p = _
      have hi := congrArg (fun f ↦ f.hom.app (op U) a) (IsIso.hom_inv_id c)
      change (inv c).hom.app (op U) (c.hom.app (op U) a) = a at hi
      rw [hi]
    _ = _ := (completedTensor_smul l E L ι Y M _ a p).symm

end AlgebraicGeometry.ProEtale.IsomorphismScalarTensor
