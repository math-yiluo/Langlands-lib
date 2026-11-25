/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
public import Mathlib.CategoryTheory.Sites.Pullback
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.Colimits
public import WeilConjectures.CategoryTheory.SitePullbackAbelianUnderlying
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement

import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import Mathlib.CategoryTheory.Sites.Pullback
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageCanonicalUnit
import all WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Category.ModuleCat.AB
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all Mathlib.CategoryTheory.Sites.Sheafification
import all WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all Mathlib.CategoryTheory.Monoidal.Ring
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import all WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
import all WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import all WeilConjectures.CategoryTheory.ModuleInverseImageAction
import all Mathlib.Algebra.Category.Ring.Limits
import all WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
import all WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageUnitComparison
import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorComparisonOfUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImageTensorComparison

/-!
# Normalized tensor comparison for pro-etale inverse image

## References

* Stacks, Section 03EK
* Stacks Project, Modules on Sites, Section 03EK and Tag 03D7
* Stacks Project, Modules on Sites, Tag 03D2
* Stacks Project, Sites, Tag 00YV, and Modules on Sites, Tag 03D2
* Stacks, Tags 03EK, 03EL and 09A5, with Tags 00VE, 00WH, 00WX and 03CB for coherence
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme SheafOfModules

namespace AlgebraicGeometry.ProEtaleTensorComparison

/-- The recorded sheafification of the sectionwise tensor product. -/
noncomputable abbrev tensor {X : Scheme.{u}} {R : Rings X} (M N : Modules R) : Modules R :=
  (siteSheafTensorRight N).obj M

/-- The local pure tensor followed by the existing sheafification unit. -/
noncomputable abbrev pure {X : Scheme.{u}} {R : Rings X} (M N : Modules R)
    (V : X.ProEt) (s : M.val.obj (op V)) (t : N.val.obj (op V)) :=
  siteSheafTensorTmul M N (op V) s t

private theorem inverseSection_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Rings Y) (M : Modules R) (U : Y.ProEtᵒᵖ) (s : M.val.obj U) :
    ((AlgebraicGeometry.Scheme.canonicalAdjunction f R).unit.app M).val.app U s =
      inverseSection f (R := R) M U.unop s := by
  exact AlgebraicGeometry.Scheme.canonicalUnit_sections f R M U s

-- Use the canonical-unit API without unfolding the small-model module construction.
attribute [local irreducible] proEtaleModuleInverseImage inverseSection

/-- The canonical ring compositor is the adjoint conjugate of pullback associativity. -/
noncomputable def ringComp {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z)
    (R : Rings Z) : inverseRing (g ≫ h) R ≅ inverseRing g (inverseRing h R) :=
  ((conjugateIsoEquiv
    ((proEtaleSheafAdjunction h CommRingCat.{u + 1}).comp
      (proEtaleSheafAdjunction g CommRingCat.{u + 1}))
    (proEtaleSheafAdjunction (g ≫ h) CommRingCat.{u + 1})).symm
      (AlgebraicGeometry.ProEtale.lowerStarComp CommRingCat.{u + 1} g h)).app R

private theorem ringComp_unit {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z)
    (R : Rings Z) (U : Z.ProEtᵒᵖ) (r : R.obj.obj U) :
    (ringComp g h R).hom.hom.app ((proEtaleBaseChange (g ≫ h)).op.obj U)
      (((proEtaleSheafAdjunction (g ≫ h) CommRingCat.{u + 1}).unit.app R).hom.app U r) =
    (inverseRing g (inverseRing h R)).obj.map ((MorphismProperty.Over.pullbackComp
        (P := @WeaklyEtale) (Q := ⊤) g h).hom.app U.unop).op
      (((proEtaleSheafAdjunction g CommRingCat.{u + 1}).unit.app (inverseRing h R)).hom.app
        ((proEtaleBaseChange h).op.obj U)
          (((proEtaleSheafAdjunction h CommRingCat.{u + 1}).unit.app R).hom.app U r)) := by
  have hu := (unit_conjugateEquiv_symm
    ((proEtaleSheafAdjunction h CommRingCat.{u + 1}).comp
      (proEtaleSheafAdjunction g CommRingCat.{u + 1}))
    (proEtaleSheafAdjunction (g ≫ h) CommRingCat.{u + 1})
    (AlgebraicGeometry.ProEtale.lowerStarComp CommRingCat.{u + 1} g h).hom R).symm
  unfold ringComp
  exact congrArg (fun z ↦ z.hom.app U r) hu

-- Treat the adjoint-conjugation data through its unit equations.
attribute [local irreducible] ringComp

/-- Restriction of scalars is Mathlib's existing functor. -/
noncomputable abbrev restrict {X : Scheme.{u}} {R S : Rings X} (a : R ⟶ S) :
    Modules S ⥤ Modules R :=
  SheafOfModules.restrictScalars.{u + 1}
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map a)

/-- Inverse image on ring morphisms, from the recorded functor. -/
noncomputable abbrev inverseRingMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    {R S : Rings Y} (a : R ⟶ S) :=
  (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map a

-- Restrict a tensor pairing at the level of modules, before using it on sheaf sections.
private noncomputable def restrictedTensorPairing {A B : Type u} [CommRing A] [CommRing B]
    (c : A →+* B) (M N P : ModuleCat.{u} B) (f : TensorProduct B M N →ₗ[B] P) :
    (ModuleCat.restrictScalars c).obj M →ₗ[A]
      (ModuleCat.restrictScalars c).obj N →ₗ[A] (ModuleCat.restrictScalars c).obj P :=
  let b := (TensorProduct.mk B M N).compr₂ f
  LinearMap.mk₂ A (fun x y ↦ b x y)
    (fun x y z ↦ LinearMap.congr_fun (b.map_add x y) z)
    (fun r x y ↦ LinearMap.congr_fun (b.map_smul (c r) x) y)
    (fun x y z ↦ (b x).map_add y z)
    (fun r x y ↦ (b x).map_smul (c r) y)

/-- The coefficient quotient is uniquely fixed by local pure tensors. -/
theorem coefficientQuotient_exists {X : Scheme.{u}} {R S : Rings X} (a : R ⟶ S)
    (M N : Modules S) :
    ∃! p : tensor ((restrict a).obj M) ((restrict a).obj N) ⟶
        (restrict a).obj (tensor M N),
      ∀ (V : X.ProEt) (s : M.val.obj (op V)) (t : N.val.obj (op V)),
        p.val.app (op V) (pure ((restrict a).obj M) ((restrict a).obj N) V s t) =
          pure M N V s t := by
  let adj := PresheafOfModules.sheafificationAdjunction.{u + 1}
    (𝟙 ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj)
  let adjS := PresheafOfModules.sheafificationAdjunction.{u + 1}
    (𝟙 ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S).obj)
  let β (U : X.ProEtᵒᵖ) :
      ((restrict a).obj M).val.obj U →ₗ[R.obj.obj U]
        ((restrict a).obj N).val.obj U →ₗ[R.obj.obj U]
          ((restrict a).obj (tensor M N)).val.obj U :=
    restrictedTensorPairing (a.hom.app U).hom (M.val.obj U) (N.val.obj U)
      ((tensor M N).val.obj U)
      ((adjS.unit.app (siteTensorPresheaf M.val N.val)).app U).hom
  let q : siteTensorPresheaf ((restrict a).obj M).val ((restrict a).obj N).val ⟶
      ((restrict a).obj (tensor M N)).val :=
    { app := fun U ↦ ModuleCat.ofHom
        (X := (siteTensorPresheaf ((restrict a).obj M).val ((restrict a).obj N).val).obj U)
        (Y := ((restrict a).obj (tensor M N)).val.obj U) (TensorProduct.lift (β U))
      naturality := by
        intro U V i
        ext t
        induction t using TensorProduct.inductionOn with
        | tmul x y =>
          change pure M N V.unop (M.val.map i x) (N.val.map i y) =
            (tensor M N).val.map i (pure M N U.unop x y)
          exact PresheafOfModules.naturality_apply
            (adjS.unit.app (siteTensorPresheaf M.val N.val)) i (x ⊗ₜ[S.obj.obj U] y)
        | add t s ht hs => simp only [map_add, ht, hs] }
  let p := (adj.homEquiv _ ((restrict a).obj (tensor M N))).symm q
  have hp : ∀ (V : X.ProEt) (s : M.val.obj (op V)) (t : N.val.obj (op V)),
      p.val.app (op V) (pure ((restrict a).obj M) ((restrict a).obj N) V s t) =
        pure M N V s t := by
    intro V s t
    have h := (adj.homEquiv _ ((restrict a).obj (tensor M N))).apply_symm_apply q
    rw [Adjunction.homEquiv_unit] at h
    exact congrArg (fun k ↦ k.app (op V) (s ⊗ₜ[R.obj.obj (op V)] t)) h
  refine ⟨p, hp, ?_⟩
  intro p' hp'
  apply (adj.homEquiv _ ((restrict a).obj (tensor M N))).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro U
  ext t
  induction t using TensorProduct.inductionOn with
  | tmul x y => exact (hp' U.unop x y).trans (hp U.unop x y).symm
  | add t s ht hs => simp only [map_add, ht, hs]

/-- The canonical map from the tensor over R to the tensor over S, selected from its
unique universal-property characterization, rather than from mere existence. -/
noncomputable def coefficientQuotient {X : Scheme.{u}} {R S : Rings X} (a : R ⟶ S)
    (M N : Modules S) :
    tensor ((restrict a).obj M) ((restrict a).obj N) ⟶ (restrict a).obj (tensor M N) :=
  Classical.choose (coefficientQuotient_exists a M N)

/-- Inverse image commutes with restriction of the scalar action through a ring map;
the identification is uniquely normalized by the actual adjunction units. -/
theorem scalarIdentification_exists {X Y : Scheme.{u}} (f : X ⟶ Y)
    {R S : Rings Y} (a : R ⟶ S) (M : Modules S) :
    ∃! e : (inverse f R).obj ((restrict a).obj M) ≅
        (restrict (inverseRingMap f a)).obj ((inverse f S).obj M),
      ∀ (V : Y.ProEt) (s : M.val.obj (op V)),
        e.hom.val.app (op ((proEtaleBaseChange f).obj V))
          (inverseSection f ((restrict a).obj M) V s) = inverseSection f M V s := by
  let aiR := AlgebraicGeometry.Scheme.canonicalAdjunction f R
  let aiS := AlgebraicGeometry.Scheme.canonicalAdjunction f S
  let η := aiS.unit.app M
  let M' := (restrict (inverseRingMap f a)).obj ((inverse f S).obj M)
  let k : (restrict a).obj M ⟶
      (AlgebraicGeometry.Scheme.T f R).obj M' :=
    { val :=
      { app := fun U ↦ ModuleCat.ofHom
          (X := ((restrict a).obj M).val.obj U)
          (Y := ((AlgebraicGeometry.Scheme.T f R).obj M').val.obj U)
          { toFun := η.val.app U
            map_add' := (η.val.app U).hom.map_add
            map_smul' := by
              intro r m
              change η.val.app U (a.hom.app U r • (show M.val.obj U from m)) =
                (inverseRingMap f a).hom.app ((proEtaleBaseChange f).op.obj U)
                  (((proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app R).hom.app U r) •
                    (show ((inverse f S).obj M).val.obj
                      ((proEtaleBaseChange f).op.obj U) from η.val.app U m)
              have h := congrArg (fun z ↦ z.hom.app U r)
                ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.naturality a)
              change ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app S).hom.app U
                (a.hom.app U r) = _ at h
              exact ((η.val.app U).hom.map_smul (a.hom.app U r) m).trans
                (congrArg (fun t ↦ t • (show ((inverse f S).obj M).val.obj
                    ((proEtaleBaseChange f).op.obj U) from η.val.app U m)) h) }
        naturality := by
          intro U V i
          ext m
          exact PresheafOfModules.naturality_apply η.val i m } }
  let p := (aiR.homEquiv ((restrict a).obj M) M').symm k
  have hp : ∀ (V : Y.ProEt) (s : M.val.obj (op V)),
      p.val.app (op ((proEtaleBaseChange f).obj V))
        (inverseSection f ((restrict a).obj M) V s) = inverseSection f M V s := by
    intro V s
    have h := (aiR.homEquiv ((restrict a).obj M) M').apply_symm_apply k
    rw [Adjunction.homEquiv_unit] at h
    have hh := congrArg (fun z ↦ z.val.app (op V) s) h
    change p.val.app (op ((proEtaleBaseChange f).obj V))
      (((aiR.unit.app ((restrict a).obj M)).val.app (op V)) s) = η.val.app (op V) s at hh
    rw [inverseSection_unit] at hh
    exact hh.trans (inverseSection_unit f S M (op V) s)
  clear_value p
  let U := toSheaf ((sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (inverseRing f R)) ⋙
      sheafCompose (ProEt.topology X) (CategoryTheory.forget AddCommGrpCat.{u + 1})
  have he : (moduleSetsIdentification f ((restrict a).obj M)).hom ≫ U.map p =
      (moduleSetsIdentification f M).hom := by
    apply ((AlgebraicGeometry.ProEtale.setPullbackAdjunction f).homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    ext V s
    have hM := (Classical.choose_spec
      (moduleSetsIdentification_exists f ((restrict a).obj M))).1 V.unop s
    have hN := (Classical.choose_spec
      (moduleSetsIdentification_exists f M)).1 V.unop s
    exact (congrArg (p.val.app ((proEtaleBaseChange f).op.obj V)) hM).trans
      ((hp V.unop s).trans hN.symm)
  have : IsIso (U.map p) := by
    have hh : U.map p = (moduleSetsIdentification f ((restrict a).obj M)).inv ≫
        (moduleSetsIdentification f M).hom := by
      rw [← he]
      simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    rw [hh]
    exact inferInstanceAs (IsIso (((moduleSetsIdentification f ((restrict a).obj M)).symm ≪≫
      moduleSetsIdentification f M).hom))
  have : IsIso p := isIso_of_reflects_iso p U
  refine ⟨asIso p, hp, ?_⟩
  intro e he'
  apply Iso.ext
  apply U.map_injective
  apply (cancel_epi (moduleSetsIdentification f ((restrict a).obj M)).hom).mp
  apply ((AlgebraicGeometry.ProEtale.setPullbackAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  ext V s
  have hM := (Classical.choose_spec
    (moduleSetsIdentification_exists f ((restrict a).obj M))).1 V.unop s
  exact (congrArg (e.hom.val.app ((proEtaleBaseChange f).op.obj V)) hM).trans
    (((he' V.unop s).trans (hp V.unop s).symm).trans
      (congrArg (p.val.app ((proEtaleBaseChange f).op.obj V)) hM).symm)

/-- The unit-normalized scalar identification; uniqueness determines its data. -/
noncomputable def scalarIdentification {X Y : Scheme.{u}} (f : X ⟶ Y)
    {R S : Rings Y} (a : R ⟶ S) (M : Modules S) :
    (inverse f R).obj ((restrict a).obj M) ≅
      (restrict (inverseRingMap f a)).obj ((inverse f S).obj M) :=
  Classical.choose (scalarIdentification_exists f a M)

section TensorPairing

universe uC vC uD vD r

/-- Pair two maps into module pushforwards, then use the sectionwise tensor universal
property and module sheafification. The uniqueness is the same universal property. -/
private theorem tensorPushforwardPairing_exists
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasWeakSheafify J AddCommGrpCat.{r}] [HasWeakSheafify K AddCommGrpCat.{r}]
    (F : C ⥤ D) [F.IsContinuous J K]
    (R : Sheaf J CommRingCat.{r}) (S : Sheaf K CommRingCat.{r})
    (a : R ⟶ (F.sheafPushforwardContinuous CommRingCat.{r} J K).obj S)
    (M N : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (P Q : SheafOfModules.{r} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S))
    (ηM : M ⟶ (SheafOfModules.pushforward.{r} (F := F) (J := J) (K := K)
      (R := (sheafCompose K (forget₂ CommRingCat.{r} RingCat.{r})).obj S)
      (S := (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)
      ⟨Functor.whiskerRight a.hom (forget₂ CommRingCat RingCat)⟩).obj P)
    (ηN : N ⟶ (SheafOfModules.pushforward.{r} (F := F) (J := J) (K := K)
      (R := (sheafCompose K (forget₂ CommRingCat.{r} RingCat.{r})).obj S)
      (S := (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)
      ⟨Functor.whiskerRight a.hom (forget₂ CommRingCat RingCat)⟩).obj Q) :
    let T := SheafOfModules.pushforward.{r} (F := F) (J := J) (K := K)
      (R := (sheafCompose K (forget₂ CommRingCat.{r} RingCat.{r})).obj S)
      (S := (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)
      ⟨Functor.whiskerRight a.hom (forget₂ CommRingCat RingCat)⟩
    ∃! k : (siteSheafTensorRight N).obj M ⟶ T.obj ((siteSheafTensorRight Q).obj P),
      ∀ (V : C) (x : M.val.obj (op V)) (y : N.val.obj (op V)),
        k.val.app (op V) (siteSheafTensorTmul M N (op V) x y) =
          siteSheafTensorTmul P Q (op (F.obj V))
            (ηM.val.app (op V) x) (ηN.val.app (op V) y) := by
  let T := SheafOfModules.pushforward.{r} (F := F) (J := J) (K := K)
      (R := (sheafCompose K (forget₂ CommRingCat.{r} RingCat.{r})).obj S)
      (S := (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)
    ⟨Functor.whiskerRight a.hom (forget₂ CommRingCat RingCat)⟩
  let H := (siteSheafTensorRight Q).obj P
  let adj := PresheafOfModules.sheafificationAdjunction.{r}
    (𝟙 ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R).obj)
  let adjX := PresheafOfModules.sheafificationAdjunction.{r}
    (𝟙 ((sheafCompose K
      (forget₂ CommRingCat.{r} RingCat.{r})).obj S).obj)
  let β (U : Cᵒᵖ) : M.val.obj U →ₗ[R.obj.obj U]
      N.val.obj U →ₗ[R.obj.obj U]
        (T.obj H).val.obj U :=
    (restrictedTensorPairing (a.hom.app U).hom (P.val.obj (F.op.obj U))
      (Q.val.obj (F.op.obj U)) (H.val.obj (F.op.obj U))
      ((adjX.unit.app (siteTensorPresheaf P.val Q.val)).app (F.op.obj U)).hom).compl₁₂
        (ηM.val.app U).hom (ηN.val.app U).hom
  let q : siteTensorPresheaf M.val N.val ⟶
      (T.obj H).val :=
    { app := fun U ↦ ModuleCat.ofHom
        (X := (siteTensorPresheaf M.val N.val).obj U)
        (Y := (T.obj H).val.obj U)
        (TensorProduct.lift (β U))
      naturality := by
        intro U V i
        ext t
        induction t using TensorProduct.inductionOn with
        | tmul x y =>
          change siteSheafTensorTmul P Q (F.op.obj V)
            (ηM.val.app V (M.val.map i x)) (ηN.val.app V (N.val.map i y)) =
            H.val.map (F.op.map i)
              (siteSheafTensorTmul P Q (F.op.obj U)
                (ηM.val.app U x) (ηN.val.app U y))
          rw [PresheafOfModules.naturality_apply ηM.val i x,
            PresheafOfModules.naturality_apply ηN.val i y]
          exact PresheafOfModules.naturality_apply
            (adjX.unit.app (siteTensorPresheaf P.val Q.val))
              (F.op.map i)
                (ηM.val.app U x ⊗ₜ[S.obj.obj
                  (F.op.obj U)] ηN.val.app U y)
        | add t s ht hs => simp only [map_add, ht, hs] }
  let k := (adj.homEquiv _ (T.obj H)).symm q
  have hk (V : C) (x : M.val.obj (op V)) (y : N.val.obj (op V)) :
      k.val.app (op V) (siteSheafTensorTmul M N (op V) x y) =
        siteSheafTensorTmul P Q (op (F.obj V))
          (ηM.val.app (op V) x) (ηN.val.app (op V) y) := by
    have h := (adj.homEquiv _ (T.obj H)).apply_symm_apply q
    rw [Adjunction.homEquiv_unit] at h
    exact congrArg (fun z ↦ z.app (op V) (x ⊗ₜ[R.obj.obj (op V)] y)) h
  refine ⟨k, hk, ?_⟩
  intro k' hk'
  apply (adj.homEquiv _ (T.obj H)).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro U
  ext t
  induction t using TensorProduct.inductionOn with
  | tmul x y => exact (hk' U.unop x y).trans (hk U.unop x y).symm
  | add t s ht hs => simp only [map_add, ht, hs]

end TensorPairing

/-- Existence and uniqueness of the module tensor comparison with its local normalization. -/
theorem comparison_exists {X Y : Scheme.{u}} (f : X ⟶ Y) (R : Rings Y)
    (M N : Modules R) :
    ∃! s : (inverse f R).obj (tensor M N) ⟶
        tensor ((inverse f R).obj M) ((inverse f R).obj N),
      ∀ (V : Y.ProEt) (x : M.val.obj (op V)) (y : N.val.obj (op V)),
        s.val.app (op ((proEtaleBaseChange f).obj V))
          (inverseSection f (tensor M N) V (pure M N V x y)) =
        pure ((inverse f R).obj M) ((inverse f R).obj N)
          ((proEtaleBaseChange f).obj V) (inverseSection f M V x) (inverseSection f N V y) := by
  let ai := AlgebraicGeometry.Scheme.canonicalAdjunction f R
  let ηM := ai.unit.app M
  let ηN := ai.unit.app N
  let FM := (inverse f R).obj M
  let FN := (inverse f R).obj N
  let H := tensor FM FN
  obtain ⟨k, hk, hk_unique⟩ := tensorPushforwardPairing_exists (proEtaleBaseChange f)
    R (inverseRing f R) ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app R)
      M N FM FN ηM ηN
  let p := (ai.homEquiv (tensor M N) H).symm k
  have hp : ∀ (V : Y.ProEt) (x : M.val.obj (op V)) (y : N.val.obj (op V)),
      p.val.app (op ((proEtaleBaseChange f).obj V))
        (inverseSection f (tensor M N) V (pure M N V x y)) =
          pure FM FN ((proEtaleBaseChange f).obj V)
            (inverseSection f M V x) (inverseSection f N V y) := by
    intro V x y
    have h := (ai.homEquiv (tensor M N) H).apply_symm_apply k
    rw [Adjunction.homEquiv_unit] at h
    have hh := congrArg (fun z ↦ z.val.app (op V) (pure M N V x y)) h
    change p.val.app (op ((proEtaleBaseChange f).obj V))
      ((ai.unit.app (tensor M N)).val.app (op V) (pure M N V x y)) =
        k.val.app (op V) (pure M N V x y) at hh
    rw [inverseSection_unit] at hh
    exact hh.trans ((hk V x y).trans
      (congrArg₂ (pure FM FN ((proEtaleBaseChange f).obj V))
        (inverseSection_unit f R M (op V) x)
        (inverseSection_unit f R N (op V) y)))
  refine ⟨p, hp, ?_⟩
  intro p' hp'
  apply (ai.homEquiv (tensor M N) H).injective
  refine (hk_unique _ ?_).trans ((ai.homEquiv (tensor M N) H).apply_symm_apply k).symm
  intro V x y
  change p'.val.app (op ((proEtaleBaseChange f).obj V))
    ((ai.unit.app (tensor M N)).val.app (op V) (pure M N V x y)) = _
  rw [inverseSection_unit]
  exact (hp' V x y).trans
    (congrArg₂ (pure FM FN ((proEtaleBaseChange f).obj V))
      (inverseSection_unit f R M (op V) x)
      (inverseSection_unit f R N (op V) y)).symm

/-- The canonical sigma, determined uniquely by its local pure-tensor formula. -/
noncomputable def comparison {X Y : Scheme.{u}} (f : X ⟶ Y) (R : Rings Y)
    (M N : Modules R) :
    (inverse f R).obj (tensor M N) ⟶ tensor ((inverse f R).obj M) ((inverse f R).obj N) :=
  Classical.choose (comparison_exists f R M N)

/-- The tensor map in both variables is the composite of the two recorded factor maps. -/
noncomputable def tensorMap {X : Scheme.{u}} {R : Rings X} {M M' N N' : Modules R}
    (a : M ⟶ M') (b : N ⟶ N') : tensor M N ⟶ tensor M' N' :=
  (siteSheafTensorRight N).map a ≫ siteSheafTensorSecondMap M' b

private theorem tensor_hom_ext {X : Scheme.{u}} {R : Rings X}
    {M N K : Modules R} (p q : tensor M N ⟶ K)
    (h : ∀ (V : X.ProEt) (x : M.val.obj (op V)) (y : N.val.obj (op V)),
      p.val.app (op V) (pure M N V x y) =
        q.val.app (op V) (pure M N V x y)) : p = q := by
  let adj := PresheafOfModules.sheafificationAdjunction.{u + 1}
    (𝟙 ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj)
  apply (adj.homEquiv (siteTensorPresheaf M.val N.val) K).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro U
  ext t
  induction t using TensorProduct.inductionOn with
  | tmul x y => exact h U.unop x y
  | add t s ht hs => simp only [map_add, ht, hs]

/-- Adjunction injectivity tests a module map on the images of original sections. -/
private theorem inverseModule_hom_ext {X Y : Scheme.{u}} (f : X ⟶ Y)
    {R : Rings Y} {M : Modules R} {K : Modules (inverseRing f R)}
    (p q : (inverse f R).obj M ⟶ K)
    (h : ∀ (V : Y.ProEt) (s : M.val.obj (op V)),
      p.val.app (op ((proEtaleBaseChange f).obj V))
          (inverseSection f (R := R) M V s) =
        q.val.app (op ((proEtaleBaseChange f).obj V))
          (inverseSection f (R := R) M V s)) : p = q := by
  let ai := AlgebraicGeometry.Scheme.canonicalAdjunction f R
  apply (ai.homEquiv M K).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  change p.val.app ((proEtaleBaseChange f).op.obj U)
      ((ai.unit.app M).val.app U s) =
    q.val.app ((proEtaleBaseChange f).op.obj U)
      ((ai.unit.app M).val.app U s)
  have hu := inverseSection_unit f R M U s
  exact (congrArg (p.val.app ((proEtaleBaseChange f).op.obj U)) hu).trans
    ((h U.unop s).trans
      (congrArg (q.val.app ((proEtaleBaseChange f).op.obj U)) hu).symm)

private theorem inverseTensor_hom_ext {X Y : Scheme.{u}} (f : X ⟶ Y)
    {R : Rings Y} {M N : Modules R} {K : Modules (inverseRing f R)}
    (p q : (inverse f R).obj (tensor M N) ⟶ K)
    (h : ∀ (V : Y.ProEt) (x : M.val.obj (op V)) (y : N.val.obj (op V)),
      p.val.app (op ((proEtaleBaseChange f).obj V))
          (inverseSection f (R := R) (tensor M N) V (pure M N V x y)) =
        q.val.app (op ((proEtaleBaseChange f).obj V))
          (inverseSection f (R := R) (tensor M N) V (pure M N V x y))) : p = q := by
  let ai := AlgebraicGeometry.Scheme.canonicalAdjunction f R
  apply (ai.homEquiv (tensor M N) K).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply tensor_hom_ext (R := R) (M := M) (N := N)
  intro V x y
  change p.val.app (op ((proEtaleBaseChange f).obj V))
      ((ai.unit.app (tensor M N)).val.app (op V) (pure M N V x y)) =
    q.val.app (op ((proEtaleBaseChange f).obj V))
      ((ai.unit.app (tensor M N)).val.app (op V) (pure M N V x y))
  have hu := inverseSection_unit f R (tensor M N)
    (op V) (pure M N V x y)
  exact (congrArg (p.val.app (op ((proEtaleBaseChange f).obj V))) hu).trans
    ((h V x y).trans
      (congrArg (q.val.app (op ((proEtaleBaseChange f).obj V))) hu).symm)

private theorem inverseSection_map {X Y : Scheme.{u}} (f : X ⟶ Y)
    {R : Rings Y} {M N : Modules R} (k : M ⟶ N)
    (V : Y.ProEt) (x : M.val.obj (op V)) :
    ((inverse f R).map k).val.app (op ((proEtaleBaseChange f).obj V))
        (inverseSection f (R := R) M V x) = inverseSection f (R := R) N V (k.val.app (op V) x) := by
  have h := congrArg (fun z ↦ z.val.app (op V) x)
    ((AlgebraicGeometry.Scheme.canonicalAdjunction f R).unit.naturality k)
  change ((AlgebraicGeometry.Scheme.canonicalAdjunction f R).unit.app N).val.app
      (op V) (k.val.app (op V) x) =
    ((inverse f R).map k).val.app (op ((proEtaleBaseChange f).obj V))
      (((AlgebraicGeometry.Scheme.canonicalAdjunction f R).unit.app M).val.app
        (op V) x) at h
  have hM := inverseSection_unit f R M (op V) x
  have hN := inverseSection_unit f R N (op V)
    (k.val.app (op V) x)
  exact (congrArg (((inverse f R).map k).val.app
    (op ((proEtaleBaseChange f).obj V))) hM).symm.trans (h.symm.trans hN)

private theorem tensorMap_pure {X : Scheme.{u}} {R : Rings X}
    {M M' N N' : Modules R} (a : M ⟶ M') (b : N ⟶ N')
    (V : X.ProEt) (x : M.val.obj (op V)) (y : N.val.obj (op V)) :
    (tensorMap a b).val.app (op V) (pure M N V x y) =
      pure M' N' V (a.val.app (op V) x) (b.val.app (op V) y) := by
  let adj := PresheafOfModules.sheafificationAdjunction.{u + 1}
    (𝟙 ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj)
  have h₁ := congrArg (fun z ↦ z.app (op V) (x ⊗ₜ[R.obj.obj (op V)] y))
    (adj.unit.naturality (siteTensorHom a.val N.val)).symm
  have h₂ := congrArg (fun z ↦ z.app (op V)
      (a.val.app (op V) x ⊗ₜ[R.obj.obj (op V)] y))
    (adj.unit.naturality (siteTensorSecondMap M'.val b.val)).symm
  change ((siteSheafTensorRight N).map a).val.app (op V) (pure M N V x y) =
    pure M' N V (a.val.app (op V) x) y at h₁
  change (siteSheafTensorSecondMap M' b).val.app (op V)
      (pure M' N V (a.val.app (op V) x) y) =
    pure M' N' V (a.val.app (op V) x) (b.val.app (op V) y) at h₂
  exact (congrArg ((siteSheafTensorSecondMap M' b).val.app (op V)) h₁).trans h₂

private theorem comparison_pure {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Rings Y) (M N : Modules R) (V : Y.ProEt)
    (x : M.val.obj (op V)) (y : N.val.obj (op V)) :
    (comparison f R M N).val.app (op ((proEtaleBaseChange f).obj V))
        (inverseSection f (tensor M N) V (pure M N V x y)) =
      pure ((inverse f R).obj M) ((inverse f R).obj N)
        ((proEtaleBaseChange f).obj V) (inverseSection f M V x) (inverseSection f N V y) :=
  (Classical.choose_spec (comparison_exists f R M N)).1 V x y

private theorem comparison_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Rings Y) {M M' N N' : Modules R} (a : M ⟶ M') (b : N ⟶ N') :
    (inverse f R).map (tensorMap (R := R) a b) ≫ comparison f R M' N' =
      comparison f R M N ≫
        tensorMap (R := inverseRing f R) ((inverse f R).map a) ((inverse f R).map b) := by
  apply inverseTensor_hom_ext f (R := R) (M := M) (N := N)
  intro V x y
  change (comparison f R M' N').val.app (op ((proEtaleBaseChange f).obj V))
      (((inverse f R).map (tensorMap (R := R) a b)).val.app (op ((proEtaleBaseChange f).obj V))
        (inverseSection f (R := R) (tensor M N) V (pure M N V x y))) =
    (tensorMap (R := inverseRing f R) ((inverse f R).map a) ((inverse f R).map b)).val.app
      (op ((proEtaleBaseChange f).obj V))
        ((comparison f R M N).val.app (op ((proEtaleBaseChange f).obj V))
          (inverseSection f (R := R) (tensor M N) V (pure M N V x y)))
  rw [inverseSection_map f (R := R) (tensorMap (R := R) a b) V (pure M N V x y)]
  rw [tensorMap_pure (R := R) a b V x y]
  rw [comparison_pure f R M' N' V (a.val.app (op V) x) (b.val.app (op V) y)]
  rw [comparison_pure f R M N V x y]
  rw [tensorMap_pure (R := inverseRing f R) ((inverse f R).map a) ((inverse f R).map b)
    ((proEtaleBaseChange f).obj V)
    (inverseSection f (R := R) M V x) (inverseSection f (R := R) N V y)]
  exact congrArg₂
    (pure (R := inverseRing f R) ((inverse f R).obj M') ((inverse f R).obj N')
      ((proEtaleBaseChange f).obj V))
    (inverseSection_map f (R := R) a V x).symm
    (inverseSection_map f (R := R) b V y).symm

private theorem coefficientQuotient_pure {X : Scheme.{u}} {R S : Rings X}
    (a : R ⟶ S) (M N : Modules S) (V : X.ProEt)
    (x : M.val.obj (op V)) (y : N.val.obj (op V)) :
    (coefficientQuotient a M N).val.app (op V)
        (pure ((restrict a).obj M) ((restrict a).obj N) V x y) = pure M N V x y :=
  (Classical.choose_spec (coefficientQuotient_exists a M N)).1 V x y

private theorem scalarIdentification_sections {X Y : Scheme.{u}} (f : X ⟶ Y)
    {R S : Rings Y} (a : R ⟶ S) (M : Modules S) (V : Y.ProEt)
    (x : M.val.obj (op V)) :
    (scalarIdentification f a M).hom.val.app (op ((proEtaleBaseChange f).obj V))
        (inverseSection f ((restrict a).obj M) V x) = inverseSection f M V x :=
  (Classical.choose_spec (scalarIdentification_exists f a M)).1 V x

private theorem comparison_coefficient_change {X Y : Scheme.{u}} (f : X ⟶ Y)
    {R S : Rings Y} (a : R ⟶ S) (F G : Modules S) :
    (inverse f R).map (coefficientQuotient (R := R) (S := S) a F G) ≫
        (scalarIdentification f a (tensor (R := S) F G)).hom ≫
        (restrict (R := inverseRing f R) (S := inverseRing f S)
          (inverseRingMap f a)).map (comparison f S F G) =
      comparison f R ((restrict a).obj F) ((restrict a).obj G) ≫
        tensorMap (R := inverseRing f R) (scalarIdentification f a F).hom
            (scalarIdentification f a G).hom ≫
        coefficientQuotient (R := inverseRing f R) (S := inverseRing f S)
          (inverseRingMap f a)
          ((inverse f S).obj F) ((inverse f S).obj G) := by
  apply inverseTensor_hom_ext f (R := R)
    (M := (restrict a).obj F) (N := (restrict a).obj G)
  intro V x y
  change (comparison f S F G).val.app (op ((proEtaleBaseChange f).obj V))
      ((scalarIdentification f a (tensor (R := S) F G)).hom.val.app
        (op ((proEtaleBaseChange f).obj V))
        (((inverse f R).map (coefficientQuotient (R := R) (S := S) a F G)).val.app
          (op ((proEtaleBaseChange f).obj V))
          (inverseSection f (R := R) (tensor (R := R) ((restrict a).obj F) ((restrict a).obj G)) V
            (pure ((restrict a).obj F) ((restrict a).obj G) V x y)))) =
    (coefficientQuotient (R := inverseRing f R) (S := inverseRing f S)
          (inverseRingMap f a)
      ((inverse f S).obj F) ((inverse f S).obj G)).val.app
      (op ((proEtaleBaseChange f).obj V))
      ((tensorMap (R := inverseRing f R) (scalarIdentification f a F).hom
            (scalarIdentification f a G).hom).val.app
        (op ((proEtaleBaseChange f).obj V))
        ((comparison f R ((restrict a).obj F) ((restrict a).obj G)).val.app
          (op ((proEtaleBaseChange f).obj V))
          (inverseSection f (R := R) (tensor (R := R) ((restrict a).obj F) ((restrict a).obj G)) V
            (pure ((restrict a).obj F) ((restrict a).obj G) V x y))))
  rw [inverseSection_map f (R := R) (coefficientQuotient a F G) V
    (pure ((restrict a).obj F) ((restrict a).obj G) V x y)]
  rw [coefficientQuotient_pure a F G V x y]
  rw [scalarIdentification_sections f a (tensor F G) V (pure F G V x y)]
  rw [comparison_pure f S F G V x y]
  rw [comparison_pure f R ((restrict a).obj F) ((restrict a).obj G) V x y]
  rw [tensorMap_pure (R := inverseRing f R)
    (scalarIdentification f a F).hom (scalarIdentification f a G).hom
    ((proEtaleBaseChange f).obj V)
    (inverseSection f (R := R) ((restrict a).obj F) V x)
    (inverseSection f (R := R) ((restrict a).obj G) V y)]
  rw [scalarIdentification_sections f a F V x, scalarIdentification_sections f a G V y]
  exact (coefficientQuotient_pure
    (R := inverseRing f R) (S := inverseRing f S) (inverseRingMap f a)
    ((inverse f S).obj F) ((inverse f S).obj G) ((proEtaleBaseChange f).obj V)
    (inverseSection f (R := S) F V x) (inverseSection f (R := S) G V y)).symm

section IdentityScalars
universe c h r
variable {C : Type c} [Category.{h} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasWeakSheafify J AddCommGrpCat.{r}]
  (A : Sheaf J CommRingCat.{r})
  (P : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A))

open scoped ChangeOfRings

private theorem identityScalarIso_exists :
    ∃! a : changeOfRings (𝟙 A) P ≅ P,
      ∀ (U : Cᵒᵖ) (m : P.val.obj U),
        a.hom.val.app U
          (((PresheafOfModules.sheafificationAdjunction.{r}
            (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A).obj)).unit.app
              (changeOfRingsPresheaf (𝟙 A) P)).app U
                ((1 : A.obj.obj U) ⊗ₜ[A.obj.obj U, ((𝟙 A : A ⟶ A).hom.app U).hom] m)) = m := by
  let G := SheafOfModules.forget ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A) ⋙
    PresheafOfModules.restrictScalars
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A).obj)
  let e : changeOfRingsPresheaf (𝟙 A) P ≅ G.obj P :=
    PresheafOfModules.isoMk
      (fun U ↦ (ModuleCat.extendScalarsId (A.obj.obj U)).app (P.val.obj U)) (by
        intro U V i
        apply ModuleCat.ExtendScalars.hom_ext
        intro m
        let : Module (A.obj.obj V)
            ((ModuleCat.restrictScalars
              (((sheafCompose J (forget₂ CommRingCat RingCat)).obj A).obj.map i).hom).obj
                (P.val.obj V)) := inferInstanceAs (Module (A.obj.obj V) (P.val.obj V))
        change (ModuleCat.extendScalarsId (A.obj.obj V)).hom.app (P.val.obj V)
            (changeOfRingsMap (𝟙 A) P i
              ((1 : A.obj.obj U) ⊗ₜ[A.obj.obj U, ((𝟙 A : A ⟶ A).hom.app U).hom] m)) =
          P.val.map i ((ModuleCat.extendScalarsId (A.obj.obj U)).hom.app
            (P.val.obj U)
              ((1 : A.obj.obj U) ⊗ₜ[A.obj.obj U, ((𝟙 A : A ⟶ A).hom.app U).hom] m))
        rw [show changeOfRingsMap (𝟙 A) P i
              ((1 : A.obj.obj U) ⊗ₜ[A.obj.obj U, ((𝟙 A : A ⟶ A).hom.app U).hom] m) =
            A.obj.map i 1 ⊗ₜ[A.obj.obj V, ((𝟙 A : A ⟶ A).hom.app V).hom] P.val.map i m from
          Classical.choose_spec (exists_changeOfRingsMap (𝟙 A) P i) 1 m]
        rw [map_one, ModuleCat.extendScalarsId_hom_app_one_tmul,
          ModuleCat.extendScalarsId_hom_app_one_tmul])
  let L := PresheafOfModules.sheafification.{r}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A).obj)
  let adj : L ⊣ G := PresheafOfModules.sheafificationAdjunction.{r}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A).obj)
  let a : changeOfRings (𝟙 A) P ≅ P :=
    L.mapIso e ≪≫ (asIso adj.counit).app P
  have ha : (adj.homEquiv _ P) a.hom = e.hom := by
    change (adj.homEquiv _ P) (L.map e.hom ≫ adj.counit.app P) = e.hom
    rw [← Adjunction.homEquiv_counit]
    exact (adj.homEquiv _ P).apply_symm_apply e.hom
  have hp (U : Cᵒᵖ) (m : P.val.obj U) :
      a.hom.val.app U
        (((adj.unit.app (changeOfRingsPresheaf (𝟙 A) P)).app U)
          ((1 : A.obj.obj U) ⊗ₜ[A.obj.obj U, ((𝟙 A : A ⟶ A).hom.app U).hom] m)) = m := by
    rw [Adjunction.homEquiv_unit] at ha
    have h := congrArg (fun z ↦ z.app U
      ((1 : A.obj.obj U) ⊗ₜ[A.obj.obj U, ((𝟙 A : A ⟶ A).hom.app U).hom] m)) ha
    exact h.trans (ModuleCat.extendScalarsId_hom_app_one_tmul (R := A.obj.obj U)
      (P.val.obj U) m)
  refine ⟨a, hp, ?_⟩
  intro a' hp'
  apply Iso.ext
  apply (adj.homEquiv _ P).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  exact (hp' U m).trans (hp U m).symm
end IdentityScalars

-- Keep Kan-extension data abstract after the unit identifications.
attribute [local irreducible] Functor.sheafPullbackConstruction.sheafPullback
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
  AlgebraicGeometry.ProEtale.setPullback
  AlgebraicGeometry.ProEtale.setPullbackAdjunction
  AlgebraicGeometry.ProEtale.setPullbackComp

private theorem setComp_map_units {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z)
    (H : Sheaf (ProEt.topology Z) (Type (u + 1)))
    (Hh : Sheaf (ProEt.topology Y) (Type (u + 1)))
    (Hgh : Sheaf (ProEt.topology X) (Type (u + 1)))
    (eh : (AlgebraicGeometry.ProEtale.setPullback h).obj H ⟶ Hh)
    (eg : (AlgebraicGeometry.ProEtale.setPullback g).obj Hh ⟶ Hgh)
    (V : Z.ProEt) (s : H.obj.obj (op V)) :
    (((AlgebraicGeometry.ProEtale.setPullbackComp g h).hom.app H ≫
      (AlgebraicGeometry.ProEtale.setPullback g).map eh ≫ eg).hom.app
        (op ((proEtaleBaseChange (g ≫ h)).obj V)))
      (((AlgebraicGeometry.ProEtale.setPullbackAdjunction (g ≫ h)).unit.app H).hom.app
        (op V) s) =
    Hgh.obj.map
      ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) g h).hom.app V).op
      (eg.hom.app (op ((proEtaleBaseChange g).obj ((proEtaleBaseChange h).obj V)))
        (((AlgebraicGeometry.ProEtale.setPullbackAdjunction g).unit.app Hh).hom.app
          (op ((proEtaleBaseChange h).obj V))
          (eh.hom.app (op ((proEtaleBaseChange h).obj V))
            (((AlgebraicGeometry.ProEtale.setPullbackAdjunction h).unit.app H).hom.app
              (op V) s)))) := by
  let δ := MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) g h
  let W := (proEtaleBaseChange h).obj V
  let W' := (proEtaleBaseChange g).obj W
  let W'' := (proEtaleBaseChange (g ≫ h)).obj V
  let ηh := (AlgebraicGeometry.ProEtale.setPullbackAdjunction h).unit.app H
  let ηg := (AlgebraicGeometry.ProEtale.setPullbackAdjunction g).unit.app
    ((AlgebraicGeometry.ProEtale.setPullback h).obj H)
  let a := (AlgebraicGeometry.ProEtale.setPullback g).map eh
  have hc := congrArg (fun z ↦ z.hom.app (op V) s)
    ((AlgebraicGeometry.ProEtale.toposFunctorialityInverseImage g h).2.2.2.2.2 H)
  change ((AlgebraicGeometry.ProEtale.setPullbackComp g h).hom.app H).hom.app (op W'')
      (((AlgebraicGeometry.ProEtale.setPullbackAdjunction (g ≫ h)).unit.app H).hom.app
        (op V) s) =
    ((AlgebraicGeometry.ProEtale.setPullback g).obj
      ((AlgebraicGeometry.ProEtale.setPullback h).obj H)).obj.map (δ.hom.app V).op
        (ηg.hom.app (op W) (ηh.hom.app (op V) s)) at hc
  have hn := a.hom.naturality (δ.hom.app V).op
  have hn' := eg.hom.naturality (δ.hom.app V).op
  have hu := (AlgebraicGeometry.ProEtale.setPullbackAdjunction g).unit.naturality eh
  exact (congrArg (fun t ↦ eg.hom.app (op W'') (a.hom.app (op W'') t)) hc).trans
    ((congrArg (eg.hom.app (op W'')) (ConcreteCategory.congr_hom hn _)).trans
      ((ConcreteCategory.congr_hom hn' _).trans
        (congrArg (fun t ↦ Hgh.obj.map (δ.hom.app V).op (eg.hom.app (op W') t))
          (ConcreteCategory.congr_hom
            (congrArg (fun z ↦ z.hom.app (op W)) hu).symm (ηh.hom.app (op V) s)))))

-- Elaborate the semilinear actions on the iterated pullback.
/-- The module compositor is uniquely fixed by the images of original sections,
with the canonical fibre-product associator written explicitly. -/
theorem moduleComp_exists {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z)
    (R : Rings Z) (M : Modules R) :
    ∃! e : (inverse (g ≫ h) R).obj M ≅
        (restrict (ringComp g h R).hom).obj
          ((inverse g (inverseRing h R)).obj ((inverse h R).obj M)),
      ∀ (V : Z.ProEt) (s : M.val.obj (op V)),
        e.hom.val.app (op ((proEtaleBaseChange (g ≫ h)).obj V))
          (inverseSection (g ≫ h) M V s) =
        ((inverse g (inverseRing h R)).obj ((inverse h R).obj M)).val.map
          ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) g h).hom.app V).op
          (inverseSection g ((inverse h R).obj M) ((proEtaleBaseChange h).obj V)
            (inverseSection h M V s)) := by
  let := proEtaleBaseChange_isContinuous (g ≫ h)
  let := proEtaleBaseChange_isContinuous g
  let := proEtaleBaseChange_isContinuous h
  let Fh := inverse h R
  let Fg := inverse g (inverseRing h R)
  let Q := Fg.obj (Fh.obj M)
  let δ := MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) g h
  let ai := AlgebraicGeometry.Scheme.canonicalAdjunction (g ≫ h) R
  let ηh := (AlgebraicGeometry.Scheme.canonicalAdjunction h R).unit.app M
  let ηg := (AlgebraicGeometry.Scheme.canonicalAdjunction g (inverseRing h R)).unit.app (Fh.obj M)
  let M' := (restrict (ringComp g h R).hom).obj Q
  have hr := ringComp_unit g h R
  let j := ηh ≫ (AlgebraicGeometry.Scheme.T h R).map ηg
  let k : M ⟶ (AlgebraicGeometry.Scheme.T (g ≫ h) R).obj M' :=
    { val :=
      { app := fun U ↦ ModuleCat.ofHom
          (X := M.val.obj U)
          (Y := ((AlgebraicGeometry.Scheme.T (g ≫ h) R).obj M').val.obj U)
          { toFun := fun s ↦ Q.val.map (δ.hom.app U.unop).op (j.val.app U s)
            map_add' := by
              intro s t
              exact (congrArg (Q.val.map (δ.hom.app U.unop).op)
                ((j.val.app U).hom.map_add s t)).trans
                  ((Q.val.map (δ.hom.app U.unop).op).hom.map_add _ _)
            map_smul' := by
              intro r s
              have hj := (j.val.app U).hom.map_smul r s
              change j.val.app U (r • s) =
                (((proEtaleSheafAdjunction g CommRingCat.{u + 1}).unit.app
                    (inverseRing h R)).hom.app ((proEtaleBaseChange h).op.obj U)
                  (((proEtaleSheafAdjunction h CommRingCat.{u + 1}).unit.app R).hom.app
                    U r)) • (show Q.val.obj
                  ((proEtaleBaseChange g).op.obj ((proEtaleBaseChange h).op.obj U)) from
                    j.val.app U s) at hj
              change Q.val.map (δ.hom.app U.unop).op (j.val.app U (r • s)) =
                (ringComp g h R).hom.hom.app ((proEtaleBaseChange (g ≫ h)).op.obj U)
                  (((proEtaleSheafAdjunction (g ≫ h) CommRingCat.{u + 1}).unit.app R).hom.app
                    U r) • (show Q.val.obj ((proEtaleBaseChange (g ≫ h)).op.obj U) from
                      Q.val.map (δ.hom.app U.unop).op (j.val.app U s))
              exact (congrArg (Q.val.map (δ.hom.app U.unop).op) hj).trans
                ((Q.val.map_smul (δ.hom.app U.unop).op _ _).trans
                  (congrArg (fun t ↦ t •
                    (show Q.val.obj ((proEtaleBaseChange (g ≫ h)).op.obj U) from
                      Q.val.map (δ.hom.app U.unop).op (j.val.app U s)))
                    (hr U r).symm)) }
        naturality := by
          intro U V i
          ext s
          have hj := PresheafOfModules.naturality_apply j.val i s
          change j.val.app V (M.val.map i s) =
            Q.val.map ((proEtaleBaseChange h ⋙ proEtaleBaseChange g).op.map i)
              (j.val.app U s) at hj
          change Q.val.map (δ.hom.app V.unop).op (j.val.app V (M.val.map i s)) =
            Q.val.map ((proEtaleBaseChange (g ≫ h)).op.map i)
              (Q.val.map (δ.hom.app U.unop).op (j.val.app U s))
          exact (congrArg (Q.val.map (δ.hom.app V.unop).op) hj).trans
            ((Q.val.map_comp_apply
              ((proEtaleBaseChange h ⋙ proEtaleBaseChange g).op.map i)
                (δ.hom.app V.unop).op (j.val.app U s)).symm.trans
              ((congrArg (fun l : (proEtaleBaseChange (g ≫ h)).obj V.unop ⟶
                  (proEtaleBaseChange h ⋙ proEtaleBaseChange g).obj U.unop ↦
                    Q.val.map l.op (j.val.app U s)) (δ.hom.naturality i.unop).symm).trans
                (Q.val.map_comp_apply (δ.hom.app U.unop).op
                  ((proEtaleBaseChange (g ≫ h)).op.map i) (j.val.app U s)))) } }
  let p := (ai.homEquiv M M').symm k
  have hp (V : Z.ProEt) (s : M.val.obj (op V)) :
      p.val.app (op ((proEtaleBaseChange (g ≫ h)).obj V))
        (inverseSection (g ≫ h) (R := R) M V s) =
      Q.val.map (δ.hom.app V).op
        (inverseSection g (R := inverseRing h R) (Fh.obj M) ((proEtaleBaseChange h).obj V)
          (inverseSection h (R := R) M V s)) := by
    have hu := (ai.homEquiv M M').apply_symm_apply k
    rw [Adjunction.homEquiv_unit] at hu
    have hv := congrArg (fun z ↦ z.val.app (op V) s) hu
    change p.val.app (op ((proEtaleBaseChange (g ≫ h)).obj V))
      ((ai.unit.app M).val.app (op V) s) = k.val.app (op V) s at hv
    have hk : k.val.app (op V) s = Q.val.map (δ.hom.app V).op
        (ηg.val.app ((proEtaleBaseChange h).op.obj (op V))
          (ηh.val.app (op V) s)) := rfl
    have hgh := inverseSection_unit (g ≫ h) R M (op V) s
    have hv' := (congrArg (p.val.app (op ((proEtaleBaseChange (g ≫ h)).obj V)))
      hgh).symm.trans (hv.trans hk)
    exact hv'.trans (congrArg (Q.val.map (δ.hom.app V).op)
      ((inverseSection_unit g (inverseRing h R) (Fh.obj M)
        (op ((proEtaleBaseChange h).obj V)) (ηh.val.app (op V) s)).trans
          (congrArg (inverseSection g (R := inverseRing h R) (Fh.obj M)
            ((proEtaleBaseChange h).obj V))
            (inverseSection_unit h R M (op V) s))))
  clear_value p
  let U := toSheaf ((sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (inverseRing (g ≫ h) R)) ⋙
      sheafCompose (ProEt.topology X) (CategoryTheory.forget AddCommGrpCat.{u + 1})
  let b : (AlgebraicGeometry.ProEtale.setPullback (g ≫ h)).obj
      (moduleSets (R := R) M) ≅ U.obj M' :=
    (AlgebraicGeometry.ProEtale.setPullbackComp g h).app (moduleSets (R := R) M) ≪≫
    (AlgebraicGeometry.ProEtale.setPullback g).mapIso (moduleSetsIdentification h (R := R) M) ≪≫
      moduleSetsIdentification g (R := inverseRing h R) (Fh.obj M)
  have hb (V : Z.ProEt) (s : M.val.obj (op V)) :
      b.hom.hom.app (op ((proEtaleBaseChange (g ≫ h)).obj V))
        (((AlgebraicGeometry.ProEtale.setPullbackAdjunction (g ≫ h)).unit.app
          (moduleSets (R := R) M)).hom.app (op V) s) =
      Q.val.map (δ.hom.app V).op
        (inverseSection g (R := inverseRing h R) (Fh.obj M) ((proEtaleBaseChange h).obj V)
          (inverseSection h (R := R) M V s)) := by
    have hb' := setComp_map_units g h (moduleSets (R := R) M)
      (moduleSets (R := inverseRing h R) (Fh.obj M))
      (moduleSets (R := inverseRing g (inverseRing h R)) Q)
        (moduleSetsIdentification h (R := R) M).hom
        (moduleSetsIdentification g (R := inverseRing h R) (Fh.obj M)).hom V s
    have hM := (Classical.choose_spec (moduleSetsIdentification_exists h (R := R) M)).1 V s
    have hN := (Classical.choose_spec
      (moduleSetsIdentification_exists g (R := inverseRing h R) (Fh.obj M))).1
      ((proEtaleBaseChange h).obj V) (inverseSection h (R := R) M V s)
    exact hb'.trans (congrArg (Q.val.map (δ.hom.app V).op)
      ((congrArg (fun t ↦ (moduleSetsIdentification g (R := inverseRing h R) (Fh.obj M)).hom.hom.app
        (op ((proEtaleBaseChange g).obj ((proEtaleBaseChange h).obj V)))
          (((AlgebraicGeometry.ProEtale.setPullbackAdjunction g).unit.app
            (moduleSets (R := inverseRing h R) (Fh.obj M))).hom.app
              (op ((proEtaleBaseChange h).obj V)) t)) hM).trans
              hN))
  clear_value b
  have he : (moduleSetsIdentification (g ≫ h) (R := R) M).hom ≫ U.map p = b.hom := by
    apply ((AlgebraicGeometry.ProEtale.setPullbackAdjunction (g ≫ h)).homEquiv
      (moduleSets (R := R) M)
      (U.obj M')).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    apply ConcreteCategory.hom_ext
    intro s
    have hM := (Classical.choose_spec
      (moduleSetsIdentification_exists (g ≫ h) (R := R) M)).1 V.unop s
    exact (congrArg (p.val.app ((proEtaleBaseChange (g ≫ h)).op.obj V)) hM).trans
      ((hp V.unop s).trans (hb V.unop s).symm)
  have : IsIso (U.map p) := by
    have hh : U.map p = (moduleSetsIdentification (g ≫ h) (R := R) M).inv ≫ b.hom := by
      rw [← he]
      simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    rw [hh]
    exact inferInstanceAs (IsIso (((moduleSetsIdentification (g ≫ h) (R := R) M).symm ≪≫ b).hom))
  have : IsIso p := isIso_of_reflects_iso p U
  refine ⟨asIso p, hp, ?_⟩
  intro e he'
  apply Iso.ext
  apply inverseModule_hom_ext (g ≫ h) (R := R) (M := M)
  intro V s
  exact (he' V s).trans (hp V s).symm

/-- The canonical semilinear module compositor, from its unique unit characterization. -/
noncomputable def moduleComp {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z)
    (R : Rings Z) (M : Modules R) :
    (inverse (g ≫ h) R).obj M ≅
      (restrict (ringComp g h R).hom).obj
        ((inverse g (inverseRing h R)).obj ((inverse h R).obj M)) :=
  Classical.choose (moduleComp_exists g h R M)

/-- The canonical ring identity comparison, from the inverse-image adjunction. -/
noncomputable def ringId {X : Scheme.{u}} (R : Rings X) : inverseRing (𝟙 X) R ≅ R :=
  ((conjugateIsoEquiv Adjunction.id
    (proEtaleSheafAdjunction (𝟙 X) CommRingCat.{u + 1})).symm
      (AlgebraicGeometry.ProEtale.lowerStarId CommRingCat.{u + 1} X).symm).app R

private theorem ringId_unit {X : Scheme.{u}} (R : Rings X)
    (U : X.ProEtᵒᵖ) (r : R.obj.obj U) :
    (ringId R).hom.hom.app ((proEtaleBaseChange (𝟙 X)).op.obj U)
      (((proEtaleSheafAdjunction (𝟙 X) CommRingCat.{u + 1}).unit.app R).hom.app U r) =
        R.obj.map ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).hom.app U.unop).op r := by
  have h := (unit_conjugateEquiv_symm Adjunction.id
    (proEtaleSheafAdjunction (𝟙 X) CommRingCat.{u + 1})
    (AlgebraicGeometry.ProEtale.lowerStarId CommRingCat.{u + 1} X).inv R).symm
  exact congrArg (fun z ↦ z.hom.app U r) h

-- Use the unit equation of the identity ring comparison.
attribute [local irreducible] ringId

-- Elaborate the identity scalar transport through the adjunction unit.
/-- The module identity comparison is uniquely normalized by the identity unit. -/
theorem moduleId_exists {X : Scheme.{u}} (R : Rings X) (M : Modules R) :
    ∃! e : (inverse (𝟙 X) R).obj M ≅ (restrict (ringId R).hom).obj M,
      ∀ (V : X.ProEt) (s : M.val.obj (op V)),
        e.hom.val.app (op ((proEtaleBaseChange (𝟙 X)).obj V))
          (inverseSection (𝟙 X) M V s) =
        M.val.map ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).hom.app V).op s := by
  let ai := AlgebraicGeometry.Scheme.canonicalAdjunction (𝟙 X) R
  let δ := MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X
  let M' := (restrict (ringId R).hom).obj M
  have hr (U : X.ProEtᵒᵖ) (r : R.obj.obj U) :
      (ringId R).hom.hom.app ((proEtaleBaseChange (𝟙 X)).op.obj U)
        (((proEtaleSheafAdjunction (𝟙 X) CommRingCat.{u + 1}).unit.app R).hom.app U r) =
          R.obj.map (δ.hom.app U.unop).op r := by
    exact ringId_unit R U r
  let k : M ⟶ (AlgebraicGeometry.Scheme.T (𝟙 X) R).obj M' :=
    { val :=
      { app := fun U ↦ ModuleCat.ofHom
          (X := M.val.obj U)
          (Y := ((AlgebraicGeometry.Scheme.T (𝟙 X) R).obj M').val.obj U)
          { toFun := M.val.map (δ.hom.app U.unop).op
            map_add' := (M.val.map (δ.hom.app U.unop).op).hom.map_add
            map_smul' := by
              intro r m
              change M.val.map (δ.hom.app U.unop).op (r • m) =
                (ringId R).hom.hom.app ((proEtaleBaseChange (𝟙 X)).op.obj U)
                  (((proEtaleSheafAdjunction (𝟙 X) CommRingCat.{u + 1}).unit.app R).hom.app U r) •
                    (show M.val.obj ((proEtaleBaseChange (𝟙 X)).op.obj U) from
                      M.val.map (δ.hom.app U.unop).op m)
              rw [hr]
              exact M.val.map_smul (δ.hom.app U.unop).op r m }
        naturality := by
          intro U V i
          ext m
          change M.val.map (δ.hom.app V.unop).op (M.val.map i m) =
            M.val.map ((proEtaleBaseChange (𝟙 X)).op.map i)
              (M.val.map (δ.hom.app U.unop).op m)
          exact (M.val.map_comp_apply i (δ.hom.app V.unop).op m).symm.trans
            ((congrArg (fun j : (proEtaleBaseChange (𝟙 X)).obj V.unop ⟶ U.unop ↦
              M.val.map j.op m) (δ.hom.naturality i.unop).symm).trans
              (M.val.map_comp_apply (δ.hom.app U.unop).op
                ((proEtaleBaseChange (𝟙 X)).op.map i) m)) } }
  let p := (ai.homEquiv M M').symm k
  have hp (V : X.ProEt) (s : M.val.obj (op V)) :
      p.val.app (op ((proEtaleBaseChange (𝟙 X)).obj V))
        (inverseSection (𝟙 X) M V s) = M.val.map (δ.hom.app V).op s := by
    have h := (ai.homEquiv M M').apply_symm_apply k
    rw [Adjunction.homEquiv_unit] at h
    have hh := congrArg (fun z ↦ z.val.app (op V) s) h
    change p.val.app (op ((proEtaleBaseChange (𝟙 X)).obj V))
      ((ai.unit.app M).val.app (op V) s) = M.val.map (δ.hom.app V).op s at hh
    rw [inverseSection_unit] at hh
    exact hh
  clear_value p
  let U := toSheaf ((sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (inverseRing (𝟙 X) R)) ⋙
      sheafCompose (ProEt.topology X) (CategoryTheory.forget AddCommGrpCat.{u + 1})
  let b : AlgebraicGeometry.ProEtale.setPullback (𝟙 X) ≅
      𝟭 (Sheaf (ProEt.topology X) (Type (u + 1))) :=
    (conjugateIsoEquiv Adjunction.id
      (AlgebraicGeometry.ProEtale.setPullbackAdjunction (𝟙 X))).symm
        (AlgebraicGeometry.ProEtale.lowerStarId (Type (u + 1)) X).symm
  have hb (V : X.ProEt) (s : M.val.obj (op V)) :
      (b.hom.app (moduleSets (R := R) M)).hom.app
        (op ((proEtaleBaseChange (𝟙 X)).obj V))
          (((AlgebraicGeometry.ProEtale.setPullbackAdjunction (𝟙 X)).unit.app
            (moduleSets (R := R) M)).hom.app (op V) s) =
      M.val.map (δ.hom.app V).op s := by
    have h := (unit_conjugateEquiv_symm Adjunction.id
      (AlgebraicGeometry.ProEtale.setPullbackAdjunction (𝟙 X))
      (AlgebraicGeometry.ProEtale.lowerStarId (Type (u + 1)) X).inv
        (moduleSets (R := R) M)).symm
    exact congrArg (fun z ↦ z.hom.app (op V) s) h
  clear_value b
  have he : (moduleSetsIdentification (𝟙 X) (R := R) M).hom ≫ U.map p =
      b.hom.app (moduleSets (R := R) M) := by
    apply ((AlgebraicGeometry.ProEtale.setPullbackAdjunction (𝟙 X)).homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    ext V s
    have hM := (Classical.choose_spec (moduleSetsIdentification_exists (𝟙 X) (R := R) M)).1 V.unop s
    exact (congrArg (p.val.app ((proEtaleBaseChange (𝟙 X)).op.obj V)) hM).trans
      ((hp V.unop s).trans (hb V.unop s).symm)
  have : IsIso (U.map p) := by
    have hh : U.map p = (moduleSetsIdentification (𝟙 X) (R := R) M).inv ≫
        b.hom.app (moduleSets (R := R) M) := by
      rw [← he]
      simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    rw [hh]
    exact inferInstanceAs (IsIso (((moduleSetsIdentification (𝟙 X) (R := R) M).symm ≪≫
      b.app (moduleSets (R := R) M)).hom))
  have : IsIso p := isIso_of_reflects_iso p U
  refine ⟨asIso p, hp, ?_⟩
  intro e he'
  apply Iso.ext
  apply inverseModule_hom_ext (𝟙 X) (R := R) (M := M)
  intro V s
  exact (he' V s).trans (hp V s).symm

/-- The canonical module identity comparison, from its unique unit characterization. -/
noncomputable def moduleId {X : Scheme.{u}} (R : Rings X) (M : Modules R) :
    (inverse (𝟙 X) R).obj M ≅ (restrict (ringId R).hom).obj M :=
  Classical.choose (moduleId_exists R M)

/-- Forget a ring morphism to its actual underlying sheaf map. -/
noncomputable abbrev ringMapSets {X : Scheme.{u}} {R S : Rings X} (a : R ⟶ S) :=
  (sheafCompose (ProEt.topology X) (CategoryTheory.forget CommRingCat.{u + 1})).map a

private theorem pure_restriction {X : Scheme.{u}} {R : Rings X}
    (M N : Modules R) {U V : X.ProEtᵒᵖ} (i : U ⟶ V)
    (x : M.val.obj U) (y : N.val.obj U) :
    (tensor M N).val.map i (pure M N U.unop x y) =
      pure M N V.unop (M.val.map i x) (N.val.map i y) := by
  let adj := PresheafOfModules.sheafificationAdjunction.{u + 1}
    (𝟙 ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj)
  exact (PresheafOfModules.naturality_apply
    (adj.unit.app (siteTensorPresheaf M.val N.val)) i (x ⊗ₜ[R.obj.obj U] y)).symm

private theorem moduleId_sections {X : Scheme.{u}} (R : Rings X)
    (M : Modules R) (V : X.ProEt) (x : M.val.obj (op V)) :
    (moduleId R M).hom.val.app (op ((proEtaleBaseChange (𝟙 X)).obj V))
        (inverseSection (𝟙 X) M V x) =
      M.val.map ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).hom.app V).op x :=
  (Classical.choose_spec (moduleId_exists R M)).1 V x

private theorem comparison_identity {X : Scheme.{u}} (R : Rings X)
    (M N : Modules R) :
    comparison (𝟙 X) R M N ≫ tensorMap (moduleId R M).hom (moduleId R N).hom ≫
        coefficientQuotient (ringId R).hom M N = (moduleId R (tensor M N)).hom := by
  apply inverseTensor_hom_ext (𝟙 X) (R := R) (M := M) (N := N)
  intro V x y
  change (coefficientQuotient (ringId R).hom M N).val.app
      (op ((proEtaleBaseChange (𝟙 X)).obj V))
      ((tensorMap (moduleId R M).hom (moduleId R N).hom).val.app
        (op ((proEtaleBaseChange (𝟙 X)).obj V))
        ((comparison (𝟙 X) R M N).val.app
          (op ((proEtaleBaseChange (𝟙 X)).obj V))
          (inverseSection (𝟙 X) (tensor M N) V (pure M N V x y)))) =
    (moduleId R (tensor M N)).hom.val.app (op ((proEtaleBaseChange (𝟙 X)).obj V))
      (inverseSection (𝟙 X) (tensor M N) V (pure M N V x y))
  rw [comparison_pure, tensorMap_pure, coefficientQuotient_pure]
  simp only [moduleId_sections]
  exact (pure_restriction M N
    ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).hom.app V).op x y).symm

private theorem setIdentity_unit_isIso {X : Scheme.{u}}
    (H : Sheaf (ProEt.topology X) (Type (u + 1))) :
    IsIso ((AlgebraicGeometry.ProEtale.setPullbackAdjunction (𝟙 X)).unit.app H) := by
  let b : AlgebraicGeometry.ProEtale.setPullback (𝟙 X) ≅
      𝟭 (Sheaf (ProEt.topology X) (Type (u + 1))) :=
    (conjugateIsoEquiv Adjunction.id
      (AlgebraicGeometry.ProEtale.setPullbackAdjunction (𝟙 X))).symm
        (AlgebraicGeometry.ProEtale.lowerStarId (Type (u + 1)) X).symm
  have : (AlgebraicGeometry.ProEtale.setPullback (𝟙 X)).IsEquivalence :=
    Functor.isEquivalence_of_iso b.symm
  have := (AlgebraicGeometry.ProEtale.setPullbackAdjunction (𝟙 X)).unit_isIso_of_L_fully_faithful
  infer_instance

private theorem ringSets_composition {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z)
    (R : Rings Z) :
    (AlgebraicGeometry.ProEtale.setPullbackComp g h).hom.app (ringSets R) ≫
        (AlgebraicGeometry.ProEtale.setPullback g).map (ringSetsIdentification h R).hom ≫
        (ringSetsIdentification g (inverseRing h R)).hom =
      (ringSetsIdentification (g ≫ h) R).hom ≫ ringMapSets (ringComp g h R).hom := by
  apply ((AlgebraicGeometry.ProEtale.setPullbackAdjunction (g ≫ h)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  ext V r
  let W := (proEtaleBaseChange h).obj V.unop
  let δ := MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) g h
  let A := inverseRing g (inverseRing h R)
  have hb := setComp_map_units g h (ringSets R) (ringSets (inverseRing h R))
    (ringSets A) (ringSetsIdentification h R).hom
      (ringSetsIdentification g (inverseRing h R)).hom V.unop r
  have hR := (Classical.choose_spec (ringSetsIdentification_exists h R)).1 V.unop r
  have hR' := (Classical.choose_spec
    (ringSetsIdentification_exists g (inverseRing h R))).1 W
      (((proEtaleSheafAdjunction h CommRingCat.{u + 1}).unit.app R).hom.app V r)
  have hR0 := (Classical.choose_spec
    (ringSetsIdentification_exists (g ≫ h) R)).1 V.unop r
  have hr := ringComp_unit g h R V r
  exact hb.trans ((congrArg (A.obj.map (δ.hom.app V.unop).op)
    ((congrArg (fun t ↦ (ringSetsIdentification g (inverseRing h R)).hom.hom.app
      (op ((proEtaleBaseChange g).obj W))
      (((AlgebraicGeometry.ProEtale.setPullbackAdjunction g).unit.app
        (ringSets (inverseRing h R))).hom.app (op W) t)) hR).trans hR')).trans
          (hr.symm.trans (congrArg
            ((ringComp g h R).hom.hom.app ((proEtaleBaseChange (g ≫ h)).op.obj V))
              hR0).symm))

private theorem moduleSets_composition {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z)
    (R : Rings Z) (P : Modules R) :
    (AlgebraicGeometry.ProEtale.setPullbackComp g h).hom.app (moduleSets P) ≫
        (AlgebraicGeometry.ProEtale.setPullback g).map (moduleSetsIdentification h P).hom ≫
        (moduleSetsIdentification g ((inverse h R).obj P)).hom =
      (moduleSetsIdentification (g ≫ h) P).hom ≫
        moduleMapSets (moduleComp g h R P).hom := by
  apply ((AlgebraicGeometry.ProEtale.setPullbackAdjunction (g ≫ h)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  ext V s
  let W := (proEtaleBaseChange h).obj V.unop
  let P' := (inverse h R).obj P
  let Q := (inverse g (inverseRing h R)).obj P'
  let δ := MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) g h
  have hb := setComp_map_units g h (moduleSets P) (moduleSets P') (moduleSets Q)
    (moduleSetsIdentification h P).hom (moduleSetsIdentification g P').hom V.unop s
  have hP := (Classical.choose_spec (moduleSetsIdentification_exists h P)).1 V.unop s
  have hP' := (Classical.choose_spec (moduleSetsIdentification_exists g P')).1 W
    (inverseSection h P V.unop s)
  have hP0 := (Classical.choose_spec
    (moduleSetsIdentification_exists (g ≫ h) P)).1 V.unop s
  have hC := (Classical.choose_spec (moduleComp_exists g h R P)).1 V.unop s
  exact hb.trans ((congrArg (Q.val.map (δ.hom.app V.unop).op)
    ((congrArg (fun t ↦ (moduleSetsIdentification g P').hom.hom.app
      (op ((proEtaleBaseChange g).obj W))
      (((AlgebraicGeometry.ProEtale.setPullbackAdjunction g).unit.app
        (moduleSets P')).hom.app (op W) t)) hP).trans hP')).trans
          (hC.symm.trans (congrArg
            ((moduleComp g h R P).hom.val.app ((proEtaleBaseChange (g ≫ h)).op.obj V))
              hP0).symm))

private theorem moduleComp_sections {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z)
    (R : Rings Z) (P : Modules R) (V : Z.ProEt) (x : P.val.obj (op V)) :
    (moduleComp g h R P).hom.val.app (op ((proEtaleBaseChange (g ≫ h)).obj V))
        (inverseSection (g ≫ h) P V x) =
      ((inverse g (inverseRing h R)).obj ((inverse h R).obj P)).val.map
        ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) g h).hom.app V).op
        (inverseSection g ((inverse h R).obj P) ((proEtaleBaseChange h).obj V)
          (inverseSection h P V x)) :=
  (Classical.choose_spec (moduleComp_exists g h R P)).1 V x

private theorem comparison_composition {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z)
    (R : Rings Z) (M N : Modules R) :
    (moduleComp g h R (tensor (R := R) M N)).hom ≫
        (restrict (ringComp g h R).hom).map
          ((inverse g (inverseRing h R)).map (comparison h R M N)) ≫
        (restrict (ringComp g h R).hom).map
          (comparison g (inverseRing h R) ((inverse h R).obj M) ((inverse h R).obj N)) =
      comparison (g ≫ h) R M N ≫
        tensorMap (R := inverseRing (g ≫ h) R) (moduleComp g h R M).hom (moduleComp g h R N).hom ≫
        coefficientQuotient (ringComp g h R).hom
          ((inverse g (inverseRing h R)).obj ((inverse h R).obj M))
          ((inverse g (inverseRing h R)).obj ((inverse h R).obj N)) := by
  apply inverseTensor_hom_ext (g ≫ h) (R := R) (M := M) (N := N)
  intro V x y
  let Rh := inverseRing h R
  let Rgh := inverseRing (g ≫ h) R
  let Ri := inverseRing g Rh
  let Fh := inverse h R
  let Fg := inverse g Rh
  let M0 := Fh.obj M
  let N0 := Fh.obj N
  let M1 := Fg.obj M0
  let N1 := Fg.obj N0
  let W := (proEtaleBaseChange h).obj V
  let W' := (proEtaleBaseChange g).obj W
  let W'' := (proEtaleBaseChange (g ≫ h)).obj V
  let δ := MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) g h
  let i := (δ.hom.app V).op
  let mh := inverseSection h (R := R) M V x
  let nh := inverseSection h (R := R) N V y
  let a := comparison h R M N
  let b := comparison g Rh M0 N0
  let c := Fg.map a
  let t := inverseSection h (R := R) (tensor M N) V (pure M N V x y)
  let u := inverseSection g (R := Rh) (Fh.obj (tensor M N)) W t
  let mg := inverseSection g (R := Rh) M0 W mh
  let ng := inverseSection g (R := Rh) N0 W nh
  let v := inverseSection (g ≫ h) (R := R) (tensor M N) V (pure M N V x y)
  let eT := (moduleComp g h R (tensor M N)).hom
  let eM := (moduleComp g h R M).hom
  let eN := (moduleComp g h R N).hom
  let q := coefficientQuotient (ringComp g h R).hom M1 N1
  let d := tensorMap (R := Rgh) eM eN
  let hT := comparison (g ≫ h) R M N
  change b.val.app (op W'') (c.val.app (op W'') (eT.val.app (op W'') v)) =
    q.val.app (op W'') (d.val.app (op W'') (hT.val.app (op W'') v))
  have hc := inverseSection_map g (R := Rh) a W t
  have ha := comparison_pure h R M N V x y
  have hb := comparison_pure g Rh M0 N0 W mh nh
  have hl : b.val.app (op W'') (c.val.app (op W'') (eT.val.app (op W'') v)) =
      (tensor (R := Ri) M1 N1).val.map i (pure (R := Ri) M1 N1 W' mg ng) := by
    calc
      b.val.app (op W'') (c.val.app (op W'') (eT.val.app (op W'') v)) =
          b.val.app (op W'') (c.val.app (op W'') ((Fg.obj (Fh.obj (tensor M N))).val.map
            i u)) :=
        congrArg (fun z ↦ b.val.app (op W'') (c.val.app (op W'') z))
          (moduleComp_sections g h R (tensor M N) V (pure M N V x y))
      _ = b.val.app (op W'') ((Fg.obj (tensor (R := Rh) M0 N0)).val.map i
          (c.val.app (op W') u)) :=
        congrArg (b.val.app (op W''))
          (PresheafOfModules.naturality_apply c.val i u)
      _ = (tensor (R := Ri) M1 N1).val.map i
          (b.val.app (op W') (c.val.app (op W') u)) :=
        PresheafOfModules.naturality_apply b.val i (c.val.app (op W') u)
      _ = (tensor (R := Ri) M1 N1).val.map i
          (b.val.app (op W')
            (inverseSection g (R := Rh) (tensor (R := Rh) M0 N0) W
              (a.val.app (op W) t))) :=
        congrArg (fun z ↦ (tensor (R := Ri) M1 N1).val.map i (b.val.app (op W') z)) hc
      _ = (tensor (R := Ri) M1 N1).val.map i
          (b.val.app (op W')
            (inverseSection g (R := Rh) (tensor (R := Rh) M0 N0) W
              (pure (R := Rh) M0 N0 W mh nh))) :=
        congrArg (fun z ↦ (tensor (R := Ri) M1 N1).val.map i
          (b.val.app (op W') (inverseSection g (R := Rh)
            (tensor (R := Rh) M0 N0) W z))) ha
      _ = (tensor (R := Ri) M1 N1).val.map i
          (pure (R := Ri) M1 N1 W' mg ng) :=
        congrArg ((tensor (R := Ri) M1 N1).val.map i) hb
  have hr : q.val.app (op W'') (d.val.app (op W'') (hT.val.app (op W'') v)) =
      pure (R := Ri) M1 N1 W'' (M1.val.map i mg) (N1.val.map i ng) := by
    let xm := inverseSection (g ≫ h) (R := R) M V x
    let yn := inverseSection (g ≫ h) (R := R) N V y
    calc
      q.val.app (op W'') (d.val.app (op W'') (hT.val.app (op W'') v)) =
          q.val.app (op W'') (d.val.app (op W'')
            (pure (R := Rgh) ((inverse (g ≫ h) R).obj M)
              ((inverse (g ≫ h) R).obj N) W'' xm yn)) :=
        congrArg (fun z ↦ q.val.app (op W'') (d.val.app (op W'') z))
          (comparison_pure (g ≫ h) R M N V x y)
      _ = q.val.app (op W'')
          (pure (R := Rgh) ((restrict (ringComp g h R).hom).obj M1)
            ((restrict (ringComp g h R).hom).obj N1) W''
              (eM.val.app (op W'') xm) (eN.val.app (op W'') yn)) :=
        congrArg (q.val.app (op W''))
          (tensorMap_pure (R := Rgh) eM eN W'' xm yn)
      _ = pure (R := Ri) M1 N1 W'' (eM.val.app (op W'') xm)
          (eN.val.app (op W'') yn) :=
        coefficientQuotient_pure (ringComp g h R).hom M1 N1 W''
          (eM.val.app (op W'') xm) (eN.val.app (op W'') yn)
      _ = pure (R := Ri) M1 N1 W'' (M1.val.map i mg) (N1.val.map i ng) :=
        congrArg₂ (pure (R := Ri) M1 N1 W'')
          (moduleComp_sections g h R M V x) (moduleComp_sections g h R N V y)
  exact hl.trans ((pure_restriction (R := Ri) M1 N1 i mg ng).trans hr.symm)

section AlgebraicLift
universe v w

private theorem inverseImage_map_ext
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {T : Sheaf (ProEt.topology Y) (Type (u + 1))}
    {H : Sheaf (ProEt.topology X) (Type (u + 1))}
    (a b : (AlgebraicGeometry.ProEtale.setPullback f).obj T ⟶ H)
    (h : ∀ (U : Y.ProEtᵒᵖ) (x : T.obj.obj U),
      a.hom.app ((proEtaleBaseChange f).op.obj U)
          (((AlgebraicGeometry.ProEtale.setPullbackAdjunction f).unit.app T).hom.app U x) =
      b.hom.app ((proEtaleBaseChange f).op.obj U)
          (((AlgebraicGeometry.ProEtale.setPullbackAdjunction f).unit.app T).hom.app U x)) :
    a = b := by
  apply ((AlgebraicGeometry.ProEtale.setPullbackAdjunction f).homEquiv T H).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  ext U x
  exact h U x

private def binaryMap
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (X Y Z : Sheaf J (Type w))
    (op : ∀ U : Cᵒᵖ, X.obj.obj U → Y.obj.obj U → Z.obj.obj U)
    (hn : ∀ {U V : Cᵒᵖ} (i : U ⟶ V) x y,
      op V (X.obj.map i x) (Y.obj.map i y) = Z.obj.map i (op U x y))
    {T : Sheaf J (Type w)} (a : T ⟶ X) (b : T ⟶ Y) : T ⟶ Z :=
  ⟨{ app := fun U ↦ ↾fun x ↦ op U (a.hom.app U x) (b.hom.app U x)
     naturality := by
       intro U V i
       ext x
       change op V (a.hom.app V (T.obj.map i x)) (b.hom.app V (T.obj.map i x)) = _
       have ha := congrArg (fun q ↦ q x) (a.hom.naturality i)
       have hb := congrArg (fun q ↦ q x) (b.hom.naturality i)
       change a.hom.app V (T.obj.map i x) = X.obj.map i (a.hom.app U x) at ha
       change b.hom.app V (T.obj.map i x) = Y.obj.map i (b.hom.app U x) at hb
       rw [ha, hb]
       exact hn i _ _ }⟩

private theorem transport_binary
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A B C : Sheaf (ProEt.topology Y) (Type (u + 1))}
    {A' B' C' : Sheaf (ProEt.topology X) (Type (u + 1))}
    (eA : (AlgebraicGeometry.ProEtale.setPullback f).obj A ≅ A')
    (eB : (AlgebraicGeometry.ProEtale.setPullback f).obj B ≅ B')
    (eC : (AlgebraicGeometry.ProEtale.setPullback f).obj C ≅ C')
    (op : ∀ U : Y.ProEtᵒᵖ, A.obj.obj U → B.obj.obj U → C.obj.obj U)
    (op' : ∀ V : X.ProEtᵒᵖ, A'.obj.obj V → B'.obj.obj V → C'.obj.obj V)
    (hn : ∀ {U V : X.ProEtᵒᵖ} (i : U ⟶ V) x y,
      op' V (A'.obj.map i x) (B'.obj.map i y) = C'.obj.map i (op' U x y))
    (hu : ∀ (U : Y.ProEtᵒᵖ) x y,
      eC.hom.hom.app ((proEtaleBaseChange f).op.obj U)
          (((AlgebraicGeometry.ProEtale.setPullbackAdjunction f).unit.app C).hom.app U
            (op U x y)) =
      op' ((proEtaleBaseChange f).op.obj U)
        (eA.hom.hom.app ((proEtaleBaseChange f).op.obj U)
          (((AlgebraicGeometry.ProEtale.setPullbackAdjunction f).unit.app A).hom.app U x))
        (eB.hom.hom.app ((proEtaleBaseChange f).op.obj U)
          (((AlgebraicGeometry.ProEtale.setPullbackAdjunction f).unit.app B).hom.app U y)))
    (T : Sheaf (ProEt.topology Y) (Type (u + 1))) (a : T ⟶ A) (b : T ⟶ B) (t : T ⟶ C)
    (ht : ∀ U x, t.hom.app U x = op U (a.hom.app U x) (b.hom.app U x)) :
    ∀ V x,
      eC.hom.hom.app V (((AlgebraicGeometry.ProEtale.setPullback f).map t).hom.app V x) =
      op' V
        (eA.hom.hom.app V (((AlgebraicGeometry.ProEtale.setPullback f).map a).hom.app V x))
        (eB.hom.hom.app V (((AlgebraicGeometry.ProEtale.setPullback f).map b).hom.app V x)) := by
  let L := AlgebraicGeometry.ProEtale.setPullback f
  let eta := (AlgebraicGeometry.ProEtale.setPullbackAdjunction f).unit
  have hh : L.map t ≫ eC.hom =
      binaryMap A' B' C' op' hn (L.map a ≫ eA.hom) (L.map b ≫ eB.hom) := by
    apply inverseImage_map_ext f
    intro U x
    have ha := congrArg (fun q ↦ q.hom.app U x) (eta.naturality a)
    have hb := congrArg (fun q ↦ q.hom.app U x) (eta.naturality b)
    have hc := congrArg (fun q ↦ q.hom.app U x) (eta.naturality t)
    change eC.hom.hom.app _ ((L.map t).hom.app _ (eta.app T |>.hom.app U x)) =
      op' _ (eA.hom.hom.app _ ((L.map a).hom.app _ (eta.app T |>.hom.app U x)))
        (eB.hom.hom.app _ ((L.map b).hom.app _ (eta.app T |>.hom.app U x)))
    change (eta.app A).hom.app U (a.hom.app U x) =
      (L.map a).hom.app _ ((eta.app T).hom.app U x) at ha
    change (eta.app B).hom.app U (b.hom.app U x) =
      (L.map b).hom.app _ ((eta.app T).hom.app U x) at hb
    change (eta.app C).hom.app U (t.hom.app U x) =
      (L.map t).hom.app _ ((eta.app T).hom.app U x) at hc
    rw [← ha, ← hb, ← hc, ht]
    exact hu U _ _
  intro V x
  exact congrArg (fun q ↦ q.hom.app V x) hh

private theorem inverseSection_add {X Y : Scheme.{u}} (f : X ⟶ Y)
    {R : Rings Y} (M : Modules R) (V : Y.ProEt) (m n : M.val.obj (op V)) :
    inverseSection f (R := R) M V (m + n) =
      inverseSection f (R := R) M V m + inverseSection f (R := R) M V n := by
  let η := (AlgebraicGeometry.Scheme.canonicalAdjunction f R).unit.app M
  exact (inverseSection_unit f R M (op V) (m + n)).symm.trans
    (((η.val.app (op V)).hom.map_add m n).trans
      (congrArg₂ (· + ·)
        (inverseSection_unit f R M (op V) m)
        (inverseSection_unit f R M (op V) n)))

private theorem inverseSection_zero {X Y : Scheme.{u}} (f : X ⟶ Y)
    {R : Rings Y} (M : Modules R) (V : Y.ProEt) :
    inverseSection f (R := R) M V 0 = 0 := by
  exact (inverseSection_unit f R M (op V) 0).symm.trans
    ((((AlgebraicGeometry.Scheme.canonicalAdjunction f R).unit.app M).val.app
      (op V)).hom.map_zero)

private theorem inverseSection_smul {X Y : Scheme.{u}} (f : X ⟶ Y)
    {R : Rings Y} (M : Modules R) (V : Y.ProEt)
    (r : R.obj.obj (op V)) (m : M.val.obj (op V)) :
    inverseSection f (R := R) M V (r • m) =
      (((proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app R).hom.app (op V) r) •
        inverseSection f (R := R) M V m := by
  let η := (AlgebraicGeometry.Scheme.canonicalAdjunction f R).unit.app M
  have hh := (η.val.app (op V)).hom.map_smul r m
  change η.val.app (op V) (r • m) =
    (((proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app R).hom.app (op V) r) •
      (show ((inverse f R).obj M).val.obj
        (op ((proEtaleBaseChange f).obj V)) from η.val.app (op V) m) at hh
  exact (inverseSection_unit f R M (op V) (r • m)).symm.trans
    (hh.trans (congrArg
      (fun t : ((inverse f R).obj M).val.obj (op ((proEtaleBaseChange f).obj V)) ↦
        (((proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app R).hom.app
        (op V) r) • t)
      (inverseSection_unit f R M (op V) m)))

private theorem moduleSetsIdentification_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {R : Rings Y} {M N : Modules R} (k : M ⟶ N) :
    (AlgebraicGeometry.ProEtale.setPullback f).map (moduleMapSets k) ≫
        (moduleSetsIdentification f N).hom =
      (moduleSetsIdentification f M).hom ≫ moduleMapSets ((inverse f R).map k) := by
  apply inverseImage_map_ext f
  intro U m
  have hn := congrArg (fun z ↦ z.hom.app U m)
    ((AlgebraicGeometry.ProEtale.setPullbackAdjunction f).unit.naturality (moduleMapSets k))
  change (moduleSetsIdentification f N).hom.hom.app _
      (((AlgebraicGeometry.ProEtale.setPullback f).map (moduleMapSets k)).hom.app _
        (((AlgebraicGeometry.ProEtale.setPullbackAdjunction f).unit.app
          (moduleSets M)).hom.app U m)) = _
  change ((AlgebraicGeometry.ProEtale.setPullbackAdjunction f).unit.app
      (moduleSets N)).hom.app U (k.val.app U m) =
    ((AlgebraicGeometry.ProEtale.setPullback f).map (moduleMapSets k)).hom.app _
      (((AlgebraicGeometry.ProEtale.setPullbackAdjunction f).unit.app
        (moduleSets M)).hom.app U m) at hn
  rw [← hn]
  have hM := (Classical.choose_spec (moduleSetsIdentification_exists f M)).1 U.unop m
  have hN := (Classical.choose_spec (moduleSetsIdentification_exists f N)).1 U.unop
    (k.val.app U m)
  change (moduleSetsIdentification f M).hom.hom.app _ _ = _ at hM
  change (moduleSetsIdentification f N).hom.hom.app _ _ = _ at hN
  change _ = ((inverse f R).map k).val.app _
    ((moduleSetsIdentification f M).hom.hom.app _ _)
  exact hN.trans ((inverseSection_map f k U.unop m).symm.trans
    (congrArg (fun z ↦ ((inverse f R).map k).val.app
      ((proEtaleBaseChange f).op.obj U) z) hM.symm))

/-- The specified module inverse image transports the ring and module operations along
set inverse image. -/
private noncomputable def algebraicLift {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :
    SheafOfModules.AlgebraicInverseImage
      (AlgebraicGeometry.ProEtale.setPullback f) R
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) := by
  let eR := ringSetsIdentification f R
  let eI : (SheafOfModules.toSheaf ((sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) ⋙
        sheafCompose (ProEt.topology Y) (CategoryTheory.forget AddCommGrpCat.{u + 1})) ⋙
      AlgebraicGeometry.ProEtale.setPullback f ≅
      inverse f R ⋙ (SheafOfModules.toSheaf ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (inverseRing f R)) ⋙
          sheafCompose (ProEt.topology X) (CategoryTheory.forget AddCommGrpCat.{u + 1})) :=
    NatIso.ofComponents (fun M ↦ moduleSetsIdentification f (R := R) M)
      (fun k ↦ moduleSetsIdentification_naturality f (R := R) k)
  refine {
    ringUnderlying := eR
    modules := inverse f R
    moduleUnderlying := eI.symm
    ringAdd := ?_
    ringMul := ?_
    ringZero := ?_
    ringOne := ?_
    moduleAdd := ?_
    moduleZero := ?_
    moduleSMul := ?_
  }
  all_goals
    have hr (U : Y.ProEtᵒᵖ) (r : R.obj.obj U) :
        eR.hom.hom.app ((proEtaleBaseChange f).op.obj U)
          (((AlgebraicGeometry.ProEtale.setPullbackAdjunction f).unit.app
            (ringSets R)).hom.app U r) =
        ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app R).hom.app U r :=
      (Classical.choose_spec (ringSetsIdentification_exists f R)).1 U.unop r
    have hm (M : Modules R) (U : Y.ProEtᵒᵖ) (m : M.val.obj U) :
        (moduleSetsIdentification f (R := R) M).hom.hom.app ((proEtaleBaseChange f).op.obj U)
          (((AlgebraicGeometry.ProEtale.setPullbackAdjunction f).unit.app
            (moduleSets (R := R) M)).hom.app U m) = inverseSection f (R := R) M U.unop m :=
      (Classical.choose_spec (moduleSetsIdentification_exists f (R := R) M)).1 U.unop m
  · intro T a b t ht
    exact transport_binary f eR eR eR
      (fun U x y ↦ @Add.add (R.obj.obj U) inferInstance x y)
      (fun V x y ↦ @Add.add ((inverseRing f R).obj.obj V) inferInstance x y)
      (fun i x y ↦ ((inverseRing f R).obj.map i).hom.map_add x y |>.symm)
      (by
        intro U x y
        rw [hr, hr, hr]
        exact (((proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app R).hom.app U).hom.map_add
          x y) T a b t ht
  · intro T a b t ht
    exact transport_binary f eR eR eR
      (fun U x y ↦ @Mul.mul (R.obj.obj U) inferInstance x y)
      (fun V x y ↦ @Mul.mul ((inverseRing f R).obj.obj V) inferInstance x y)
      (fun i x y ↦ ((inverseRing f R).obj.map i).hom.map_mul x y |>.symm)
      (by
        intro U x y
        rw [hr, hr, hr]
        exact (((proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app R).hom.app U).hom.map_mul
          x y) T a b t ht
  · intro T a ha
    exact transport_binary f eR eR eR
      (fun U _ _ ↦ (0 : R.obj.obj U))
      (fun V _ _ ↦ (0 : (inverseRing f R).obj.obj V))
      (fun i _ _ ↦ ((inverseRing f R).obj.map i).hom.map_zero.symm)
      (by
        intro U x y
        rw [hr]
        exact (((proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app R).hom.app U).hom.map_zero)
      T a a a ha
  · intro T a ha
    exact transport_binary f eR eR eR
      (fun U _ _ ↦ (1 : R.obj.obj U))
      (fun V _ _ ↦ (1 : (inverseRing f R).obj.obj V))
      (fun i _ _ ↦ ((inverseRing f R).obj.map i).hom.map_one.symm)
      (by
        intro U x y
        rw [hr]
        exact (((proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app R).hom.app U).hom.map_one)
      T a a a ha
  · intro M T a b t ht
    exact transport_binary f (moduleSetsIdentification f (R := R) M)
      (moduleSetsIdentification f (R := R) M)
      (moduleSetsIdentification f (R := R) M)
      (fun U x y ↦ @Add.add (M.val.obj U) inferInstance x y)
      (fun V x y ↦ @Add.add (((inverse f R).obj M).val.obj V) inferInstance x y)
      (fun i x y ↦ (((inverse f R).obj M).val.map i).hom.map_add x y |>.symm)
      (by intro U x y; rw [hm, hm, hm]; exact inverseSection_add f (R := R) M U.unop x y)
      T a b t ht
  · intro M T a ha
    exact transport_binary f (moduleSetsIdentification f (R := R) M)
      (moduleSetsIdentification f (R := R) M)
      (moduleSetsIdentification f (R := R) M)
      (fun U _ _ ↦ (0 : M.val.obj U))
      (fun V _ _ ↦ (0 : ((inverse f R).obj M).val.obj V))
      (fun i _ _ ↦ (((inverse f R).obj M).val.map i).hom.map_zero.symm)
      (by
        intro U x y
        rw [hm]
        exact inverseSection_zero f (R := R) M U.unop)
      T a a a ha
  · intro M T a b t ht
    exact transport_binary f eR (moduleSetsIdentification f (R := R) M)
      (moduleSetsIdentification f (R := R) M)
      (fun U x y ↦ @SMul.smul (R.obj.obj U) (M.val.obj U) inferInstance x y)
      (fun V x y ↦ @SMul.smul ((inverseRing f R).obj.obj V)
        (((inverse f R).obj M).val.obj V) inferInstance x y)
      (fun i x y ↦ (((inverse f R).obj M).val.map_smul i x y).symm)
      (by intro U x y; rw [hm, hr, hm]; exact inverseSection_smul f (R := R) M U.unop x y)
      T a b t ht

end AlgebraicLift

-- Use normalization and adjunction equations without expanding their constructions.
attribute [local irreducible] monoidalCategory tensorObjIsoSheafification
  PresheafOfModules.sheafificationAdjunction

section TensorPresentation
universe c h r
variable {C : Type c} [Category.{h} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasWeakSheafify J AddCommGrpCat.{r}]
  (A : Sheaf J CommRingCat.{r})
  [(J.W.inverseImage (PresheafOfModules.toPresheaf.{r}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A).obj)).IsMonoidal]
  (P Q : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A))

private theorem tensorPresentation_exists :
    ∃ e : (monoidalCategory A).tensorObj P Q ≅ (siteSheafTensorRight Q).obj P,
      ∀ (U : Cᵒᵖ) (x : P.val.obj U) (y : Q.val.obj U),
        e.hom.val.app U
          ((tensorObjIsoSheafification (R := A) P Q).inv.val.app U
            (((PresheafOfModules.sheafificationAdjunction.{r}
              (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A).obj)).unit.app
                (PresheafOfModules.Monoidal.tensorObj P.val Q.val)).app U
                  (x ⊗ₜ[A.obj.obj U] y))) = siteSheafTensorTmul P Q U x y := by
  let ep : PresheafOfModules.Monoidal.tensorObj P.val Q.val ≅
      siteTensorPresheaf P.val Q.val :=
    PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (by
      intro U V i
      apply ModuleCat.hom_ext
      refine TensorProduct.ext' (R := A.obj.obj U) (R₂ := A.obj.obj U) ?_
      intro x y
      rfl)
  let L := PresheafOfModules.sheafification.{r}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A).obj)
  let adj := PresheafOfModules.sheafificationAdjunction.{r}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A).obj)
  let t := tensorObjIsoSheafification (R := A) P Q
  let e := t ≪≫ L.mapIso ep
  refine ⟨e, ?_⟩
  intro U x y
  let v := ((adj.unit.app (PresheafOfModules.Monoidal.tensorObj P.val Q.val)).app U)
    (x ⊗ₜ[A.obj.obj U] y)
  have hi := congrArg (fun z ↦ z.val.app U v) t.inv_hom_id
  have hu := congrArg (fun z ↦ z.app U (x ⊗ₜ[A.obj.obj U] y))
    (adj.unit.naturality ep.hom).symm
  change (L.map ep.hom).val.app U v = siteSheafTensorTmul P Q U x y at hu
  exact (congrArg ((L.map ep.hom).val.app U) hi).trans hu
end TensorPresentation

section ScalarFunctor
universe c h r
variable {C : Type c} [Category.{h} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasWeakSheafify J AddCommGrpCat.{r}]

private noncomputable def scalarPresheafFunctor (A : Sheaf J CommRingCat.{r}) :
    SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A) ⥤
      PresheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A).obj where
  obj M := changeOfRingsPresheaf (𝟙 A) M
  map {M N} f :=
    { app := fun W ↦ (ModuleCat.extendScalars ((𝟙 A : A ⟶ A).hom.app W).hom).map (f.val.app W)
      naturality := changeOfRingsHom_naturality (𝟙 A) _ f }
  map_id M := by
    ext W : 1
    exact (ModuleCat.extendScalars ((𝟙 A : A ⟶ A).hom.app W).hom).map_id _
  map_comp f g := by
    ext W : 1
    exact (ModuleCat.extendScalars ((𝟙 A : A ⟶ A).hom.app W).hom).map_comp _ _

private noncomputable def scalarFunctor (A : Sheaf J CommRingCat.{r}) :=
  scalarPresheafFunctor A ⋙ PresheafOfModules.sheafification.{r}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A).obj)

end ScalarFunctor

private noncomputable def tensorMapIso {X : Scheme.{u}} {R : Rings X}
    {M M' N N' : Modules R} (a : M ≅ M') (b : N ≅ N') :
    tensor M N ≅ tensor M' N' where
  hom := tensorMap (R := R) a.hom b.hom
  inv := tensorMap (R := R) a.inv b.inv
  hom_inv_id := by
    apply tensor_hom_ext (R := R)
    intro V x y
    change (tensorMap (R := R) a.inv b.inv).val.app (op V)
        ((tensorMap (R := R) a.hom b.hom).val.app (op V) (pure (R := R) M N V x y)) = _
    rw [tensorMap_pure, tensorMap_pure]
    have ha := congrArg (fun z ↦ z.val.app (op V) x) a.hom_inv_id
    have hb := congrArg (fun z ↦ z.val.app (op V) y) b.hom_inv_id
    exact congrArg₂ (pure (R := R) M N V) ha hb
  inv_hom_id := by
    apply tensor_hom_ext (R := R)
    intro V x y
    change (tensorMap (R := R) a.hom b.hom).val.app (op V)
        ((tensorMap (R := R) a.inv b.inv).val.app (op V) (pure (R := R) M' N' V x y)) = _
    rw [tensorMap_pure, tensorMap_pure]
    have ha := congrArg (fun z ↦ z.val.app (op V) x) a.inv_hom_id
    have hb := congrArg (fun z ↦ z.val.app (op V) y) b.inv_hom_id
    exact congrArg₂ (pure (R := R) M' N' V) ha hb

private theorem algebraicLift_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    {R : Rings Y} (P : Modules R)
    {T : Sheaf (ProEt.topology Y) (Type (u + 1))} (z : T ⟶ moduleSets (R := R) P)
    (V : Y.ProEt) (t : T.obj.obj (op V)) :
    ((AlgebraicGeometry.ProEtale.setPullback f).map z ≫
        (algebraicLift f R).moduleUnderlying.inv.app P).hom.app
          (op ((proEtaleBaseChange f).obj V))
            (((AlgebraicGeometry.ProEtale.setPullbackAdjunction f).unit.app T).hom.app
              (op V) t) = inverseSection f (R := R) P V (z.hom.app (op V) t) := by
  have hn := congrArg (fun q ↦ q.hom.app (op V) t)
    ((AlgebraicGeometry.ProEtale.setPullbackAdjunction f).unit.naturality z)
  change ((AlgebraicGeometry.ProEtale.setPullbackAdjunction f).unit.app
      (moduleSets (R := R) P)).hom.app (op V) (z.hom.app (op V) t) =
    ((AlgebraicGeometry.ProEtale.setPullback f).map z).hom.app _
      (((AlgebraicGeometry.ProEtale.setPullbackAdjunction f).unit.app T).hom.app (op V) t)
      at hn
  change (moduleSetsIdentification f (R := R) P).hom.hom.app _
    (((AlgebraicGeometry.ProEtale.setPullback f).map z).hom.app _ _) = _
  exact (congrArg ((moduleSetsIdentification f (R := R) P).hom.hom.app
    (op ((proEtaleBaseChange f).obj V))) hn.symm).trans
      ((Classical.choose_spec (moduleSetsIdentification_exists f (R := R) P)).1 V _)

private theorem comparison_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Rings Y) (M N : Modules R) : IsIso (comparison f R M N) := by
  let RI := inverseRing f R
  let F := inverse f R
  let I := algebraicLift f R
  let L := AlgebraicGeometry.ProEtale.setPullback f
  let T := F ⋙ scalarFunctor RI
  let hobj (P : Modules R) : T.obj P = changeOfRings (𝟙 RI) (I.modules.obj P) := rfl
  let : PreservesFiniteLimits L :=
    (AlgebraicGeometry.ProEtale.toposFunctorialityInverseImage f (𝟙 Y)).2.2.2.1
  have hmap {P Q : Modules R} (a : P ⟶ Q) :
      T.map a = eqToHom (hobj P) ≫
        changeOfRingsHom (𝟙 RI) (I.modules.obj P) (I.modules.map a) ≫
          eqToHom (hobj Q).symm := by
    rfl
  let k := Classical.choice
    (CanonicalTensorPullbackOfUniverses.canonicalRingedTensorComparison_existsUnique.{u + 1, u}
       R RI RI L I (𝟙 RI) T hobj
        (AlgebraicGeometry.ProEtale.lowerStar (Type (u + 1)) f)
        (AlgebraicGeometry.ProEtale.setPullbackAdjunction f) hmap).1
  clear_value k
  let a (P : Modules R) : T.obj P ≅ F.obj P :=
    Classical.choose (identityScalarIso_exists RI (F.obj P))
  have hq (P : Modules R) (W : X.ProEtᵒᵖ) (m : (F.obj P).val.obj W) :
      (a P).hom.val.app W ((k.q P).hom.app W m) = m := by
    exact (congrArg ((a P).hom.val.app W) (k.q_one P W m)).trans
      ((Classical.choose_spec (identityScalarIso_exists RI (F.obj P))).1 W m)
  have hqi (P : Modules R) (W : X.ProEtᵒᵖ) (m : (F.obj P).val.obj W) :
      (a P).inv.val.app W m = (k.q P).hom.app W m := by
    have hi := congrArg (fun q ↦ q.val.app W ((k.q P).hom.app W m)) (a P).hom_inv_id
    exact (congrArg ((a P).inv.val.app W) (hq P W m).symm).trans hi
  clear_value a
  let eS := Classical.choose (tensorPresentation_exists.{u + 1, u, u + 1} R M N)
  let eT := Classical.choose (tensorPresentation_exists.{u + 1, u, u + 1} RI (T.obj M) (T.obj N))
  have heS := (Classical.choose_spec (tensorPresentation_exists.{u + 1, u, u + 1} R M N))
  have heT := (Classical.choose_spec
    (tensorPresentation_exists.{u + 1, u, u + 1} RI (T.obj M) (T.obj N)))
  let P := (monoidalCategory.{u, u + 1, u + 1} R).tensorObj M N
  have heSi (V : Y.ProEt) (m : M.val.obj (op V)) (n : N.val.obj (op V)) :
      eS.inv.val.app (op V) (pure (R := R) M N V m n) =
        (tensorObjIsoSheafification.{u, u + 1, u + 1} (R := R) M N).inv.val.app (op V)
          (((PresheafOfModules.sheafificationAdjunction.{u + 1, u, u + 1, u + 1}
            (𝟙 ((sheafCompose (ProEt.topology Y)
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj)).unit.app
                (PresheafOfModules.Monoidal.tensorObj.{u + 1, u, u + 1} (R := R.obj)
                  M.val N.val)).app (op V)
                  (m ⊗ₜ[R.obj.obj (op V)] n)) := by
    have h := congrArg (eS.inv.val.app (op V)) (heS (op V) m n)
    have hi := congrArg (fun z ↦ z.val.app (op V)
      ((tensorObjIsoSheafification.{u, u + 1, u + 1} (R := R) M N).inv.val.app (op V)
        (((PresheafOfModules.sheafificationAdjunction.{u + 1, u, u + 1, u + 1}
          (𝟙 ((sheafCompose (ProEt.topology Y)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj)).unit.app
              (PresheafOfModules.Monoidal.tensorObj.{u + 1, u, u + 1} (R := R.obj)
                M.val N.val)).app (op V)
                (m ⊗ₜ[R.obj.obj (op V)] n)))) eS.hom_inv_id
    exact h.symm.trans hi
  clear_value eS
  let Z := MonoidalCategory.tensorObj (moduleSets (R := R) M) (moduleSets (R := R) N)
  let x : Z ⟶ moduleSets (R := R) M := CartesianMonoidalCategory.fst _ _
  let y : Z ⟶ moduleSets (R := R) N := CartesianMonoidalCategory.snd _ _
  let zSite : Z ⟶ moduleSets (R := R) (tensor (R := R) M N) :=
    binaryMap (moduleSets (R := R) M) (moduleSets (R := R) N)
      (moduleSets (R := R) (tensor (R := R) M N))
      (fun U m n ↦ pure (R := R) M N U.unop m n)
      (fun i m n ↦ (pure_restriction (R := R) M N i m n).symm) x y
  let z : Z ⟶ moduleSets (R := R) P := zSite ≫ moduleMapSets (R := R) eS.inv
  have hz (W : Y.ProEtᵒᵖ) (t : Z.obj.obj W) :
      z.hom.app W t = (tensorObjIsoSheafification.{u, u + 1, u + 1} (R := R) M N).inv.val.app W
        (((PresheafOfModules.sheafificationAdjunction.{u + 1, u, u + 1, u + 1}
          (𝟙 ((sheafCompose (ProEt.topology Y)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj)).unit.app
              (PresheafOfModules.Monoidal.tensorObj.{u + 1, u, u + 1} (R := R.obj)
                M.val N.val)).app W
                (x.hom.app W t ⊗ₜ[R.obj.obj W] y.hom.app W t)) :=
    heSi W.unop _ _
  have hk (V : Y.ProEt) (m : M.val.obj (op V)) (n : N.val.obj (op V)) :
      eT.hom.val.app (op ((proEtaleBaseChange f).obj V))
        ((k.mu M N).hom.val.app (op ((proEtaleBaseChange f).obj V))
          ((k.q P).hom.app (op ((proEtaleBaseChange f).obj V))
            (inverseSection f (R := R) P V
              (eS.inv.val.app (op V) (pure (R := R) M N V m n))))) =
      pure (R := RI) (T.obj M) (T.obj N) ((proEtaleBaseChange f).obj V)
        ((k.q M).hom.app (op ((proEtaleBaseChange f).obj V))
          (inverseSection f (R := R) M V m))
        ((k.q N).hom.app (op ((proEtaleBaseChange f).obj V))
          (inverseSection f (R := R) N V n)) := by
    let W := op ((proEtaleBaseChange f).obj V)
    let t : Z.obj.obj (op V) := (m, n)
    let s := ((AlgebraicGeometry.ProEtale.setPullbackAdjunction f).unit.app Z).hom.app (op V) t
    let p0 := (L.map z ≫ I.moduleUnderlying.inv.app P).hom.app W s
    let m0 := (L.map x ≫ I.moduleUnderlying.inv.app M).hom.app W s
    let n0 := (L.map y ≫ I.moduleUnderlying.inv.app N).hom.app W s
    have hh := k.pure (R := R) M N Z x y z hz W s
    change (k.mu M N).hom.val.app W ((k.q P).hom.app W p0) =
      (tensorObjIsoSheafification.{u, u + 1, u + 1} (R := RI) (T.obj M) (T.obj N)).inv.val.app W
        (((PresheafOfModules.sheafificationAdjunction.{u + 1, u, u + 1, u + 1}
          (𝟙 ((sheafCompose (ProEt.topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RI).obj)).unit.app
              (PresheafOfModules.Monoidal.tensorObj.{u + 1, u, u + 1} (R := RI.obj)
                (T.obj M).val (T.obj N).val)).app W
                  ((k.q M).hom.app W m0 ⊗ₜ[RI.obj.obj W]
                    (k.q N).hom.app W n0)) at hh
    have hp : p0 = inverseSection f (R := R) P V
        (eS.inv.val.app (op V) (pure (R := R) M N V m n)) :=
      algebraicLift_unit f (R := R) P z V t
    have hm : m0 = inverseSection f (R := R) M V m :=
      algebraicLift_unit f (R := R) M x V t
    have hn : n0 = inverseSection f (R := R) N V n :=
      algebraicLift_unit f (R := R) N y V t
    clear_value p0 m0 n0
    have hl := congrArg
      (fun a ↦ eT.hom.val.app W ((k.mu M N).hom.val.app W ((k.q P).hom.app W a))) hp
    have hr := congrArg₂ (pure (R := RI) (T.obj M) (T.obj N) W.unop)
      (congrArg ((k.q M).hom.app W) hm) (congrArg ((k.q N).hom.app W) hn)
    exact hl.symm.trans ((congrArg (eT.hom.val.app W) hh).trans
      ((heT W ((k.q M).hom.app W m0) ((k.q N).hom.app W n0)).trans hr))
  clear_value eT
  let e : F.obj (tensor (R := R) M N) ≅ tensor (R := RI) (F.obj M) (F.obj N) :=
    F.mapIso eS.symm ≪≫ (a P).symm ≪≫ k.mu M N ≪≫ eT ≪≫
      tensorMapIso (R := RI) (a M) (a N)
  have he (V : Y.ProEt) (m : M.val.obj (op V)) (n : N.val.obj (op V)) :
      e.hom.val.app (op ((proEtaleBaseChange f).obj V))
        (inverseSection f (R := R) (tensor (R := R) M N) V
          (pure (R := R) M N V m n)) =
      pure (R := RI) (F.obj M) (F.obj N) ((proEtaleBaseChange f).obj V)
        (inverseSection f (R := R) M V m) (inverseSection f (R := R) N V n) := by
    let W := op ((proEtaleBaseChange f).obj V)
    let d := tensorMap (R := RI) (a M).hom (a N).hom
    let u := inverseSection f (R := R) (tensor (R := R) M N) V (pure (R := R) M N V m n)
    let p := inverseSection f (R := R) P V (eS.inv.val.app (op V) (pure (R := R) M N V m n))
    let xm := inverseSection f (R := R) M V m
    let yn := inverseSection f (R := R) N V n
    change d.val.app W (eT.hom.val.app W ((k.mu M N).hom.val.app W
      ((a P).inv.val.app W ((F.map eS.inv).val.app W u)))) = _
    calc
      d.val.app W (eT.hom.val.app W ((k.mu M N).hom.val.app W
          ((a P).inv.val.app W ((F.map eS.inv).val.app W u)))) =
          d.val.app W (eT.hom.val.app W ((k.mu M N).hom.val.app W
            ((a P).inv.val.app W p))) :=
        congrArg (fun v ↦ d.val.app W (eT.hom.val.app W
          ((k.mu M N).hom.val.app W ((a P).inv.val.app W v))))
            (inverseSection_map f (R := R) eS.inv V (pure (R := R) M N V m n))
      _ = d.val.app W (eT.hom.val.app W ((k.mu M N).hom.val.app W
          ((k.q P).hom.app W p))) :=
        congrArg (fun v ↦ d.val.app W (eT.hom.val.app W ((k.mu M N).hom.val.app W v)))
          (hqi P W p)
      _ = d.val.app W (pure (R := RI) (T.obj M) (T.obj N) W.unop
          ((k.q M).hom.app W xm) ((k.q N).hom.app W yn)) :=
        congrArg (d.val.app W) (hk V m n)
      _ = pure (R := RI) (F.obj M) (F.obj N) W.unop
          ((a M).hom.val.app W ((k.q M).hom.app W xm))
          ((a N).hom.val.app W ((k.q N).hom.app W yn)) :=
        tensorMap_pure (R := RI) (a M).hom (a N).hom W.unop
          ((k.q M).hom.app W xm) ((k.q N).hom.app W yn)
      _ = pure (R := RI) (F.obj M) (F.obj N) W.unop xm yn :=
        congrArg₂ (pure (R := RI) (F.obj M) (F.obj N) W.unop)
          (hq M W xm) (hq N W yn)
  clear_value e
  have heq : e.hom = comparison f R M N :=
    (Classical.choose_spec (comparison_exists f R M N)).2 e.hom he
  exact heq ▸ (inferInstanceAs (IsIso e.hom))

/-- The normalized pro-etale inverse-image tensor comparison: invertibility, local formula,
joint naturality, coefficient change, set/ring/module composition, and the identity case.
The existence and uniqueness assertions are comparison_exists and setComp_unique; the
coefficient quotient and the semilinear identifications above have unique normalizations. -/
theorem inverseImage_tensor_comparison {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z)
    (R : Rings Z) (M N : Modules R) :
    IsIso (comparison h R M N) ∧
    (∀ (V : Z.ProEt) (s : M.val.obj (op V)) (t : N.val.obj (op V)),
      (comparison h R M N).val.app (op ((proEtaleBaseChange h).obj V))
        (inverseSection h (tensor M N) V (pure M N V s t)) =
      pure ((inverse h R).obj M) ((inverse h R).obj N) ((proEtaleBaseChange h).obj V)
        (inverseSection h M V s) (inverseSection h N V t)) ∧
    (∀ (M' N' : Modules R) (a : M ⟶ M') (b : N ⟶ N'),
      (inverse h R).map (tensorMap a b) ≫ comparison h R M' N' =
        comparison h R M N ≫ tensorMap ((inverse h R).map a) ((inverse h R).map b)) ∧
    (∀ (S : Rings Z) (a : R ⟶ S) (F G : Modules S),
      (inverse h R).map (coefficientQuotient a F G) ≫
          (scalarIdentification h a (tensor F G)).hom ≫
          (restrict (inverseRingMap h a)).map (comparison h S F G) =
        comparison h R ((restrict a).obj F) ((restrict a).obj G) ≫
          tensorMap (scalarIdentification h a F).hom (scalarIdentification h a G).hom ≫
          coefficientQuotient (inverseRingMap h a)
            ((inverse h S).obj F) ((inverse h S).obj G)) ∧
    ((AlgebraicGeometry.ProEtale.setPullbackComp g h).hom.app (ringSets R) ≫
        (AlgebraicGeometry.ProEtale.setPullback g).map (ringSetsIdentification h R).hom ≫
        (ringSetsIdentification g (inverseRing h R)).hom =
      (ringSetsIdentification (g ≫ h) R).hom ≫ ringMapSets (ringComp g h R).hom) ∧
    (∀ P : Modules R,
      (AlgebraicGeometry.ProEtale.setPullbackComp g h).hom.app (moduleSets P) ≫
          (AlgebraicGeometry.ProEtale.setPullback g).map (moduleSetsIdentification h P).hom ≫
          (moduleSetsIdentification g ((inverse h R).obj P)).hom =
        (moduleSetsIdentification (g ≫ h) P).hom ≫ moduleMapSets (moduleComp g h R P).hom) ∧
    ((moduleComp g h R (tensor M N)).hom ≫
        (restrict (ringComp g h R).hom).map
          ((inverse g (inverseRing h R)).map (comparison h R M N)) ≫
        (restrict (ringComp g h R).hom).map
          (comparison g (inverseRing h R) ((inverse h R).obj M) ((inverse h R).obj N)) =
      comparison (g ≫ h) R M N ≫
        tensorMap (moduleComp g h R M).hom (moduleComp g h R N).hom ≫
        coefficientQuotient (ringComp g h R).hom
          ((inverse g (inverseRing h R)).obj ((inverse h R).obj M))
          ((inverse g (inverseRing h R)).obj ((inverse h R).obj N))) ∧
    (∀ H : Sheaf (ProEt.topology Z) (Type (u + 1)),
      IsIso ((AlgebraicGeometry.ProEtale.setPullbackAdjunction (𝟙 Z)).unit.app H)) ∧
    (comparison (𝟙 Z) R M N ≫ tensorMap (moduleId R M).hom (moduleId R N).hom ≫
      coefficientQuotient (ringId R).hom M N = (moduleId R (tensor M N)).hom) := by
  exact ⟨comparison_isIso h R M N, comparison_pure h R M N,
    fun M' N' a b ↦ comparison_naturality h R a b,
    fun S a F G ↦ comparison_coefficient_change h a F G,
    ringSets_composition g h R, fun P ↦ moduleSets_composition g h R P,
    comparison_composition g h R M N,
    fun H ↦ setIdentity_unit_isIso H, comparison_identity R M N⟩

end AlgebraicGeometry.ProEtaleTensorComparison
