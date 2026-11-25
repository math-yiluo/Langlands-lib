/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.Ringed.RingedSectionLocalizationOfUniversesSupplement
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

import WeilConjectures.CategoryTheory.GeometricMorphism.GeometricInverseImageExactSupplement
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.RingTheory.ModuleLocalizationFilteredColimit
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.RingTheory.Localization.Module
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.RingTheory.Flat.Localization
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-!
# Localization and geometric inverse image

Source: Stacks Project, Modules on Sites, Tags 03EL, 03CZ and 03D2; the localization
universal property and its identity/composition normalization
(blueprint: lem-weil-pbc-localization-inverse-image-coherence).

## Main statements

- `existsUnique_localizationInverseImage`: the unit-normalized module natural isomorphism.
- `existsUnique_localizationInverseImageRing`: the normalized ring-sheaf isomorphism.
- `localizationInverseImage_fraction`: normalization on all generalized fractions.
- `localizationInverseImage_comp`, `_id`, `_coefficient`: module coherence equations.
- `localizationComparisonDerived`: canonical descent to ordinary unbounded derived categories.

## Proof dependencies

1. Identify the tensor localization with sheafified fractions using
   `lem-pc-sites-module-sheafification-tensor`, `lem-weil-pbc-localization-tensor`,
   `lem-pc-sites-sheafification-underlying-sets` and
   `def-weil-presheaf-modules-sheafification`. The identification takes units to units.
2. The ring mapping property follows objectwise from
   `lem-weil-pbc-localization-away-universal-property`, then from sheafification.
3. Extend a module map by sending m/t^n to the inverse t-action applied n times to its
   image, using `def-weil-pbc-module-localization`; sheafify and use uniqueness.
4. `lem-weil-pbc-adjunction-lifts-group-ring-objects` and
   `situation-conventions` transport the ring initial property.
5. `lem-weil-pbc-geometric-module-transport` transports the module initial property.
6. The same unit characterization proves naturality and the generalized fraction formula.
7. Kernels of inverse image are finite limits, and its adjunction preserves cokernels;
   use `situation-conventions` and
   `situation-conventions`.
8. For scalar localization combine `lem-weil-pbc-localization-module-exact`,
   `lem-weil-pbc-ringed-site-module-sheafification-exact` and
   `lem-weil-pbc-ringed-topoi-module-adjunction` to obtain kernels and cokernels.
9. `def-weil-pbc-composite-adjunction` and `situation-conventions`
   identify the composite inverse image. Both comparison routes extend the same unit,
   so uniqueness proves the composition and identity equations.
10. Extend a specified ring isomorphism using the localization mapping property; its
    module reinterpretation preserves units, so the same uniqueness proves the square.
11. `situation-conventions`,
    `lem-weil-pbc-exact-functor-derived-functor` and
    `lem-weil-pbc-localization-universal-property` descend the termwise comparison,
    units and equations on every unbounded complex.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u uC vC uD vD uF vF uA uB uE vA vB vE wA wB wE

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The existing module category of a commutative ring sheaf.
Source: Stacks, Tag 03D2
(blueprint: lem-weil-pbc-localization-inverse-image-coherence). -/
abbrev inverseLocalizationModules
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify J CommRingCat.{u}]
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (R : Sheaf J CommRingCat.{u}) :=
  ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)

/-- Scalar localization is the existing sheaf tensor product with the localized ring.
The order of factors is `M ⊗ R[1/t]`, the symmetric form of `R[1/t] ⊗ M`.
Source: Stacks, Tags 03EK and 00DK
(blueprint: lem-weil-pbc-localization-inverse-image-coherence). -/
abbrev scalarLocalization
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify J CommRingCat.{u}]
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (R : Sheaf J CommRingCat.{u}) (t : (R.obj ⋙ forget CommRingCat.{u}).sections) :
    inverseLocalizationModules R ⥤ inverseLocalizationModules R :=
  SheafOfModules.siteSheafTensorRight (A := R) (ringedSectionLocalizationOfUniverses R t)

/-- The localization unit is uniquely specified by `m ↦ m ⊗ 1` on every section.
Source: Stacks, Tags 03EK and 00DK
(blueprint: lem-weil-pbc-localization-inverse-image-coherence).
Proof: the pure-tensor map is linear and compatible with restriction because the
localization restrictions preserve one. Compose with the module sheafification unit.
Naturality follows on pure tensors. Every section of the source has the specified image,
so componentwise extensionality proves uniqueness. -/
theorem existsUnique_scalarLocalizationUnit
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify J CommRingCat.{u}]
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (R : Sheaf J CommRingCat.{u}) (t : (R.obj ⋙ forget CommRingCat.{u}).sections) :
    ∃! η : 𝟭 (inverseLocalizationModules R) ⟶ scalarLocalization R t,
      ∀ (M : inverseLocalizationModules R) (U : Cᵒᵖ) (m : M.val.obj U),
        (η.app M).val.app U m =
          SheafOfModules.siteSheafTensorTmul M (ringedSectionLocalizationOfUniverses R t) U m
            ((ringedSectionLocalizationUnitOfUniverses R t).val.app U (1 : R.obj.obj U)) := by
  let N := ringedSectionLocalizationOfUniverses R t
  let j := ringedSectionLocalizationUnitOfUniverses R t
  let p (M : inverseLocalizationModules R) : M.val ⟶
      SheafOfModules.siteTensorPresheaf M.val N.val :=
    { app := fun U ↦ by
        change ModuleCat.of (R.obj.obj U) (M.val.obj U) ⟶ ModuleCat.of (R.obj.obj U)
          (TensorProduct (R.obj.obj U) (M.val.obj U) (N.val.obj U))
        exact ModuleCat.ofHom (R := R.obj.obj U)
          { toFun := fun m ↦ m ⊗ₜ[R.obj.obj U] (j.val.app U (1 : R.obj.obj U))
            map_add' := by intros; exact TensorProduct.add_tmul _ _ _
            map_smul' := by intros; exact TensorProduct.smul_tmul' _ _ _ }
      naturality := by
        intro U V f
        apply ModuleCat.hom_ext
        ext m
        change (show M.val.obj V from M.val.map f m) ⊗ₜ[R.obj.obj V]
            j.val.app V (1 : R.obj.obj V) =
          (show M.val.obj V from M.val.map f m) ⊗ₜ[R.obj.obj V]
            (show N.val.obj V from N.val.map f (j.val.app U (1 : R.obj.obj U)))
        congr 1
        rw [← PresheafOfModules.naturality_apply j.val f]
        change j.val.app V (1 : R.obj.obj V) =
          j.val.app V (R.obj.map f (1 : R.obj.obj U))
        rw [(R.obj.map f).hom.map_one] }
  let η : 𝟭 (inverseLocalizationModules R) ⟶ scalarLocalization R t :=
    { app := fun M ↦ ⟨p M ≫
        (PresheafOfModules.sheafificationAdjunction
          (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).unit.app
          (SheafOfModules.siteTensorPresheaf M.val N.val)⟩
      naturality := by
        intro M M' f
        apply SheafOfModules.hom_ext
        change f.val ≫ p M' ≫ _ = (p M ≫ _) ≫ _
        rw [← Category.assoc]
        have hp : f.val ≫ p M' = p M ≫ SheafOfModules.siteTensorHom f.val N.val := by
          ext U m
          rfl
        rw [hp, Category.assoc]
        exact congrArg (fun g ↦ p M ≫ g)
          ((PresheafOfModules.sheafificationAdjunction
          (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).unit.naturality
            (SheafOfModules.siteTensorHom f.val N.val)) }
  refine ⟨η, ?_, ?_⟩
  · intro M U m
    rfl
  · intro θ hθ
    apply NatTrans.ext
    funext M
    apply SheafOfModules.hom_ext
    ext U m
    exact hθ M U m

/-- The actual localization unit, chosen from its unique sectionwise specification.
Source: Stacks, Tags 03EK and 00DK
(blueprint: lem-weil-pbc-localization-inverse-image-coherence). -/
def scalarLocalizationUnit
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify J CommRingCat.{u}]
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (R : Sheaf J CommRingCat.{u}) (t : (R.obj ⋙ forget CommRingCat.{u}).sections) :
    𝟭 (inverseLocalizationModules R) ⟶ scalarLocalization R t :=
  Classical.choose (existsUnique_scalarLocalizationUnit R t)

/-- The underlying set sheaf of a module sheaf.
Source: Stacks, Tag 03D2
(blueprint: lem-weil-pbc-localization-inverse-image-coherence). -/
abbrev localizationModuleSets
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify J CommRingCat.{u}]
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (R : Sheaf J CommRingCat.{u}) :=
  SheafOfModules.toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
    sheafCompose J (forget AddCommGrpCat.{u})

/-- Transport of a global section, tested on all generalized elements. This expresses
`t' = f⁻¹t` without a point or a presentation of the geometric morphism by a site functor.
Source: Stacks, Tag 00YV
(blueprint: lem-weil-pbc-localization-inverse-image-coherence). -/
def IsInverseImageSection
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
    {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify J CommRingCat.{u}]
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] {K : GrothendieckTopology D}
    [HasSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify K CommRingCat.{u}]
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {L : Sheaf J (Type u) ⥤ Sheaf K (Type u)}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (a : SheafOfModules.AlgebraicInverseImage L R S)
    (t : (R.obj ⋙ forget CommRingCat.{u}).sections)
    (s : (S.obj ⋙ forget CommRingCat.{u}).sections) : Prop :=
  ∀ (T : Sheaf J (Type u))
    (r : T ⟶ (sheafCompose J (forget CommRingCat.{u})).obj R),
    (∀ (U : Cᵒᵖ) (x : T.obj.obj U), r.hom.app U x = t.val U) →
    ∀ (V : Dᵒᵖ) (x : (L.obj T).obj.obj V),
      a.ringUnderlying.hom.hom.app V ((L.map r).hom.app V x) = s.val V

private def unliftSetSheafIso
    {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C} :
    sheafCompose J uliftFunctor.{u, u} ≅ 𝟭 (Sheaf J (Type u)) :=
  NatIso.ofComponents (fun T ↦
    { hom := ⟨{ app := fun _ ↦ ↾ULift.down }⟩
      inv := ⟨{ app := fun _ ↦ ↾ULift.up }⟩ })
    (by intro T T' f; rfl)

private def inverseImageUniverses
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {L : Sheaf J (Type u) ⥤ Sheaf K (Type u)}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (a : SheafOfModules.AlgebraicInverseImage L R S) :
    SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, u, u} L R S := by
  let eJ := unliftSetSheafIso (J := J)
  let eK := unliftSetSheafIso (J := K)
  let rR := (sheafCompose J (forget CommRingCat.{u})).obj R
  let rS := (sheafCompose K (forget CommRingCat.{u})).obj S
  let mR := SheafOfModules.toSheaf.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
      sheafCompose J (forget AddCommGrpCat.{u})
  let mS := SheafOfModules.toSheaf.{u}
    ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙
      sheafCompose K (forget AddCommGrpCat.{u})
  refine
    { ringUnderlying := L.mapIso (eJ.app rR) ≪≫ a.ringUnderlying ≪≫ (eK.app rS).symm
      modules := a.modules
      moduleUnderlying :=
        Functor.isoWhiskerLeft a.modules (Functor.isoWhiskerLeft mS eK) ≪≫
          a.moduleUnderlying ≪≫
            Functor.isoWhiskerRight (Functor.isoWhiskerLeft mR eJ.symm) L
      ringAdd := ?_
      ringMul := ?_
      ringZero := ?_
      ringOne := ?_
      moduleAdd := ?_
      moduleZero := ?_
      moduleSMul := ?_ }
  · intro T x y z h W q
    simpa [eJ, eK, unliftSetSheafIso, Functor.map_comp] using
      a.ringAdd T (x ≫ eJ.hom.app rR) (y ≫ eJ.hom.app rR)
        (z ≫ eJ.hom.app rR) h W q
  · intro T x y z h W q
    simpa [eJ, eK, unliftSetSheafIso, Functor.map_comp] using
      a.ringMul T (x ≫ eJ.hom.app rR) (y ≫ eJ.hom.app rR)
        (z ≫ eJ.hom.app rR) h W q
  · intro T x h W q
    simpa [eJ, eK, unliftSetSheafIso, Functor.map_comp] using
      a.ringZero T (x ≫ eJ.hom.app rR) h W q
  · intro T x h W q
    simpa [eJ, eK, unliftSetSheafIso, Functor.map_comp] using
      a.ringOne T (x ≫ eJ.hom.app rR) h W q
  · intro M T x y z h W q
    have h' := a.moduleAdd M T (x ≫ eJ.hom.app (mR.obj M))
      (y ≫ eJ.hom.app (mR.obj M)) (z ≫ eJ.hom.app (mR.obj M)) h W q
    simp only [Functor.map_comp] at h'
    convert h' using 1
    all_goals rfl
  · intro M T x h W q
    have h' := a.moduleZero M T (x ≫ eJ.hom.app (mR.obj M)) h W q
    simp only [Functor.map_comp] at h'
    convert h' using 1
    all_goals rfl
  · intro M T r x z h W q
    have h' := a.moduleSMul M T (r ≫ eJ.hom.app rR) (x ≫ eJ.hom.app (mR.obj M))
      (z ≫ eJ.hom.app (mR.obj M)) h W q
    simp only [Functor.map_comp] at h'
    convert h' using 1
    all_goals rfl

namespace LocalizationSequence

set_option linter.unusedSectionVars false

open Opposite

private theorem scalar_localization_colimit {R : Type u} [CommRing R] (s : R) :
    let D := Functor.ofSequence (X := fun _ : ℕ ↦ ModuleCat.of R R)
      (fun _ ↦ ModuleCat.ofHom (LinearMap.lsmul R R s))
    ∃ e : colimit D ≅ ModuleCat.of R (Localization.Away s),
      ∀ (m : ℕ) (a : R), e.hom ((colimit.ι D m) a) =
        algebraMap R _ a * IsLocalization.Away.invSelf s ^ m := by
  dsimp only
  obtain ⟨κ, hκ⟩ := ModuleCat.localization_away_colimit s R
  let e := IsLocalizedModule.iso (Submonoid.powers s)
    (Algebra.linearMap R (Localization.Away s))
  have he (a : R) (n : ℕ) :
      e (LocalizedModule.mk (S := Submonoid.powers s) a ⟨s ^ n, ⟨n, rfl⟩⟩) =
        algebraMap R _ a * IsLocalization.Away.invSelf s ^ n := by
    apply (IsLocalization.Away.algebraMap_pow_isUnit
      (S := Localization.Away s) s n).mul_left_cancel
    calc
      _ = e ((s ^ n) • LocalizedModule.mk (S := Submonoid.powers s)
          a ⟨s ^ n, ⟨n, rfl⟩⟩) := by rw [map_smul, Algebra.smul_def, map_pow]
      _ = algebraMap R _ a := by
        rw [LocalizedModule.smul'_mk, ← Submonoid.smul_def (⟨s ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers s),
          LocalizedModule.mk_cancel]
        exact IsLocalizedModule.iso_mk_one _ _ a
      _ = _ := by rw [mul_left_comm, ← mul_pow,
        IsLocalization.Away.mul_invSelf, one_pow, mul_one]
  refine ⟨(κ.trans e).toModuleIso, ?_⟩
  intro n a
  change e (κ ((colimit.ι (Functor.ofSequence (X := fun _ : ℕ ↦
    ModuleCat.of R R) (fun _ ↦ ModuleCat.ofHom (LinearMap.lsmul R R s))) n) a)) = _
  rw [hκ, he]

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C]
variable {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasSheafify J CommRingCat.{u}]
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable (O : Sheaf J CommRingCat.{u})

private def regularScalar
    (s : (O.obj ⋙ forget CommRingCat).sections) :
    End (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
  .of ((SheafOfModules.unitHomEquiv _).symm ⟨s.val, s.property⟩)

private abbrev sectionValue
    (s : (O.obj ⋙ forget CommRingCat).sections) (X : Cᵒᵖ) : O.obj.obj X := s.val X

private abbrev localizationInv
    (s : (O.obj ⋙ forget CommRingCat).sections) (X : Cᵒᵖ) :
    ringedSectionLocalizationCarrierOfUniverses O s X :=
  IsLocalization.Away.invSelf (R := O.obj.obj X) (sectionValue O s X)

private theorem localization_map_inv
    (s : (O.obj ⋙ forget CommRingCat).sections) {X Y : Cᵒᵖ} (g : X ⟶ Y) :
    ringedSectionLocalizationMapOfUniverses O s g
      (localizationInv O s X) =
        localizationInv O s Y := by
  apply (IsLocalization.Away.algebraMap_isUnit
    (R := O.obj.obj Y) (S := ringedSectionLocalizationCarrierOfUniverses O s Y)
      (sectionValue O s Y)).mul_left_cancel
  have hc (a : O.obj.obj X) :
      ringedSectionLocalizationMapOfUniverses O s g (algebraMap _ _ a) =
        algebraMap _ _ (O.obj.map g a) := by
    exact IsLocalization.Away.lift_eq _ _ a
  calc
    _ = ringedSectionLocalizationMapOfUniverses O s g
        (algebraMap _ _ (sectionValue O s X) * localizationInv O s X) := by
      rw [map_mul, hc, show O.obj.map g (sectionValue O s X) =
          sectionValue O s Y from s.property g]
    _ = 1 := by rw [IsLocalization.Away.mul_invSelf, map_one]
    _ = _ := (IsLocalization.Away.mul_invSelf (sectionValue O s Y)).symm

private def fractionMap
    (s : (O.obj ⋙ forget CommRingCat).sections) (n : ℕ) :
    PresheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).obj ⟶
      ringedSectionLocalizationPresheafOfUniverses O s :=
  (ringedSectionLocalizationPresheafOfUniverses O s).unitHomEquiv.symm
    (PresheafOfModules.sectionsMk
      (fun X ↦ localizationInv O s X ^ n)
      (fun {_ _} g ↦ by
        change ringedSectionLocalizationMapOfUniverses O s g _ = _
        rw [map_pow, localization_map_inv]))

private theorem fractionMap_apply
    (s : (O.obj ⋙ forget CommRingCat).sections) (n : ℕ)
    (X : Cᵒᵖ) (a : O.obj.obj X) :
    (fractionMap O s n).app X a =
      algebraMap (O.obj.obj X) (ringedSectionLocalizationCarrierOfUniverses O s X) a *
        localizationInv O s X ^ n := by
  change a • localizationInv O s X ^ n = _
  exact Algebra.smul_def a _

private theorem scalar_apply
    (s : (O.obj ⋙ forget CommRingCat).sections) (X : Cᵒᵖ) (a : O.obj.obj X) :
    (regularScalar O s).asHom.val.app X a = a * sectionValue O s X := by
  change a • sectionValue O s X = _
  rfl

private theorem fractionMap_step
    (s : (O.obj ⋙ forget CommRingCat).sections) (n : ℕ) :
    (regularScalar O s).asHom.val ≫ fractionMap O s (n + 1) = fractionMap O s n := by
  apply PresheafOfModules.hom_ext
  intro X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change O.obj.obj X at a
  change (fractionMap O s (n + 1)).app X ((regularScalar O s).asHom.val.app X a) =
    (fractionMap O s n).app X a
  rw [fractionMap_apply, scalar_apply, fractionMap_apply, map_mul, pow_succ]
  calc
    _ = (algebraMap _ _ a * localizationInv O s X ^ n) *
        (algebraMap _ _ (sectionValue O s X) * localizationInv O s X) := by ring
    _ = _ := by rw [IsLocalization.Away.mul_invSelf, mul_one]

private def localizationPresheafCocone
    (s : (O.obj ⋙ forget CommRingCat).sections) :
    Cocone (Functor.ofSequence (X := fun _ : ℕ ↦
      SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
        (fun _ ↦ (regularScalar O s).asHom) ⋙ SheafOfModules.forget _) where
  pt := ringedSectionLocalizationPresheafOfUniverses O s
  ι := NatTrans.ofSequence (fun n ↦ fractionMap O s n) (by
    intro n
    change ((SheafOfModules.forget _).map
      ((Functor.ofSequence (fun _ ↦ (regularScalar O s).asHom)).map _)) ≫ _ = _ ≫ 𝟙 _
    rw [Functor.ofSequence_map_homOfLE_succ, Category.comp_id]
    exact fractionMap_step O s n)

private def localizationPresheafCoconeIsColimit
    (s : (O.obj ⋙ forget CommRingCat).sections) :
    IsColimit (localizationPresheafCocone O s) := by
  apply PresheafOfModules.evaluationJointlyReflectsColimits
  intro X
  let R := O.obj.obj X
  let D := Functor.ofSequence (X := fun _ : ℕ ↦ ModuleCat.of R R)
    (fun _ ↦ ModuleCat.ofHom (LinearMap.lsmul R R (sectionValue O s X)))
  let c := (PresheafOfModules.evaluation _ X).mapCocone
    (localizationPresheafCocone O s)
  let F := (Functor.ofSequence (fun _ ↦ (regularScalar O s).asHom) ⋙
    SheafOfModules.forget _) ⋙ PresheafOfModules.evaluation _ X
  let t : D ⟶ F := NatTrans.ofSequence (fun _ ↦ 𝟙 (ModuleCat.of R R)) (by
    intro n
    simp only [F, D, Functor.comp_map, Functor.ofSequence_map_homOfLE_succ]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change O.obj.obj X at a
    change (sectionValue O s X) * a = (regularScalar O s).asHom.val.app X a
    rw [scalar_apply, mul_comm])
  let et : D ≅ F := NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intro i j f; exact t.naturality f)
  let e := Classical.choose (scalar_localization_colimit (sectionValue O s X))
  have he := Classical.choose_spec (scalar_localization_colimit (sectionValue O s X))
  change ∀ (m : ℕ) (a : R), e.hom ((colimit.ι D m) a) =
    algebraMap R (Localization.Away (sectionValue O s X)) a *
      IsLocalization.Away.invSelf (sectionValue O s X) ^ m at he
  clear_value e
  apply (IsColimit.precomposeHomEquiv et c).toFun
  apply IsColimit.ofIsoColimit (colimit.isColimit D)
  refine Cocone.ext e ?_
  intro m
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  dsimp only [et, c, Cocone.precompose, localizationPresheafCocone,
    Functor.mapCocone, NatIso.ofComponents, NatTrans.ofSequence] at *
  change e.hom ((colimit.ι D m) a) = (fractionMap O s m).app X a
  rw [he, fractionMap_apply]

private def localizationSheafMap
    (s : (O.obj ⋙ forget CommRingCat).sections) (n : ℕ) :
    SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) ⟶
      ringedSectionLocalizationOfUniverses O s :=
  (SheafOfModules.fullyFaithfulForget _).preimage
    (fractionMap O s n ≫
      (PresheafOfModules.sheafificationAdjunction
        (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).obj)).unit.app _)

private theorem localizationSheafMap_step
    (s : (O.obj ⋙ forget CommRingCat).sections) (n : ℕ) :
    (regularScalar O s).asHom ≫ localizationSheafMap O s (n + 1) =
      localizationSheafMap O s n := by
  apply SheafOfModules.hom_ext
  change (regularScalar O s).asHom.val ≫ (fractionMap O s (n + 1) ≫ _) = _
  rw [← Category.assoc, fractionMap_step]
  rfl

private def localizationSheafCocone
    (s : (O.obj ⋙ forget CommRingCat).sections) :
    Cocone (Functor.ofSequence (X := fun _ : ℕ ↦
      SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
        (fun _ ↦ (regularScalar O s).asHom)) where
  pt := ringedSectionLocalizationOfUniverses O s
  ι := NatTrans.ofSequence (fun n ↦ localizationSheafMap O s n) (by
    intro n
    rw [Functor.ofSequence_map_homOfLE_succ, Functor.const_obj_map]
    change (regularScalar O s).asHom ≫ _ = _ ≫ 𝟙 _
    rw [Category.comp_id]
    exact localizationSheafMap_step O s n)

private def localizationSheafCoconeIsColimit
    (s : (O.obj ⋙ forget CommRingCat).sections) :
    IsColimit (localizationSheafCocone O s) := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).obj)
  let hc := localizationPresheafCoconeIsColimit O s
  clear_value hc
  let U := SheafOfModules.forget ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
  refine { desc := fun t ↦ (adj.homEquiv _ _).symm (hc.desc (U.mapCocone t))
           fac := ?_
           uniq := ?_ }
  · intro t n
    apply U.map_injective
    change (fractionMap O s n ≫ adj.unit.app _) ≫
      U.map ((adj.homEquiv _ _).symm (hc.desc (U.mapCocone t))) = _
    rw [Category.assoc]
    erw [← Adjunction.homEquiv_unit, Equiv.apply_symm_apply]
    exact hc.fac (U.mapCocone t) n
  · intro t m hm
    apply (adj.homEquiv _ _).injective
    rw [Equiv.apply_symm_apply]
    apply hc.hom_ext
    intro n
    rw [hc.fac]
    change fractionMap O s n ≫ (adj.homEquiv _ _ m) = _
    rw [Adjunction.homEquiv_unit, ← Category.assoc]
    exact congrArg (fun f ↦ U.map f) (hm n)

private theorem localizationSheafMap_zero
    (s : (O.obj ⋙ forget CommRingCat).sections) :
    localizationSheafMap O s 0 = ringedSectionLocalizationUnitOfUniverses O s := by
  unfold localizationSheafMap ringedSectionLocalizationUnitOfUniverses
  congr 2

end LocalizationSequence

section ScalarMaps

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C]
variable {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasSheafify J CommRingCat.{u}]
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

private def localizationScalar (R : Sheaf J CommRingCat.{u})
    (t : (R.obj ⋙ forget CommRingCat.{u}).sections) (M : inverseLocalizationModules R) :
    M ⟶ M :=
  ⟨{ app := fun U ↦ ModuleCat.ofHom (LinearMap.lsmul (R.obj.obj U) (M.val.obj U) (t.val U))
     naturality := by
       intro U V f
       ext m
       change (t.val V : R.obj.obj V) • (show M.val.obj V from M.val.map f m) =
         M.val.map f ((t.val U : R.obj.obj U) • m)
       rw [M.val.map_smul]
       have ht : R.obj.map f (t.val U) = t.val V := t.property f
       change (t.val V : R.obj.obj V) • (show M.val.obj V from M.val.map f m) =
         R.obj.map f (t.val U) • (show M.val.obj V from M.val.map f m)
       rw [ht] }⟩

private theorem localizationSets_preserves_sequence (R : Sheaf J CommRingCat.{u}) :
    PreservesColimitsOfShape ℕ (localizationModuleSets R) := by
  let O := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R
  have : ∀ X : Cᵒᵖ,
      HasLimitsOfShape (StructuredArrow X (equivSmallModel.{u} C).inverse.op) (Type u) :=
    fun _ ↦ hasLimitsOfShape_of_essentiallySmall.{u} _ _
  have : HasSheafify J (Type u) := hasSheafifyEssentiallySmallSite J _
  have : PreservesColimitsOfSize.{u, u} (SheafOfModules.toSheaf.{u} O) := by
    constructor
    intro T _
    exact ((moduleSheaves_colimits_forgetful O).2.2.2.2.2 T).2.1
  have : PreservesColimitsOfShape ℕ (SheafOfModules.toSheaf.{u} O) :=
    (preservesColimitsOfSize_shrink (SheafOfModules.toSheaf.{u} O)).preservesColimitsOfShape
  have : PreservesFilteredColimitsOfSize.{0, 0} (forget AddCommGrpCat.{u}) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  have : J.PreservesSheafification (forget AddCommGrpCat.{u}) := inferInstance
  have : PreservesColimitsOfShape ℕ (sheafCompose J (forget AddCommGrpCat.{u})) := by
    rw [(sheafificationAdjunction J AddCommGrpCat.{u}).preservesColimitsOfShape_iff]
    exact preservesColimitsOfShape_of_natIso
      (sheafComposeNatIso J (forget AddCommGrpCat.{u})
        (sheafificationAdjunction J AddCommGrpCat.{u}) (sheafificationAdjunction J (Type u)))
  exact comp_preservesColimitsOfShape _ _

end ScalarMaps

private theorem inverseImage_preserves_sequence
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify J CommRingCat.{u}]
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [HasSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify K CommRingCat.{u}]
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {L : Sheaf J (Type u) ⥤ Sheaf K (Type u)}
    {V : Sheaf K (Type u) ⥤ Sheaf J (Type u)} (adj : L ⊣ V)
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (a : SheafOfModules.AlgebraicInverseImage L R S) :
    PreservesColimitsOfShape ℕ a.modules := by
  have : PreservesColimitsOfShape ℕ L := adj.leftAdjoint_preservesColimits.preservesColimitsOfShape
  have := localizationSets_preserves_sequence R
  have := localizationSets_preserves_sequence S
  have : PreservesColimitsOfShape ℕ (a.modules ⋙ localizationModuleSets S) :=
    preservesColimitsOfShape_of_natIso a.moduleUnderlying.symm
  have : ReflectsColimitsOfShape ℕ (localizationModuleSets S) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  exact preservesColimitsOfShape_of_reflects_of_preserves a.modules (localizationModuleSets S)

private theorem inverseImage_scalar
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify J CommRingCat.{u}]
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [HasSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify K CommRingCat.{u}]
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {L : Sheaf J (Type u) ⥤ Sheaf K (Type u)}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (a : SheafOfModules.AlgebraicInverseImage L R S)
    (t : (R.obj ⋙ forget CommRingCat.{u}).sections)
    (s : (S.obj ⋙ forget CommRingCat.{u}).sections) (hs : IsInverseImageSection a t s)
    (M : inverseLocalizationModules R) :
    a.modules.map (localizationScalar R t M) = localizationScalar S s (a.modules.obj M) := by
  let T := (localizationModuleSets R).obj M
  let r : T ⟶ (sheafCompose J (forget CommRingCat.{u})).obj R :=
    ⟨{ app := fun U ↦ TypeCat.ofHom (fun _ ↦ t.val U)
       naturality := by
         intro U V f
         ext x
         exact (t.property f).symm }⟩
  have h := a.moduleSMul M T r (𝟙 T)
    ((localizationModuleSets R).map (localizationScalar R t M)) (by intro U x; rfl)
  apply (localizationModuleSets S).map_injective
  apply (cancel_epi (a.moduleUnderlying.inv.app M)).1
  ext W x
  have hn := congrArg (fun f ↦ f.hom.app W x)
    (a.moduleUnderlying.inv.naturality (localizationScalar R t M))
  change (a.moduleUnderlying.inv.app M).hom.app W
      ((L.map ((localizationModuleSets R).map (localizationScalar R t M))).hom.app W x) =
    (a.modules.map (localizationScalar R t M)).val.app W
      ((a.moduleUnderlying.inv.app M).hom.app W x) at hn
  change (a.modules.map (localizationScalar R t M)).val.app W
      ((a.moduleUnderlying.inv.app M).hom.app W x) = _
  rw [← hn]
  have hh := h W x
  dsimp only [id_eq] at hh
  rw [hs T r (by intro U x; rfl) W x, L.map_id] at hh
  exact hh

namespace LocalizationSequence

open MonoidalCategory
set_option linter.unusedSectionVars false

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C]
variable {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasSheafify J CommRingCat.{u}]
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable (R : Sheaf J CommRingCat.{u}) (t : (R.obj ⋙ forget CommRingCat.{u}).sections)

private def tensorModelIso (M : inverseLocalizationModules R) :
    (PresheafOfModules.sheafification
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).obj
        (M.val ⊗ ringedSectionLocalizationPresheafOfUniverses R t) ≅
      (scalarLocalization R t).obj M := by
  let O := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R
  let P := ringedSectionLocalizationPresheafOfUniverses R t
  let F := PresheafOfModules.sheafification (R := O) (𝟙 O.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (R := O) (𝟙 O.obj)
  let W := J.W.inverseImage (PresheafOfModules.toPresheaf.{u} O.obj)
  have hη : W (adj.unit.app P) := by
    change J.W ((PresheafOfModules.toPresheaf O.obj).map (adj.unit.app P))
    rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    exact J.W_toSheafify P.presheaf
  have hk : W (M.val ◁ adj.unit.app P) := W.whiskerLeft_mem M.val _ hη
  dsimp only [W] at hk
  rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
    (R := O) (𝟙 O.obj)] at hk
  have : IsIso (F.map (M.val ◁ adj.unit.app P)) := hk
  exact asIso (F.map (M.val ◁ adj.unit.app P)) ≪≫
    F.mapIso ((SheafOfModules.siteTensorRightIso R (F.obj P).val).app M.val).symm

private theorem tensorModelIso_tmul (M : inverseLocalizationModules R)
    (U : Cᵒᵖ) (m : M.val.obj U)
    (p : ringedSectionLocalizationCarrierOfUniverses R t U) :
    (tensorModelIso R t M).hom.val.app U
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).unit.app
          (M.val ⊗ ringedSectionLocalizationPresheafOfUniverses R t)).app U
            (m ⊗ₜ[R.obj.obj U] p)) =
      SheafOfModules.siteSheafTensorTmul M (ringedSectionLocalizationOfUniverses R t) U m
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).unit.app
          (ringedSectionLocalizationPresheafOfUniverses R t)).app U p) := by
  let O := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R
  let F := PresheafOfModules.sheafification (R := O) (𝟙 O.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (R := O) (𝟙 O.obj)
  let P := ringedSectionLocalizationPresheafOfUniverses R t
  let k := (M.val ◁ adj.unit.app P) ≫
    ((SheafOfModules.siteTensorRightIso R (F.obj P).val).app M.val).inv
  have hn := congrArg (fun f ↦ f.app U (m ⊗ₜ[R.obj.obj U] p)) (adj.unit.naturality k).symm
  change (F.map k).val.app U ((adj.unit.app (M.val ⊗ P)).app U
    (m ⊗ₜ[R.obj.obj U] p)) = _ at hn
  apply (show (tensorModelIso R t M).hom = F.map k by
    simp only [tensorModelIso, k, F.map_comp, Iso.trans_hom, asIso_hom,
      Functor.mapIso_hom, Iso.symm_hom]
    rfl) ▸ hn

private def modulePresheafCocone (M : inverseLocalizationModules R) :
    Cocone (Functor.ofSequence (X := fun _ : ℕ ↦ M)
      (fun _ ↦ localizationScalar R t M) ⋙ SheafOfModules.forget _) := by
  let X := SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
  let D := Functor.ofSequence (X := fun _ : ℕ ↦ M) (fun _ ↦ localizationScalar R t M)
  let E := Functor.ofSequence (X := fun _ : ℕ ↦ X) (fun _ ↦ (regularScalar R t).asHom)
  let F := tensorLeft M.val
  let ε : D ⋙ SheafOfModules.forget _ ≅
      (E ⋙ SheafOfModules.forget _) ⋙ F := by
    let τ : D ⋙ SheafOfModules.forget _ ⟶
        (E ⋙ SheafOfModules.forget _) ⋙ F :=
      NatTrans.ofSequence (fun _ ↦ (ρ_ M.val).inv) (by
        intro n
        simp only [D, E, Functor.comp_map, Functor.ofSequence_map_homOfLE_succ]
        ext U m
        change (sectionValue R t U • m) ⊗ₜ[R.obj.obj U] (1 : R.obj.obj U) =
          m ⊗ₜ[R.obj.obj U] ((regularScalar R t).asHom.val.app U (1 : R.obj.obj U))
        rw [scalar_apply, one_mul]
        simpa only [smul_eq_mul, mul_one] using
          (TensorProduct.smul_tmul (R := R.obj.obj U) (sectionValue R t U) m
            (1 : R.obj.obj U)))
    exact NatIso.ofComponents (fun _ ↦ (ρ_ M.val).symm) (fun f ↦ τ.naturality f)
  exact (Cocone.precompose ε.hom).obj (F.mapCocone (localizationPresheafCocone R t))

private def modulePresheafCoconeIsColimit (M : inverseLocalizationModules R) :
    IsColimit (modulePresheafCocone R t M) := by
  have : PreservesColimitsOfSize.{u, u} (tensorLeft M.val) := by
    change PreservesColimitsOfSize.{u, u} (tensorLeft
      (show PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat) from M.val))
    infer_instance
  have : PreservesColimitsOfSize.{0, 0} (tensorLeft M.val) :=
    preservesColimitsOfSize_shrink (tensorLeft M.val)
  unfold modulePresheafCocone
  exact (IsColimit.precomposeHomEquiv _ _).symm
    (isColimitOfPreserves _ (localizationPresheafCoconeIsColimit R t))

private theorem modulePresheafCocone_zero (M : inverseLocalizationModules R)
    (U : Cᵒᵖ) (m : M.val.obj U) :
    ((modulePresheafCocone R t M).ι.app 0).app U m =
      m ⊗ₜ[R.obj.obj U]
        (1 : ringedSectionLocalizationCarrierOfUniverses R t U) := by
  change m ⊗ₜ[R.obj.obj U] ((fractionMap R t 0).app U (1 : R.obj.obj U)) = _
  congr 1
  rw [fractionMap_apply]
  simp

end LocalizationSequence

namespace LocalizationSequence

set_option linter.unusedSectionVars false
variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C]
variable {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasSheafify J CommRingCat.{u}]
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable (R : Sheaf J CommRingCat.{u}) (t : (R.obj ⋙ forget CommRingCat.{u}).sections)

private def moduleSheafCocone (M : inverseLocalizationModules R) :
    Cocone (Functor.ofSequence (X := fun _ : ℕ ↦ M)
      (fun _ ↦ localizationScalar R t M)) := by
  let c := modulePresheafCocone R t M
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  exact
    { pt := (scalarLocalization R t).obj M
      ι :=
        { app := fun n ↦
            (show M ⟶ (PresheafOfModules.sheafification
              (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).obj c.pt from
              ⟨c.ι.app n ≫ adj.unit.app c.pt⟩) ≫ (tensorModelIso R t M).hom
          naturality := by
            intro n k f
            apply SheafOfModules.hom_ext
            change
              ((Functor.ofSequence (X := fun _ : ℕ ↦ M)
                (fun _ ↦ localizationScalar R t M)).map f).val ≫
                  ((c.ι.app k ≫ adj.unit.app c.pt) ≫ (tensorModelIso R t M).hom.val) =
                (c.ι.app n ≫ adj.unit.app c.pt) ≫ (tensorModelIso R t M).hom.val
            rw [← Category.assoc, ← Category.assoc]
            exact congrArg (fun h ↦ (h ≫ adj.unit.app c.pt) ≫
              (tensorModelIso R t M).hom.val) (c.w f) } }

private def moduleSheafCoconeIsColimit (M : inverseLocalizationModules R) :
    IsColimit (moduleSheafCocone R t M) := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  let c := modulePresheafCocone R t M
  let hc := modulePresheafCoconeIsColimit R t M
  let U := SheafOfModules.forget ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
  let e := tensorModelIso R t M
  let F := PresheafOfModules.sheafification
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  refine
    { desc := fun d ↦ e.inv ≫ (adj.homEquiv _ _).symm (hc.desc (U.mapCocone d))
      fac := ?_
      uniq := ?_ }
  · intro d n
    change ((show M ⟶ F.obj c.pt from ⟨c.ι.app n ≫ adj.unit.app c.pt⟩) ≫ e.hom) ≫
      (e.inv ≫ _) = _
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    apply U.map_injective
    change (c.ι.app n ≫ adj.unit.app c.pt) ≫
      U.map ((adj.homEquiv _ _).symm (hc.desc (U.mapCocone d))) = _
    rw [Category.assoc]
    erw [← Adjunction.homEquiv_unit, Equiv.apply_symm_apply]
    exact hc.fac (U.mapCocone d) n
  · intro d f hf
    apply (cancel_epi e.hom).1
    simp only [Iso.hom_inv_id_assoc]
    apply (adj.homEquiv _ _).injective
    rw [Equiv.apply_symm_apply]
    apply hc.hom_ext
    intro n
    rw [hc.fac]
    change c.ι.app n ≫ adj.homEquiv _ _ (e.hom ≫ f) = _
    rw [Adjunction.homEquiv_unit, ← Category.assoc]
    have hh := congrArg (fun g ↦ U.map g) (hf n)
    change ((c.ι.app n ≫ adj.unit.app c.pt) ≫ e.hom.val) ≫ f.val = _ at hh
    apply PresheafOfModules.hom_ext
    intro X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    exact congrArg (fun g ↦ g.app X m) hh

private theorem moduleSheafCocone_zero (M : inverseLocalizationModules R) :
    (moduleSheafCocone R t M).ι.app 0 = (scalarLocalizationUnit R t).app M := by
  apply SheafOfModules.hom_ext
  ext U m
  change (tensorModelIso R t M).hom.val.app U
    (((PresheafOfModules.sheafificationAdjunction
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).unit.app
      (modulePresheafCocone R t M).pt).app U
        (((modulePresheafCocone R t M).ι.app 0).app U m)) = _
  rw [modulePresheafCocone_zero]
  refine (tensorModelIso_tmul R t M U m 1).trans ?_
  convert (Classical.choose_spec (existsUnique_scalarLocalizationUnit R t)).1 M U m |>.symm
    using 1
  · congr 1
    change _ = ((PresheafOfModules.sheafificationAdjunction
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).unit.app
        (ringedSectionLocalizationPresheafOfUniverses R t)).app U
          ((1 : R.obj.obj U) • (1 : ringedSectionLocalizationCarrierOfUniverses R t U))
    rw [one_smul]
  · rfl

private theorem scalar_naturality {M N : inverseLocalizationModules R} (f : M ⟶ N) :
    localizationScalar R t M ≫ f = f ≫ localizationScalar R t N := by
  ext U m
  exact (f.val.app U).hom.map_smul (sectionValue R t U) m

private theorem colimit_hom_ext_zero
    {M N : inverseLocalizationModules R}
    (c : Cocone (Functor.ofSequence (X := fun _ : ℕ ↦ M)
      (fun _ ↦ localizationScalar R t M))) (hc : IsColimit c)
    [Mono (localizationScalar R t N)] (f g : c.pt ⟶ N)
    (h : c.ι.app 0 ≫ f = c.ι.app 0 ≫ g) : f = g := by
  apply hc.hom_ext
  intro n
  induction n with
  | zero => exact h
  | succ n ih =>
      apply (cancel_mono (localizationScalar R t N)).1
      have hw := c.w (homOfLE (Nat.le_succ n))
      simp only [Functor.ofSequence_map_homOfLE_succ] at hw
      calc
        _ = localizationScalar R t M ≫ (c.ι.app (n + 1) ≫ f) :=
          (scalar_naturality R t (c.ι.app (n + 1) ≫ f)).symm
        _ = c.ι.app n ≫ f := by rw [← Category.assoc, hw]
        _ = c.ι.app n ≫ g := ih
        _ = localizationScalar R t M ≫ (c.ι.app (n + 1) ≫ g) := by
          rw [← Category.assoc, hw]
        _ = _ := scalar_naturality R t (c.ι.app (n + 1) ≫ g)

private theorem colimit_scalar_isIso
    {M : inverseLocalizationModules R}
    (c : Cocone (Functor.ofSequence (X := fun _ : ℕ ↦ M)
      (fun _ ↦ localizationScalar R t M))) (hc : IsColimit c) :
    IsIso (localizationScalar R t c.pt) := by
  let d : Cocone (Functor.ofSequence (X := fun _ : ℕ ↦ M)
      (fun _ ↦ localizationScalar R t M)) :=
    { pt := c.pt
      ι := NatTrans.ofSequence (fun n ↦ c.ι.app (n + 1)) (by
        intro n
        simp only [Functor.ofSequence_map_homOfLE_succ, Functor.const_obj_map]
        have h := c.w (homOfLE (Nat.le_succ (n + 1)))
        rw [Functor.ofSequence_map_homOfLE_succ] at h
        exact h.trans (Category.comp_id _).symm) }
  have hstep (n : ℕ) : localizationScalar R t M ≫ c.ι.app (n + 1) = c.ι.app n := by
    have h := c.w (homOfLE (Nat.le_succ n))
    rw [Functor.ofSequence_map_homOfLE_succ] at h
    exact h
  refine ⟨⟨hc.desc d, ?_, ?_⟩⟩
  · apply hc.hom_ext
    intro n
    calc
      _ = (c.ι.app n ≫ localizationScalar R t c.pt) ≫ hc.desc d :=
        (Category.assoc _ _ _).symm
      _ = (localizationScalar R t M ≫ c.ι.app n) ≫ hc.desc d := by
        rw [scalar_naturality R t (show M ⟶ c.pt from c.ι.app n)]
      _ = localizationScalar R t M ≫ c.ι.app (n + 1) := by
        rw [Category.assoc, hc.fac]; rfl
      _ = c.ι.app n ≫ 𝟙 _ := (hstep n).trans (Category.comp_id _).symm
  · apply hc.hom_ext
    intro n
    calc
      _ = c.ι.app (n + 1) ≫ localizationScalar R t c.pt := by
        rw [← Category.assoc, hc.fac]; rfl
      _ = localizationScalar R t M ≫ c.ι.app (n + 1) :=
        (scalar_naturality R t (show M ⟶ c.pt from c.ι.app (n + 1))).symm
      _ = c.ι.app n ≫ 𝟙 _ := (hstep n).trans (Category.comp_id _).symm

end LocalizationSequence

namespace LocalizationSequence

set_option linter.unusedSectionVars false
variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
variable [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasSheafify J CommRingCat.{u}]
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasSheafify K CommRingCat.{u}]
variable [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable {L : Sheaf J (Type u) ⥤ Sheaf K (Type u)}
variable {V : Sheaf K (Type u) ⥤ Sheaf J (Type u)} (adj : L ⊣ V)
variable {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
variable (a : SheafOfModules.AlgebraicInverseImage L R S)
variable (t : (R.obj ⋙ forget CommRingCat.{u}).sections)
variable (s : (S.obj ⋙ forget CommRingCat.{u}).sections) (hs : IsInverseImageSection a t s)

private def imageCocone (M : inverseLocalizationModules R) :
    Cocone (Functor.ofSequence (X := fun _ : ℕ ↦ a.modules.obj M)
      (fun _ ↦ localizationScalar S s (a.modules.obj M))) := by
  let T := Functor.ofSequence (X := fun _ : ℕ ↦ a.modules.obj M)
    (fun _ ↦ localizationScalar S s (a.modules.obj M))
  let D := Functor.ofSequence (X := fun _ : ℕ ↦ M) (fun _ ↦ localizationScalar R t M)
  let τ : T ⟶ D ⋙ a.modules := NatTrans.ofSequence (fun _ ↦ 𝟙 _) (by
    intro n
    simpa only [T, D, Functor.comp_map, Functor.ofSequence_map_homOfLE_succ,
      Category.id_comp, Category.comp_id] using (inverseImage_scalar a t s hs M).symm)
  let e : T ≅ D ⋙ a.modules :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun f ↦ τ.naturality f)
  exact (Cocone.precompose e.hom).obj (a.modules.mapCocone (moduleSheafCocone R t M))

private def imageCoconeIsColimit (M : inverseLocalizationModules R) :
    IsColimit (imageCocone a t s hs M) := by
  have := inverseImage_preserves_sequence adj a
  unfold imageCocone
  exact (IsColimit.precomposeHomEquiv _ _).symm
    (isColimitOfPreserves _ (moduleSheafCoconeIsColimit R t M))

private theorem imageCocone_zero (M : inverseLocalizationModules R) :
    (imageCocone a t s hs M).ι.app 0 = a.modules.map ((scalarLocalizationUnit R t).app M) := by
  change (𝟙 _) ≫ a.modules.map ((moduleSheafCocone R t M).ι.app 0) = _
  rw [Category.id_comp, moduleSheafCocone_zero]

private def comparison (M : inverseLocalizationModules R) :
    a.modules.obj ((scalarLocalization R t).obj M) ≅
      (scalarLocalization S s).obj (a.modules.obj M) :=
  (imageCoconeIsColimit adj a t s hs M).coconePointUniqueUpToIso
    (moduleSheafCoconeIsColimit S s (a.modules.obj M))

private theorem comparison_unit (M : inverseLocalizationModules R) :
    a.modules.map ((scalarLocalizationUnit R t).app M) ≫ (comparison adj a t s hs M).hom =
      (scalarLocalizationUnit S s).app (a.modules.obj M) := by
  rw [← imageCocone_zero a t s hs M, comparison,
    IsColimit.comp_coconePointUniqueUpToIso_hom, moduleSheafCocone_zero]

private theorem comparison_naturality {M N : inverseLocalizationModules R} (f : M ⟶ N) :
    a.modules.map ((scalarLocalization R t).map f) ≫ (comparison adj a t s hs N).hom =
      (comparison adj a t s hs M).hom ≫ (scalarLocalization S s).map (a.modules.map f) := by
  have : IsIso (localizationScalar S s ((scalarLocalization S s).obj (a.modules.obj N))) :=
    colimit_scalar_isIso S s (moduleSheafCocone S s (a.modules.obj N))
      (moduleSheafCoconeIsColimit S s (a.modules.obj N))
  apply colimit_hom_ext_zero S s (imageCocone a t s hs M)
    (imageCoconeIsColimit adj a t s hs M)
  rw [imageCocone_zero]
  calc
    _ = a.modules.map (((scalarLocalizationUnit R t).app M) ≫
        (scalarLocalization R t).map f) ≫ (comparison adj a t s hs N).hom := by
      simp only [Functor.map_comp, Category.assoc]
    _ = a.modules.map (f ≫ (scalarLocalizationUnit R t).app N) ≫
        (comparison adj a t s hs N).hom := by
      rw [← (scalarLocalizationUnit R t).naturality f]
      rfl
    _ = a.modules.map f ≫ (scalarLocalizationUnit S s).app (a.modules.obj N) := by
      rw [Functor.map_comp, Category.assoc, comparison_unit]
    _ = (scalarLocalizationUnit S s).app (a.modules.obj M) ≫
        (scalarLocalization S s).map (a.modules.map f) :=
      (scalarLocalizationUnit S s).naturality (a.modules.map f)
    _ = _ := by rw [← comparison_unit adj a t s hs M, Category.assoc]

end LocalizationSequence

namespace LocalizationRings

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency.types false

open MonoidalCategory CartesianMonoidalCategory

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]

private abbrev sets (R : Sheaf J CommRingCat.{u}) :=
  (sheafCompose J (forget CommRingCat.{u})).obj R

private def constMap (R : Sheaf J CommRingCat.{u})
    (t : (R.obj ⋙ forget CommRingCat.{u}).sections) (T : Sheaf J (Type u)) : T ⟶ sets R :=
  ⟨{ app := fun U ↦ ↾(fun _ ↦ t.val U)
     naturality := by intro U V f; ext x; exact (t.property f).symm }⟩

private def addMap (R : Sheaf J CommRingCat.{u}) : sets R ⊗ sets R ⟶ sets R :=
  ⟨{ app := fun U ↦ ↾(fun x ↦ @Add.add (R.obj.obj U) inferInstance x.1 x.2)
     naturality := by intro U V f; ext x; exact ((R.obj.map f).hom.map_add _ _).symm }⟩

private def mulMap (R : Sheaf J CommRingCat.{u}) : sets R ⊗ sets R ⟶ sets R :=
  ⟨{ app := fun U ↦ ↾(fun x ↦ @Mul.mul (R.obj.obj U) inferInstance x.1 x.2)
     naturality := by intro U V f; ext x; exact ((R.obj.map f).hom.map_mul _ _).symm }⟩

variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable {L : Sheaf J (Type u) ⥤ Sheaf K (Type u)} [PreservesFiniteLimits L]
variable {R Q : Sheaf J CommRingCat.{u}} {S A : Sheaf K CommRingCat.{u}}
variable (a : SheafOfModules.AlgebraicInverseImage L R S)
variable (b : SheafOfModules.AlgebraicInverseImage L Q A) (f : R ⟶ Q)

private def transportSets : sets S ⟶ sets A :=
  a.ringUnderlying.inv ≫ L.map ((sheafCompose J (forget CommRingCat.{u})).map f) ≫
    b.ringUnderlying.hom

private theorem transportSets_apply (T : Sheaf J (Type u)) (r : T ⟶ sets R)
    (W : Dᵒᵖ) (x : (L.obj T).obj.obj W) :
    (transportSets a b f).hom.app W
      (a.ringUnderlying.hom.hom.app W ((L.map r).hom.app W x)) =
    b.ringUnderlying.hom.hom.app W
      ((L.map (r ≫ (sheafCompose J (forget CommRingCat.{u})).map f)).hom.app W x) := by
  have h : a.ringUnderlying.hom ≫ transportSets a b f =
      L.map ((sheafCompose J (forget CommRingCat.{u})).map f) ≫ b.ringUnderlying.hom := by
    simp only [transportSets, Iso.hom_inv_id_assoc]
  have hh := congrArg (fun g ↦ g.hom.app W x) (congrArg (fun g ↦ L.map r ≫ g) h)
  change (transportSets a b f).hom.app W
    (a.ringUnderlying.hom.hom.app W ((L.map r).hom.app W x)) =
      b.ringUnderlying.hom.hom.app W
        ((L.map r ≫ L.map ((sheafCompose J (forget CommRingCat.{u})).map f)).hom.app W x) at hh
  simpa only [Functor.map_comp] using hh

private theorem transportSets_add (W : Dᵒᵖ) (x y : S.obj.obj W) :
    @id (A.obj.obj W) ((transportSets a b f).hom.app W (x + y)) =
      @id (A.obj.obj W) ((transportSets a b f).hom.app W x) +
        @id (A.obj.obj W) ((transportSets a b f).hom.app W y) := by
  let X := sets R
  let p := inv (CartesianMonoidalCategory.prodComparison L X X)
  let z := p.hom.app W (a.ringUnderlying.inv.hom.app W x,
    a.ringUnderlying.inv.hom.app W y)
  have h₁ : (L.map (fst X X)).hom.app W z = a.ringUnderlying.inv.hom.app W x :=
    congrArg (fun g ↦ g.hom.app W
      (a.ringUnderlying.inv.hom.app W x, a.ringUnderlying.inv.hom.app W y))
      (inv_prodComparison_map_fst L X X)
  have h₂ : (L.map (snd X X)).hom.app W z = a.ringUnderlying.inv.hom.app W y :=
    congrArg (fun g ↦ g.hom.app W
      (a.ringUnderlying.inv.hom.app W x, a.ringUnderlying.inv.hom.app W y))
      (inv_prodComparison_map_snd L X X)
  have hi (r : S.obj.obj W) :
      a.ringUnderlying.hom.hom.app W (a.ringUnderlying.inv.hom.app W r) = r :=
    congrArg (fun g ↦ g.hom.app W r) a.ringUnderlying.inv_hom_id
  have ha := a.ringAdd (X ⊗ X) (fst X X) (snd X X) (addMap R) (fun _ _ ↦ rfl) W z
  rw [h₁, h₂, hi, hi] at ha
  dsimp only [id] at ha ⊢
  rw [← ha, transportSets_apply]
  have hb := b.ringAdd (X ⊗ X)
    (fst X X ≫ (sheafCompose J (forget CommRingCat.{u})).map f)
    (snd X X ≫ (sheafCompose J (forget CommRingCat.{u})).map f)
    (addMap R ≫ (sheafCompose J (forget CommRingCat.{u})).map f)
    (fun U z ↦ (f.hom.app U).hom.map_add z.1 z.2) W z
  dsimp only [id] at hb
  rw [hb, ← transportSets_apply a b f, ← transportSets_apply a b f,
    h₁, h₂, hi, hi]

private theorem transportSets_mul (W : Dᵒᵖ) (x y : S.obj.obj W) :
    @id (A.obj.obj W) ((transportSets a b f).hom.app W (x * y)) =
      @id (A.obj.obj W) ((transportSets a b f).hom.app W x) *
        @id (A.obj.obj W) ((transportSets a b f).hom.app W y) := by
  let X := sets R
  let p := inv (CartesianMonoidalCategory.prodComparison L X X)
  let z := p.hom.app W (a.ringUnderlying.inv.hom.app W x,
    a.ringUnderlying.inv.hom.app W y)
  have h₁ : (L.map (fst X X)).hom.app W z = a.ringUnderlying.inv.hom.app W x :=
    congrArg (fun g ↦ g.hom.app W
      (a.ringUnderlying.inv.hom.app W x, a.ringUnderlying.inv.hom.app W y))
      (inv_prodComparison_map_fst L X X)
  have h₂ : (L.map (snd X X)).hom.app W z = a.ringUnderlying.inv.hom.app W y :=
    congrArg (fun g ↦ g.hom.app W
      (a.ringUnderlying.inv.hom.app W x, a.ringUnderlying.inv.hom.app W y))
      (inv_prodComparison_map_snd L X X)
  have hi (r : S.obj.obj W) :
      a.ringUnderlying.hom.hom.app W (a.ringUnderlying.inv.hom.app W r) = r :=
    congrArg (fun g ↦ g.hom.app W r) a.ringUnderlying.inv_hom_id
  have ha := a.ringMul (X ⊗ X) (fst X X) (snd X X) (mulMap R) (fun _ _ ↦ rfl) W z
  rw [h₁, h₂, hi, hi] at ha
  dsimp only [id] at ha ⊢
  rw [← ha, transportSets_apply]
  have hb := b.ringMul (X ⊗ X)
    (fst X X ≫ (sheafCompose J (forget CommRingCat.{u})).map f)
    (snd X X ≫ (sheafCompose J (forget CommRingCat.{u})).map f)
    (mulMap R ≫ (sheafCompose J (forget CommRingCat.{u})).map f)
    (fun U z ↦ (f.hom.app U).hom.map_mul z.1 z.2) W z
  dsimp only [id] at hb
  rw [hb, ← transportSets_apply a b f, ← transportSets_apply a b f,
    h₁, h₂, hi, hi]

private theorem transportSets_one (W : Dᵒᵖ) :
    (transportSets a b f).hom.app W (1 : S.obj.obj W) = (1 : A.obj.obj W) := by
  let r : sets R ⟶ sets R :=
    ⟨{ app := fun U ↦ ↾(fun _ ↦ (1 : R.obj.obj U))
       naturality := by intro U V f; ext x; exact (map_one (R.obj.map f).hom).symm }⟩
  let z := a.ringUnderlying.inv.hom.app W (0 : S.obj.obj W)
  have ha := a.ringOne (sets R) r (fun _ _ ↦ rfl) W z
  dsimp only [id] at ha
  rw [← ha, transportSets_apply]
  exact b.ringOne (sets R) (r ≫ (sheafCompose J (forget CommRingCat.{u})).map f)
    (fun U _ ↦ map_one (f.hom.app U).hom) W z

private def transportHom : S ⟶ A :=
  ⟨{ app := fun W ↦ CommRingCat.ofHom
       { toFun := (transportSets a b f).hom.app W
         map_one' := transportSets_one a b f W
         map_mul' := transportSets_mul a b f W
         map_zero' := by
           have h := transportSets_add a b f W 0 0
           simp only [add_zero, id_eq] at h
           exact (add_left_cancel ((add_zero _).trans h)).symm
         map_add' := transportSets_add a b f W }
     naturality := by
       intro U V g
       ext x
       exact ConcreteCategory.congr_hom ((transportSets a b f).hom.naturality g) x }⟩

end LocalizationRings

namespace LocalizationRings

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency.types false

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C]
variable {J : GrothendieckTopology C} [HasSheafify J CommRingCat.{u}]
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable (R : Sheaf J CommRingCat.{u})
variable (t : (R.obj ⋙ forget CommRingCat.{u}).sections)

private theorem hom_ext {A : Sheaf J CommRingCat.{u}}
    (f g : ringedLocalizationRingOfUniverses R t ⟶ A)
    (h : ringedLocalizationRingUnitOfUniverses R t ≫ f =
      ringedLocalizationRingUnitOfUniverses R t ≫ g) : f = g := by
  apply ((sheafificationAdjunction J CommRingCat.{u}).homEquiv _ _).injective
  apply NatTrans.ext
  funext U
  apply CommRingCat.hom_ext
  apply IsLocalization.ringHom_ext (R := R.obj.obj U)
    (S := ringedSectionLocalizationCarrierOfUniverses R t U)
    (Submonoid.powers (show R.obj.obj U from t.val U))
  ext r
  exact congrArg (fun k ↦ k.hom.app U r) h

private def lift {A : Sheaf J CommRingCat.{u}} (c : R ⟶ A)
    (hu : ∀ U, IsUnit (c.hom.app U (t.val U))) :
    ringedLocalizationRingOfUniverses R t ⟶ A := by
  let f : ringedLocalizationRingPresheafOfUniverses R t ⟶ A.obj :=
    { app := fun U ↦ CommRingCat.ofHom (IsLocalization.Away.lift (R := R.obj.obj U)
        (S := ringedSectionLocalizationCarrierOfUniverses R t U)
        (g := (c.hom.app U).hom) (t.val U) (hu U))
      naturality := by
        intro U V g
        apply CommRingCat.hom_ext
        apply IsLocalization.ringHom_ext (R := R.obj.obj U)
          (S := ringedSectionLocalizationCarrierOfUniverses R t U)
          (Submonoid.powers (show R.obj.obj U from t.val U))
        ext r
        change IsLocalization.Away.lift (R := R.obj.obj V)
            (S := ringedSectionLocalizationCarrierOfUniverses R t V)
            (g := (c.hom.app V).hom) (t.val V) (hu V)
            ((ringedSectionLocalizationMapOfUniverses R t g)
              (algebraMap _ (ringedSectionLocalizationCarrierOfUniverses R t U) r)) =
          A.obj.map g (IsLocalization.Away.lift (R := R.obj.obj U)
            (S := ringedSectionLocalizationCarrierOfUniverses R t U)
            (g := (c.hom.app U).hom) (t.val U) (hu U)
            (algebraMap _ (ringedSectionLocalizationCarrierOfUniverses R t U) r))
        simp only [ringedSectionLocalizationMapOfUniverses, IsLocalization.Away.lift_eq,
          RingHom.comp_apply]
        exact congrArg (fun k ↦ k r) (c.hom.naturality g) }
  exact ((sheafificationAdjunction J CommRingCat.{u}).homEquiv _ _).symm f

private theorem lift_unit {A : Sheaf J CommRingCat.{u}} (c : R ⟶ A)
    (hu : ∀ U, IsUnit (c.hom.app U (t.val U))) :
    ringedLocalizationRingUnitOfUniverses R t ≫ lift R t c hu = c := by
  apply Sheaf.hom_ext
  change ringedLocalizationRingPresheafUnitOfUniverses R t ≫
    (sheafificationAdjunction J CommRingCat.{u}).homEquiv _ _ (lift R t c hu) = _
  unfold lift
  rw [Equiv.apply_symm_apply]
  ext U r
  exact IsLocalization.Away.lift_eq (R := R.obj.obj U)
    (S := ringedSectionLocalizationCarrierOfUniverses R t U)
    (g := (c.hom.app U).hom) (t.val U) (hu U) r

end LocalizationRings

namespace LocalizationRings

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency.types false

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C]
variable {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasSheafify J CommRingCat.{u}]
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable (R : Sheaf J CommRingCat.{u})
variable (t : (R.obj ⋙ forget CommRingCat.{u}).sections)

private abbrev sequence :=
  Functor.ofSequence (X := fun _ : ℕ ↦
    SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (fun _ ↦ (LocalizationSequence.regularScalar R t).asHom) ⋙ localizationModuleSets R

private def scalar : sets R ⟶ sets R :=
  (localizationModuleSets R).map ((LocalizationSequence.regularScalar R t)).asHom

private def moduleIso := Classical.choose (ringedLocalizationRing_moduleComparisonOfUniverses R t)

private def cocone : Cocone (sequence R t) := by
  let c := (localizationModuleSets R).mapCocone (LocalizationSequence.localizationSheafCocone R t)
  let e := (localizationModuleSets R).mapIso (moduleIso R t).symm
  exact c.extend e.hom

private def isColimit : IsColimit (cocone R t) := by
  have := localizationSets_preserves_sequence R
  exact IsColimit.extendIso _ (isColimitOfPreserves (localizationModuleSets R)
    (LocalizationSequence.localizationSheafCoconeIsColimit R t))

private theorem cocone_zero : (cocone R t).ι.app 0 =
    (sheafCompose J (forget CommRingCat.{u})).map (ringedLocalizationRingUnitOfUniverses R t) := by
  apply (cancel_mono ((localizationModuleSets R).map (moduleIso R t).hom)).1
  change ((localizationModuleSets R).map
      (LocalizationSequence.localizationSheafMap R t 0) ≫
        (localizationModuleSets R).map (moduleIso R t).inv) ≫
          (localizationModuleSets R).map (moduleIso R t).hom = _
  rw [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, Functor.map_id,
    Category.comp_id, LocalizationSequence.localizationSheafMap_zero]
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro r
  change R.obj.obj U at r
  have h := Classical.choose_spec (ringedLocalizationRing_moduleComparisonOfUniverses R t)
    U (algebraMap (R.obj.obj U) (ringedSectionLocalizationCarrierOfUniverses R t U) r)
  change _ = (moduleIso R t).hom.val.app U
    ((toSheafify J (ringedLocalizationRingPresheafOfUniverses R t)).app U
      (algebraMap (R.obj.obj U) (ringedSectionLocalizationCarrierOfUniverses R t U) r))
  change _ =
    (Classical.choose (ringedLocalizationRing_moduleComparisonOfUniverses R t)).hom.val.app U
    ((toSheafify J (ringedLocalizationRingPresheafOfUniverses R t)).app U
      (algebraMap (R.obj.obj U) (ringedSectionLocalizationCarrierOfUniverses R t U) r))
  rw [h]
  change ((PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).unit.app
      (ringedSectionLocalizationPresheafOfUniverses R t)).app U
    (r • (1 : ringedSectionLocalizationCarrierOfUniverses R t U)) = _
  rw [Algebra.smul_def, mul_one]

end LocalizationRings

namespace LocalizationRings

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency.types false

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
variable [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasSheafify J CommRingCat.{u}]
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasSheafify K CommRingCat.{u}]
variable [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable {L : Sheaf J (Type u) ⥤ Sheaf K (Type u)} [PreservesFiniteLimits L]
variable {V : Sheaf K (Type u) ⥤ Sheaf J (Type u)} (adj : L ⊣ V)
variable {R : Sheaf J CommRingCat.{u}} {S A : Sheaf K CommRingCat.{u}}
variable (a : SheafOfModules.AlgebraicInverseImage L R S)
variable (t : (R.obj ⋙ forget CommRingCat.{u}).sections)
variable (s : (S.obj ⋙ forget CommRingCat.{u}).sections) (hs : IsInverseImageSection a t s)
variable (b : SheafOfModules.AlgebraicInverseImage L (ringedLocalizationRingOfUniverses R t) A)

private def sectionMap {E : Type uF} [Category.{vF} E] {H : GrothendieckTopology E}
    {B Q : Sheaf H CommRingCat.{u}} (c : B ⟶ Q)
    (x : (B.obj ⋙ forget CommRingCat.{u}).sections) :
    (Q.obj ⋙ forget CommRingCat.{u}).sections :=
  ⟨fun U ↦ c.hom.app U (x.val U), by
    intro U V g
    have h := congrArg (fun k ↦ k (x.val U)) (c.hom.naturality g)
    exact h.symm.trans (congrArg (c.hom.app V) (x.property g))⟩

include hs in
include hs in
private theorem scalar_image :
    L.map (scalar R t) ≫ a.ringUnderlying.hom = a.ringUnderlying.hom ≫ scalar S s := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext W
  apply ConcreteCategory.hom_ext
  intro x
  have h := a.ringMul (sets R) (𝟙 _) (constMap R t (sets R)) (scalar R t)
    (fun U r ↦ LocalizationSequence.scalar_apply R t U r) W x
  dsimp only [id] at h
  rw [hs (sets R) (constMap R t (sets R)) (fun _ _ ↦ rfl) W x] at h
  rw [Functor.map_id] at h
  change a.ringUnderlying.hom.hom.app W ((L.map (scalar R t)).hom.app W x) =
    @Mul.mul (S.obj.obj W) _ (a.ringUnderlying.hom.hom.app W x)
      (LocalizationSequence.sectionValue S s W) at h
  change a.ringUnderlying.hom.hom.app W ((L.map (scalar R t)).hom.app W x) =
    @Mul.mul (S.obj.obj W) _ (a.ringUnderlying.hom.hom.app W x)
      (LocalizationSequence.sectionValue S s W)
  exact h

private def imageDiagramIso : sequence S s ≅ sequence R t ⋙ L := by
  let τ : sequence R t ⋙ L ⟶ sequence S s :=
    NatTrans.ofSequence (fun _ ↦ a.ringUnderlying.hom) (by
      intro n
      simpa only [sequence, Functor.comp_map, Functor.ofSequence_map_homOfLE_succ, scalar]
        using scalar_image a t s hs)
  exact (NatIso.ofComponents (fun _ ↦ a.ringUnderlying) (fun f ↦ τ.naturality f)).symm

private def imageCocone : Cocone (sequence S s) where
  pt := sets A
  ι :=
    { app := fun n ↦ a.ringUnderlying.inv ≫ L.map ((cocone R t).ι.app n) ≫
        b.ringUnderlying.hom
      naturality := by
        intro n m f
        let c := ((Cocone.precompose (imageDiagramIso a t s hs).hom).obj
          (L.mapCocone (cocone R t))).extend b.ringUnderlying.hom
        exact (c.w f).trans (Category.comp_id _).symm }

private theorem imageCocone_zero : (imageCocone a t s hs b).ι.app 0 =
    (sheafCompose K (forget CommRingCat.{u})).map
      (transportHom a b (ringedLocalizationRingUnitOfUniverses R t)) := by
  change (a.ringUnderlying.inv ≫ L.map ((cocone R t).ι.app 0)) ≫
    b.ringUnderlying.hom = _
  rw [cocone_zero]
  rfl

end LocalizationRings

end CategoryTheory
