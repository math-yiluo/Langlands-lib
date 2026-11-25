/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.PrincipalReduction.Setup.DerivedReductionResolutionIndependence
import all WeilConjectures.Algebra.Homology.PrincipalReduction.Setup.DerivedReductionResolutionIndependence
import WeilConjectures.Algebra.Homology.PrincipalQuotient.PrincipalQuotientQuasiIso
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.FromJoel.Algebra.Homology.LeftResolution.CochainComplex

/-! # Invertibility of the flat-resolution comparison

The ordinary principal-quotient counit is invertible on complexes with regular terms,
and exact sections of flat sheaves have regular terms.
(blueprint: lem-pod-principal-reduction-flat-comparison) -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
universe u v r wO wS wR wA
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open CategoryTheory.Functor
open scoped ChangeOfRings

namespace SheafOfModules.PrincipalReduction.Setup
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r} ⋙
    forget₂ RingCat.{r} AddCommGrpCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}]
  {R : Type r} [CommRing R] (D : Setup (C := C) (J := J) R)

private theorem sections_regular (M : ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J D.O)) (hf : IsFlatOnSite (R := D.O) M) :
    Function.Injective (fun x : D.sections.obj M ↦ D.t • x) := by
  have := D.sectionsLimits
  have := D.sectionsColimits
  have hs := (D.tensorShortComplex_shortExact M hf).map_of_exact D.sections
  have hi := (ModuleCat.mono_iff_injective _).1 hs.mono_f
  intro x y hxy
  apply hi
  change (D.tensorMultiplication M).val.app (op D.U) x =
    (D.tensorMultiplication M).val.app (op D.U) y
  rw [D.tensorMultiplication_apply, D.tensorMultiplication_apply,
    D.terminal.hom_ext (D.terminal.from D.U) (𝟙 D.U)]
  change D.ρ D.t • (show M.val.obj (op D.U) from x) =
    D.ρ D.t • (show M.val.obj (op D.U) from y) at hxy
  simpa using hxy

variable [HasDerivedCategory.{wO}
    (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O))]
  [HasDerivedCategory.{wS}
    (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.S))]
  [HasDerivedCategory.{wR} (ModuleCat.{r} R)]
  [HasDerivedCategory.{wA} (ModuleCat.{r} D.A)]

private theorem c_isIso_on_kFlat (K : CochainComplex (ModuleCat.{r} R) ℤ)
    (hK : (HomologicalComplex.quasiIso (ModuleCat.{r} R) (.up ℤ)).kFlat K) :
    IsIso (D.c K) := by
  have := (DerivedCategory.exists_mixedTensor_pointwise_leftDerived
    D.quotientMap D.quotientSingle).choose_spec.choose_spec.2.2 K hK
  unfold c
  infer_instance

private theorem c_isIso_on_regular [IsDomain R] (ht : D.t ≠ 0)
    (K : CochainComplex (ModuleCat.{r} R) ℤ)
    (hK : ∀ i : ℤ, Function.Injective (fun x : K.X i ↦ D.t • x)) :
    IsIso (D.c K) := by
  let Λ := (Classical.choice (inferInstance :
    Abelian.HasFunctorialFlatResolution (ModuleCat.{r} R))).reduced
  let P := Λ.resolutionFunctor.obj K
  let p := Λ.resolutionNatTrans.app K
  have hp : QuasiIso p := inferInstance
  have hflat (i : ℤ) : ObjectProperty.flat (P.X i) := by
    have := CochainComplex.closedUnderColimitsOfShape_flat (ModuleCat.{r} R) ℤ
    let c := Λ.colimitOfShapeResolutionFunctorObj K
    exact ObjectProperty.prop_of_isColimit _
      (isColimitOfPreserves (HomologicalComplex.eval _ (.up ℤ) i) c.isColimit)
      (fun j ↦ ObjectProperty.flat.essImage_ι_le _ ((c.prop_diag_obj j).1 i))
  have hreg (i : ℤ) : Function.Injective (fun x : P.X i ↦ D.t • x) := by
    have hf : Module.Flat R (P.X i) :=
      (Module.Flat.iff_preservesFiniteLimits_tensorLeft _).2
        ((ObjectProperty.flat_iff_preservesFiniteLimits _).1 (hflat i))
    exact smul_right_injective (P.X i) ht
  have hkp := Λ.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le K
  have := D.c_isIso_on_kFlat P hkp
  have hquot := CochainComplex.PrincipalQuotient.quasiIso_map D.quotientMap D.t
    D.quotient_surjective D.quotient_kernel p hp hreg hK
  have := hquot
  have hn := D.c_naturality p
  dsimp only [Functor.id_obj] at hn
  have : IsIso (D.L.map (DerivedCategory.Q.map p) ≫ D.c K) := by
    rw [← hn]
    infer_instance
  exact IsIso.of_isIso_comp_left (D.L.map (DerivedCategory.Q.map p)) (D.c K)

/-- For a flat-term K-flat sheaf complex, the comparison constructed from the canonical
quotient-section map and the ordinary derived tensor counit is invertible.

Proof: tensoring the coefficient exact sequence with a flat term preserves exactness.
Exact sections make multiplication by t injective. Resolve its section complex by a
flat-term ordinary K-flat complex; principal quotient preserves the augmentation's
quasi-isomorphism because t is injective on both complexes. Naturality transfers the
invertible tensor counit from that resolution to the section complex. All remaining
factors of alpha are the quotient-section isomorphism and localization isomorphisms.
Source: Stacks Tags 06Y6 and 06YY, blueprint steps 3--9.
(blueprint: lem-pod-principal-reduction-flat-comparison) -/
theorem alpha_isIso [IsDomain R] (ht : D.t ≠ 0)
    (P : CochainComplex
      (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O)) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := D.O) P)
    (hflat : ∀ i : ℤ, IsFlatOnSite (R := D.O) (P.X i)) :
    IsIso (D.alpha P hP hflat) := by
  have := D.c_isIso_on_regular ht
    ((D.sections.mapHomologicalComplex (.up ℤ)).obj P)
    (fun i ↦ D.sections_regular (P.X i) (hflat i))
  unfold alpha
  infer_instance

end SheafOfModules.PrincipalReduction.Setup
