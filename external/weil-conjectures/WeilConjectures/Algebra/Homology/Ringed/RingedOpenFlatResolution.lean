/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Ringed.RingedOpenTotalTensorKFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.Algebra.Homology.QuasiIso
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
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
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # Flat resolutions under ringed slice extension

Source: Stacks Project, Modules on Sites, Tags 03DI, 03DJ and 0E8I
(lemma-j-shriek-and-tensor); the cochain and strict-tower refinement is agent-written
(blueprint: lem-cbc-ringed-open-flat-resolution).

Extension is the existing direct-sum presheaf followed by module sheafification.
All complexes are integer-indexed and may be unbounded. Strict inverse sequences
are functors from the opposite natural-number order, indexed starting at zero;
reindexing by n + 1 gives the convention of towers starting at one.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe c v r

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

/-- Present the fixed-right-factor site tensor using the left presheaf tensor.
Source: Stacks Project, Tag 03EK (blueprint: lem-cbc-ringed-open-flat-resolution).
Proof: braid the presheaf factors, apply the shared sectionwise tensor comparison,
and whisker by the forgetful functor and module sheafification. -/
private def siteLeftTensorIso {T : Type c} [Category.{v} T]
    {K : GrothendieckTopology T} [EssentiallySmall.{r} T]
    [HasSheafify K AddCommGrpCat.{r}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{r}]
    (A : Sheaf K CommRingCat.{r})
    (M : SheafOfModules.{r}
      ((sheafCompose K (forget₂ CommRingCat.{r} RingCat.{r})).obj A)) :
    (forget.{r} ((sheafCompose K (forget₂ CommRingCat.{r} RingCat.{r})).obj A) ⋙
      MonoidalCategory.tensorLeft M.val ⋙ PresheafOfModules.sheafification.{r}
        (R := (sheafCompose K (forget₂ CommRingCat.{r} RingCat.{r})).obj A) (𝟙 _)) ≅
      siteSheafTensorRight (A := A) M := by
  exact Functor.isoWhiskerLeft (forget _) (Functor.isoWhiskerRight
    (BraidedCategory.tensorLeftIsoTensorRight M.val ≪≫
      (siteTensorRightIso.{c, v, r} A M.val).symm)
    (PresheafOfModules.sheafification (𝟙 _)))

variable {S : Type c} [Category.{v} S] {J : GrothendieckTopology S}
  (R : Sheaf J CommRingCat.{max c v r}) (U : S)

/-- The existing quasi-isomorphism predicate with canonical small-site sheafification
witnesses supplied explicitly. No homology theory or notion of quasi-isomorphism is changed.
Source: Stacks Project, Modules on Sites, Tags 03DI--03DJ, and Homology, Tag 010N
(blueprint: lem-cbc-ringed-open-flat-resolution). -/
abbrev ringedOpenQuasiIso {T : Type c} [Category.{v} T] {K : GrothendieckTopology T}
    (A : Sheaf K CommRingCat.{max c v r})
    {P Q : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose K (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A)) ℤ}
    (f : P ⟶ Q) : Prop :=
  letI : HasSheafify K AddCommGrpCat.{max c v r} :=
    hasSheafify_coefficientUniverse.{c, v, max c v r} (J := K)
  letI : K.WEqualsLocallyBijective AddCommGrpCat.{max c v r} :=
    wEqualsLocallyBijective_coefficientUniverse.{c, v, max c v r} (J := K)
  QuasiIso f

/-- Ringed slice extension preserves K-flatness, flat terms, and termwise epimorphic
quasi-isomorphisms, without a boundedness assumption.

Source: Stacks Project, Modules on Sites, Tags 03DI, 03DJ and 0E8I
(lemma-j-shriek-and-tensor); agent-written resolution refinement
(blueprint: lem-cbc-ringed-open-flat-resolution).

Proof:
1. Reuse the K-flat preservation conjunct of ringedOpen_totalTensor_kFlat. That theorem
   already proves the unbounded total-tensor comparison and the signed interchange.
2. Fix M = P.X i. Presheaf braiding and siteTensorRightIso identify site flatness
   with exactness of forgetting M's variable partner, tensoring on the left with M.val,
   and sheafifying. Call this functor SM. Restrict the natural projection isomorphism
   to pairs (M,N), varying N: it identifies restriction followed by SM and extension
   with the analogous functor for e_! M. The three functors are exact, so this last
   functor is exact. The same presheaf comparison translates back to site flatness.
3. Exact extension preserves epimorphisms and homology. The component of an extended
   chain map is the extension of its component. Mathlib's
   HomologicalComplex.quasiIso_map_of_preservesHomology gives the quasi-isomorphism
   assertion using the same canonical sheafification witnesses as ringedOpenQuasiIso. -/
theorem ringedOpen_preserves_flat_resolution :
    (∀ P : CochainComplex (SheafOfModules.{max c v r}
        (((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).over U)) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients.{max c v, v, max c v r}
        (J := J.over U) (R := R.over U) P →
        CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r}
          (J := J) (R := R)
          ((ringedOpenExtensionOnComplexes.{c, v, r} R U).obj P)) ∧
    (∀ P : CochainComplex (SheafOfModules.{max c v r}
        (((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).over U)) ℤ,
      (∀ i : ℤ, @IsFlatOnSite.{max c v, v, max c v r, max c v r}
          (Over U) _ (J.over U) _
          (wEqualsLocallyBijective_coefficientUniverse.{max c v, v, max c v r}
            (J := J.over U))
          (hasSheafify_coefficientUniverse.{max c v, v, max c v r}
            (J := J.over U)).isRightAdjoint (R.over U) (P.X i)) →
        ∀ i : ℤ, @IsFlatOnSite.{c, v, max c v r, max c v r} S _ J _
          (wEqualsLocallyBijective_coefficientUniverse.{c, v, max c v r} (J := J))
          (hasSheafify_coefficientUniverse.{c, v, max c v r} (J := J)).isRightAdjoint R
          (((ringedOpenExtensionOnComplexes.{c, v, r} R U).obj P).X i)) ∧
    (∀ (P C : CochainComplex (SheafOfModules.{max c v r}
        (((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).over U)) ℤ)
        (q : P ⟶ C),
      (∀ i : ℤ, Epi (q.f i)) → ringedOpenQuasiIso.{max c v, v, r} (R.over U) q →
        (∀ i : ℤ, Epi (((ringedOpenExtensionOnComplexes.{c, v, r} R U).map q).f i)) ∧
          ringedOpenQuasiIso.{c, v, r} R
            ((ringedOpenExtensionOnComplexes.{c, v, r} R U).map q)) := by
  refine ⟨(ringedOpen_totalTensor_kFlat.{c, v, r} R U).2.1, ?_, ?_⟩
  · intro P hP i
    let : HasSheafify J AddCommGrpCat.{max c v r} :=
      hasSheafify_coefficientUniverse.{c, v, max c v r} (J := J)
    let : HasSheafify (J.over U) AddCommGrpCat.{max c v r} :=
      hasSheafify_coefficientUniverse.{max c v, v, max c v r} (J := J.over U)
    let : J.WEqualsLocallyBijective AddCommGrpCat.{max c v r} :=
      wEqualsLocallyBijective_coefficientUniverse.{c, v, max c v r} (J := J)
    let : (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r} :=
      wEqualsLocallyBijective_coefficientUniverse.{max c v, v, max c v r} (J := J.over U)
    let L := localizedSystemExtension.{c, v, r} R U
    let T := localizedSystemRestriction.{c, v, r} R U
    have : PreservesFiniteLimits L := localizedSystemExtensionLimits.{c, v, r} R U
    have : PreservesFiniteColimits L := localizedSystemExtensionColimits.{c, v, r} R U
    have : PreservesFiniteLimits T := localizedSystemRestrictionLimits.{c, v, r} R U
    have : PreservesFiniteColimits T := localizedSystemRestrictionColimits.{c, v, r} R U
    let M := P.X i
    let aU := PresheafOfModules.sheafification.{max c v r} (𝟙
      ((sheafCompose (J.over U)
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj (R.over U)).obj)
    let a := PresheafOfModules.sheafification.{max c v r} (𝟙
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).obj)
    let SM := forget.{max c v r} ((sheafCompose (J.over U)
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj (R.over U)) ⋙
      MonoidalCategory.tensorLeft
      (C := PresheafOfModules.{max c v r}
        ((R.over U).obj ⋙ forget₂ CommRingCat.{max c v r} RingCat.{max c v r}))
      (show PresheafOfModules.{max c v r}
        ((R.over U).obj ⋙ forget₂ CommRingCat.{max c v r} RingCat.{max c v r})
        from M.val) ⋙ aU
    let SN := forget.{max c v r} ((sheafCompose J
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R) ⋙ MonoidalCategory.tensorLeft
      (C := PresheafOfModules.{max c v r}
        (R.obj ⋙ forget₂ CommRingCat.{max c v r} RingCat.{max c v r}))
      (show PresheafOfModules.{max c v r}
        (R.obj ⋙ forget₂ CommRingCat.{max c v r} RingCat.{max c v r})
        from (L.obj M).val) ⋙ a
    have hM : exactFunctor _ _ (siteSheafTensorRight (A := R.over U) M) := hP i
    have hSM : exactFunctor _ _ SM := (exactFunctor _ _).prop_of_iso
      (siteLeftTensorIso.{max c v, v, max c v r} (R.over U) M).symm hM
    have : PreservesFiniteLimits SM := hSM.1
    have : PreservesFiniteColimits SM := hSM.2
    obtain ⟨θ⟩ := ringedSlice_extension_tensor.{c, max c r, v} J R U
    let eθ : T ⋙ SM ⋙ L ≅ SN := NatIso.ofComponents
      (fun N ↦ θ.app (M, N)) (by
        intro N N' f
        have h := θ.hom.naturality (X := (M, N)) (Y := (M, N')) (𝟙 M, f)
        simpa [SM, SN, L, T, aU, a, Functor.comp_map, Functor.prod_map,
          MonoidalCategory.tensor_map] using h)
    have : PreservesFiniteLimits (SM ⋙ L) := comp_preservesFiniteLimits _ _
    have : PreservesFiniteColimits (SM ⋙ L) := comp_preservesFiniteColimits _ _
    have he : exactFunctor _ _ (T ⋙ SM ⋙ L) :=
      ⟨comp_preservesFiniteLimits _ _, comp_preservesFiniteColimits _ _⟩
    have hSN : exactFunctor _ _ SN := (exactFunctor _ _).prop_of_iso eθ he
    exact (exactFunctor _ _).prop_of_iso
      (siteLeftTensorIso.{c, v, max c v r} R (L.obj M)) hSN
  · intro P C q hq hqi
    let : HasSheafify J AddCommGrpCat.{max c v r} :=
      hasSheafify_coefficientUniverse.{c, v, max c v r} (J := J)
    let : HasSheafify (J.over U) AddCommGrpCat.{max c v r} :=
      hasSheafify_coefficientUniverse.{max c v, v, max c v r} (J := J.over U)
    let : J.WEqualsLocallyBijective AddCommGrpCat.{max c v r} :=
      wEqualsLocallyBijective_coefficientUniverse.{c, v, max c v r} (J := J)
    let : (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r} :=
      wEqualsLocallyBijective_coefficientUniverse.{max c v, v, max c v r} (J := J.over U)
    have : QuasiIso q := hqi
    refine ⟨?_, ?_⟩
    · intro i
      have := hq i
      change Epi ((localizedSystemExtension.{c, v, r} R U).map (q.f i))
      infer_instance
    · change QuasiIso (((localizedSystemExtension.{c, v, r} R U).mapHomologicalComplex
        (ComplexShape.up ℤ)).map q)
      infer_instance

end SheafOfModules
