/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.SfIntegralReductionTower
public import WeilConjectures.SixFunctors.Supporting.PbcWeilCategory
public import WeilConjectures.AlgebraicGeometry.Weil.WeilCompletedTensorReflector
public import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback
public import WeilConjectures.Algebra.Homology.SixFunctors.WeilSiteDerivedTensorDescent
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
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
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.ProperBaseChange.ResolvingRepresentativeWhiskeringSupplement
import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedPullback
import WeilConjectures.AlgebraicGeometry.Pbc.PbcCompletedPullbackActualSupplement
import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulQuotientComparison
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.CategoryTheory.Localization.Linear
import WeilConjectures.Algebra.Homology.BifunctorLinear
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Linear
import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Homology.HomotopyCategory.Braided
public import WeilConjectures.SixFunctors.WfTensorLinearity.WeilTensorDescent
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal

/-!
# Relative condensed derived tensor and its geometric Frobenius

Source: latest blueprint, sec-six-functors/sk-rem-sf-pf-done,
(blueprint: prose-03-02).
The current blueprint uses `wfCondensedTensor`, the native relative derived tensor
on modules over the pulled-back condensed ring. Its first argument is computed by
a K-flat representative. `wfCondensedTensorFrobenius` composes the normalized tensor
comparison of exact pullback with the tensor of the given Weil isomorphisms.

The completed adic and rationalized constructions below are retained as presentation
interfaces for existing consumers. They do not define the current condensed tensor.
No preservation of constructibility or exactness on Weil pairs is assumed here.

The finite coefficient stages use `pbcStageDatum` and `pbcStageUniformizer`:
these are the valuation-ring data transported along `Shrink.algEquiv`, with the
actual field inclusions conjugated by that canonical equivalence.

## Main definitions

- `wfCondensedTensor`: relative derived tensor for arbitrary condensed coefficients.
- `wfCondensedTensorPullback`: canonical comparison for exact termwise pullback.
- `wfCondensedTensorFrobenius`: tensor of the given strict condensed Weil structures.
- `SheafOfModules.wfSiteDerivedTensor`: the localized K-flat tensor bifunctor.
- `wfIntegralTensor`, `wfRationalTensor`: completed integral and rational tensor.
- `wfRationalTensorPullback`: the normalized Frobenius/tensor comparison.
- `WeilConjectures.wfTensorFrobenius`: tensor of the given Weil structures.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

attribute [local irreducible] ScalarLocalization.composition
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] SheafOfModules.wfSiteDerivedTensor
  intrinsicCompletion intrinsicCompletionUnit intrinsicCompletionComplex
  intrinsicCompletionComplexUnit
set_option backward.isDefEq.respectTransparency false in
private theorem scalarLocalization_precomp_injective
    {R : Type u} [CommRing R] {C : Type v} [Category C]
    [Preadditive C] [Linear R C] (p : R) {E : Type w} [Category E]
    (F G : ScalarLocalization R C p ⥤ E)
    (h : ScalarLocalization.localization R C p ⋙ F =
      ScalarLocalization.localization R C p ⋙ G) : F = G := by
  classical
  let Q := ScalarLocalization.localization R C p
  let e := eqToIso h
  let i (K : ScalarLocalization R C p) : F.obj K ≅ G.obj K := e.app K.obj
  have nat {K L : ScalarLocalization R C p} (f : K.obj ⟶ L.obj) :
      F.map (Q.map f) ≫ (i L).hom = (i K).hom ≫ G.map (Q.map f) :=
    e.hom.naturality f
  have nat_all : ∀ {K L : ScalarLocalization R C p} (f : K ⟶ L),
      F.map f ≫ (i L).hom = (i K).hom ≫ G.map f := by
    rintro ⟨K⟩ ⟨L⟩ f
    let K : ScalarLocalization R C p := ⟨K⟩
    let L : ScalarLocalization R C p := ⟨L⟩
    obtain ⟨⟨g, s⟩, hs⟩ := IsLocalizedModule.surj (Submonoid.powers p)
      (TensorProduct.mk R (Localization.Away p) (K.obj ⟶ L.obj) 1) f
    let z : K.obj ⟶ K.obj := (s : R) • 𝟙 K.obj
    have hz : Q.map z ≫ f = Q.map g := by
      change ScalarLocalization.composition R C p _ _ _ f (1 ⊗ₜ[R] z) = 1 ⊗ₜ[R] g
      have ht : (1 : Localization.Away p) ⊗ₜ[R] z =
          algebraMap R (Localization.Away p) (s : R) • (𝟙 K) := by
        dsimp [z]
        rw [TensorProduct.tmul_smul]
        exact (algebraMap_smul (M := Localization.Away p ⊗[R] (K.obj ⟶ K.obj))
          (Localization.Away p) (s : R) (1 ⊗ₜ[R] 𝟙 K.obj)).symm
      rw [ht, map_smul]
      change algebraMap R (Localization.Away p) (s : R) • (𝟙 K ≫ f) =
        1 ⊗ₜ[R] g
      rw [Category.id_comp]
      change algebraMap R (Localization.Away p) (s : R) •
        (f : Localization.Away p ⊗[R] (K.obj ⟶ L.obj)) = 1 ⊗ₜ[R] g
      have : IsScalarTower R (Localization.Away p) (K ⟶ L) :=
        inferInstanceAs (IsScalarTower R (Localization.Away p)
          (Localization.Away p ⊗[R] (K.obj ⟶ L.obj)))
      rw [algebraMap_smul]
      exact hs
    have hu := IsLocalization.map_units (Localization.Away p) s
    let j : K ≅ K :=
      { hom := (hu.unit : Localization.Away p) • 𝟙 K
        inv := ((hu.unit⁻¹ : (Localization.Away p)ˣ) : Localization.Away p) • 𝟙 K
        hom_inv_id := by simp [Linear.comp_smul, smul_smul]
        inv_hom_id := by simp [Linear.comp_smul, smul_smul] }
    have hj : Q.map z = j.hom := by
      change (1 : Localization.Away p) ⊗ₜ[R] ((s : R) • 𝟙 K.obj) = _
      rw [TensorProduct.tmul_smul]
      change (s : R) • (1 ⊗ₜ[R] 𝟙 K.obj) =
        (hu.unit : Localization.Away p) • (1 ⊗ₜ[R] 𝟙 K.obj)
      rw [hu.unit_spec, algebraMap_smul]
    have : IsIso (Q.map z) := by rw [hj]; exact j.isIso_hom
    apply (cancel_epi (F.map (Q.map z))).1
    rw [← Category.assoc, ← F.map_comp, hz, nat]
    rw [← Category.assoc, nat z, Category.assoc, ← G.map_comp, hz]
  refine CategoryTheory.Functor.ext
    (fun K ↦ CategoryTheory.Functor.congr_obj h K.obj) ?_
  intro K L f
  apply (cancel_mono (i L).hom).1
  have hi (K : ScalarLocalization R C p) : (i K).hom =
      eqToHom (CategoryTheory.Functor.congr_obj h K.obj) := eqToHom_app h K.obj
  simpa only [hi, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
    using nat_all f

private theorem scalarLocalization_mapHom_tmul
    {R : Type u} [CommRing R] {C : Type v} [Category C]
    [Preadditive C] [Linear R C] (p : R) (H : C ⥤ C) [H.Additive] [H.Linear R]
    {M N : C} (s : Localization.Away p) (f : M ⟶ N) :
    ScalarLocalization.mapHom R C p H M N (s ⊗ₜ[R] f) = s ⊗ₜ[R] H.map f :=
  LinearMap.baseChange_tmul _ _ _

set_option backward.isDefEq.respectTransparency false in
private theorem scalarLocalization_bilinear_naturality
    {R : Type u} [CommRing R] {C : Type v} [Category C]
    [Preadditive C] [Linear R C] (p : R) (H : C ⥤ C) [H.Additive] [H.Linear R]
    {M M' N N' S S' T T' : C}
    (b : (Localization.Away p ⊗[R] (M ⟶ M')) →ₗ[Localization.Away p]
      (Localization.Away p ⊗[R] (N ⟶ N')) →ₗ[Localization.Away p]
        (Localization.Away p ⊗[R] (S ⟶ S')))
    (b' : (Localization.Away p ⊗[R] (H.obj M ⟶ H.obj M')) →ₗ[Localization.Away p]
      (Localization.Away p ⊗[R] (H.obj N ⟶ H.obj N')) →ₗ[Localization.Away p]
        (Localization.Away p ⊗[R] (T ⟶ T')))
    (t : (M ⟶ M') → (N ⟶ N') → (S ⟶ S'))
    (t' : (H.obj M ⟶ H.obj M') → (H.obj N ⟶ H.obj N') → (T ⟶ T'))
    (hb : ∀ f g s z, b (s ⊗ₜ[R] f) (z ⊗ₜ[R] g) = (s * z) ⊗ₜ[R] (t f g))
    (hb' : ∀ f g s t, b' (s ⊗ₜ[R] f) (t ⊗ₜ[R] g) = (s * t) ⊗ₜ[R] (t' f g))
    (i : H.obj S ⟶ T) (i' : H.obj S' ⟶ T')
    (hi : ∀ f g, H.map (t f g) ≫ i' = i ≫ t' (H.map f) (H.map g))
    (f : Localization.Away p ⊗[R] (M ⟶ M'))
    (g : Localization.Away p ⊗[R] (N ⟶ N')) :
    ScalarLocalization.composition R C p _ _ _ (1 ⊗ₜ[R] i')
        (ScalarLocalization.mapHom R C p H _ _ (b f g)) =
      ScalarLocalization.composition R C p _ _ _
        (b' (ScalarLocalization.mapHom R C p H _ _ f)
          (ScalarLocalization.mapHom R C p H _ _ g)) (1 ⊗ₜ[R] i) := by
  induction f using TensorProduct.inductionOn with
  | add f₁ f₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
  | tmul s f =>
    induction g using TensorProduct.inductionOn with
    | add g₁ g₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
    | tmul t g =>
      rw [hb, scalarLocalization_mapHom_tmul, scalarLocalization_mapHom_tmul,
        scalarLocalization_mapHom_tmul, hb', ScalarLocalization.composition_tmul,
        ScalarLocalization.composition_tmul, one_mul, mul_one, hi]

variable (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
  (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)

attribute [local instance] WeilConjectures.instEssentiallySmallProEt_weilConjectures

/-- Ordinary uncompleted derived tensor over the actual completed coefficient sheaf.
Source: blueprint order 2107 (blueprint: prose-03-02). -/
abbrev wfOrdinaryDerivedTensor :
    PbcCompletedDerived X d × PbcCompletedDerived X d ⥤ PbcCompletedDerived X d :=
  SheafOfModules.wfSiteDerivedTensor (ProEt.topology X) (pbcAdicCompletion X d)

set_option backward.isDefEq.respectTransparency false in
private theorem siteTensorLinear (N : pbcModules X (pbcAdicCompletion X d)) :
    (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1} N).Linear A := by
  let O := (sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (pbcAdicCompletion X d)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 O.obj)
  constructor
  intro M M' f b
  change (PresheafOfModules.sheafification (𝟙 O.obj)).map
      (SheafOfModules.siteTensorHom (b • f).val N.val) =
    b • (PresheafOfModules.sheafification (𝟙 O.obj)).map
      (SheafOfModules.siteTensorHom f.val N.val)
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  have hn := adj.unit.naturality (SheafOfModules.siteTensorHom (b • f).val N.val)
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  dsimp only [Functor.comp_map]
  rw [← hn]
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  have hf := adj.unit.naturality (SheafOfModules.siteTensorHom f.val N.val)
  have hf' := congrArg (fun h ↦ (h.app U).hom (x ⊗ₜ y)) hf
  change ((adj.unit.app (SheafOfModules.siteTensorPresheaf M'.val N.val)).app U).hom
      ((pbcCompletedSection X d U b • (f.val.app U).hom x) ⊗ₜ y) =
    pbcCompletedSection X d U b •
      ((PresheafOfModules.sheafification (𝟙 O.obj)).map
        (SheafOfModules.siteTensorHom f.val N.val)).val.app U
          ((adj.unit.app (SheafOfModules.siteTensorPresheaf M.val N.val)).app U
            (x ⊗ₜ y))
  erw [← TensorProduct.smul_tmul'
    (R := (pbcAdicCompletion X d).obj.obj U)
    (R' := (pbcAdicCompletion X d).obj.obj U), map_smul]
  exact congrArg (fun z ↦ pbcCompletedSection X d U b • z) hf'

set_option backward.isDefEq.respectTransparency false in
private theorem tensorLinearRight (N : pbcModules X (pbcAdicCompletion X d)) :
    ((proEtaleOrdinaryTensor X (pbcAdicCompletion X d)).flip.obj N).Linear A := by
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0} _
  have := siteTensorLinear.{u} X d N
  let i : SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1} N ≅
      (proEtaleOrdinaryTensor X (pbcAdicCompletion X d)).flip.obj N :=
    SheafOfModules.siteSheafTensorRightIso.{u + 1, u, u + 1} (pbcAdicCompletion X d) N
  exact Functor.linear_of_iso A i

set_option backward.isDefEq.respectTransparency false in
private theorem tensorLinearLeft (M : pbcModules X (pbcAdicCompletion X d)) :
    ((proEtaleOrdinaryTensor X (pbcAdicCompletion X d)).obj M).Linear A := by
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0} _
  let := SheafOfModules.cochainModulesMonoidal.{u + 1, u, u + 1}
    (pbcAdicCompletion X d)
  let := SheafOfModules.cochainModulesSymmetric.{u + 1, u, u + 1}
    (pbcAdicCompletion X d)
  have := tensorLinearRight X d M
  exact Functor.linear_of_iso A
    (BraidedCategory.tensorLeftIsoTensorRight (C := pbcModules X (pbcAdicCompletion X d)) M).symm

set_option backward.isDefEq.respectTransparency false in
private theorem derivedBilinear :
    (∀ P, ((Functor.curry.obj (wfOrdinaryDerivedTensor X d)).obj P).Additive ∧
      ((Functor.curry.obj (wfOrdinaryDerivedTensor X d)).obj P).Linear A) ∧
    (∀ P, ((Functor.curry.obj (wfOrdinaryDerivedTensor X d)).flip.obj P).Additive ∧
      ((Functor.curry.obj (wfOrdinaryDerivedTensor X d)).flip.obj P).Linear A) := by
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0} _
  let R : Sheaf (ProEt.topology X) CommRingCat.{u + 1} := pbcAdicCompletion X d
  let := SheafOfModules.cochainModulesMonoidal.{u + 1, u, u + 1} R
  let := SheafOfModules.cochainModulesPreadditive.{u + 1, u, u + 1} R
  have (N : pbcModules X R) : ((proEtaleOrdinaryTensor X R).flip.obj N).Linear A :=
    tensorLinearRight X d N
  have (M : pbcModules X R) : ((proEtaleOrdinaryTensor X R).obj M).Linear A :=
    tensorLinearLeft X d M
  let h := SheafOfModules.wf_site_derived_tensor_descent.{u + 1, u, u + 2, 0, 0}
    (ProEt.topology X) R
  let S := h.choose
  have hS := h.choose_spec.1
  let B := h.choose_spec.2.2.1.choose
  let c := h.choose_spec.2.2.1.choose_spec.1.some
  let t := h.choose_spec.2.2.1.choose_spec.2.choose_spec.some
  let L := HomotopyCategory.quotient (pbcModules X R) (.up ℤ)
  let F := (proEtaleOrdinaryTensor X R).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)
  have hc : (L.prod L) ⋙ B ≅ Functor.uncurry.obj F ⋙ L := c
  have hb := WfTensorLinearity.homotopyBilinear A L B F L hc
  have (P : HomotopyCategory (pbcModules X R) (.up ℤ)) :
      ((Functor.curry.obj B).obj P).Additive := (hb.1 P).1
  have (P : HomotopyCategory (pbcModules X R) (.up ℤ)) :
      ((Functor.curry.obj B).obj P).Linear A := (hb.1 P).2
  have (P : HomotopyCategory (pbcModules X R) (.up ℤ)) :
      ((Functor.curry.obj B).flip.obj P).Additive := (hb.2 P).1
  have (P : HomotopyCategory (pbcModules X R) (.up ℤ)) :
      ((Functor.curry.obj B).flip.obj P).Linear A := (hb.2 P).2
  let W := (HomotopyCategory.quasiIso (pbcModules X R) (.up ℤ)).inverseImage S.ι
  let q := S.ι ⋙ DerivedCategory.Qh
  obtain ⟨E, hE, ⟨iE⟩⟩ := h.choose_spec.2.1
  have : E.IsEquivalence := hE
  have : q.IsLocalization W := Functor.IsLocalization.of_iso W iE
  have hres : ∀ K : HomotopyCategory (pbcModules X R) (.up ℤ),
      ∃ (Z : S.FullSubcategory) (f : Z.obj ⟶ K),
        HomotopyCategory.quasiIso _ (.up ℤ) f := by
    intro K
    obtain ⟨Z, f, hk, hf, hq, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients
        (C := X.ProEt) (J := ProEt.topology X) (R := R) K.as
    refine ⟨⟨L.obj Z, (hS _).2 ⟨hk, ?_⟩⟩, L.map f, ?_⟩
    · intro n
      exact hf n
    · exact (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hq
  have : W.HasRightCalculusOfFractions := WfTensorLinearity.resolvingFractions _ S hres
  have ht : (S.ι.prod S.ι) ⋙ B ⋙ DerivedCategory.Qh ≅
      (q.prod q) ⋙ wfOrdinaryDerivedTensor X d := by
    unfold wfOrdinaryDerivedTensor SheafOfModules.wfSiteDerivedTensor
    exact t
  exact WfTensorLinearity.localizedBilinear A q W S.ι B DerivedCategory.Qh
    (wfOrdinaryDerivedTensor X d) ht

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.integralOperationsSiteSmall in
set_option backward.isDefEq.respectTransparency false in
/-- The localization model's natural comparison on flat-term K-flat representatives.
Source: Stacks 06YT; blueprint order 2107 (blueprint: prose-03-02).
Proof: take the natural representative comparison from site-derived-tensor descent.
The homotopy quotient comparison identifies its source with total tensor of complexes.
Flatness means exactness of sheaf tensor, so the two flat-term subcategories coincide.
Their localization comparisons give the displayed natural isomorphism. Restriction
of transformations to the resolving subcategory is bijective by descent, so the
compatible comparison with any other model exists uniquely. Thus the chosen model
is determined up to its unique compatible natural isomorphism. -/
theorem wfTensorRepresentative_exists :
    ∃ i :
      (((proEtaleFlatRepresentatives X (pbcAdicCompletion X d)).ι.prod
          (proEtaleFlatRepresentatives X (pbcAdicCompletion X d)).ι) ⋙
        Functor.uncurry.obj
          ((proEtaleOrdinaryTensor X (pbcAdicCompletion X d)).map₂HomologicalComplex
           (.up ℤ) (.up ℤ) (.up ℤ)) ⋙ DerivedCategory.Q) ≅
      ((((proEtaleFlatRepresentatives X (pbcAdicCompletion X d)).ι ⋙ DerivedCategory.Q).prod
        ((proEtaleFlatRepresentatives X (pbcAdicCompletion X d)).ι ⋙ DerivedCategory.Q)) ⋙
          wfOrdinaryDerivedTensor X d),
      ∀ b : ProEtaleTensorModel X (pbcAdicCompletion X d),
        ∃! e : wfOrdinaryDerivedTensor X d ≅ b.tensor,
          i.hom ≫ Functor.whiskerLeft
            ((((proEtaleFlatRepresentatives X (pbcAdicCompletion X d)).ι ⋙
                DerivedCategory.Q).prod
              ((proEtaleFlatRepresentatives X (pbcAdicCompletion X d)).ι ⋙
                DerivedCategory.Q))) e.hom = b.representative.hom := by
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let R : Sheaf (ProEt.topology X) CommRingCat.{u + 1} := pbcAdicCompletion X d
  let h := SheafOfModules.wf_site_derived_tensor_descent.{u + 1, u, u + 2, 0, 0}
    (ProEt.topology X) R
  let S := h.choose
  have hS := h.choose_spec.1
  let c := h.choose_spec.2.2.1.choose_spec.1.some
  let t := h.choose_spec.2.2.1.choose_spec.2.choose_spec.some
  let P := proEtaleFlatRepresentatives X R
  let J : P.FullSubcategory ⥤ S.FullSubcategory :=
    ObjectProperty.lift S (P.ι ⋙ HomotopyCategory.quotient _ _) (by
      intro K
      apply (hS _).2
      refine ⟨K.property.1, ?_⟩
      intro n
      exact (exactFunctor (proEtaleRingModules X R) (proEtaleRingModules X R)).prop_of_iso
        (SheafOfModules.siteSheafTensorRightIso.{u + 1, u, u + 1}
          (C := X.ProEt) (J := ProEt.topology X) R (K.obj.X n))
        (K.property.2 n))
  let L := HomotopyCategory.quotient (proEtaleRingModules X R) (.up ℤ)
  let B := h.choose_spec.2.2.1.choose
  let T := wfOrdinaryDerivedTensor X d
  let tc := Functor.uncurry.obj
    ((proEtaleOrdinaryTensor X R).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ))
  have hc : (L.prod L) ⋙ B ≅ tc ⋙ L := c
  have ht : (S.ι.prod S.ι) ⋙ B ⋙ DerivedCategory.Qh ≅
      ((S.ι ⋙ DerivedCategory.Qh).prod (S.ι ⋙ DerivedCategory.Qh)) ⋙ T := by
    unfold T wfOrdinaryDerivedTensor SheafOfModules.wfSiteDerivedTensor
    exact t
  let i := WfTensorLinearity.representativeComparison P.ι J S.ι L DerivedCategory.Qh
    DerivedCategory.Q B T tc hc ht rfl rfl (DerivedCategory.quotientCompQhIso _)
  refine ⟨i, ?_⟩
  intro b
  let H : ObjectProperty (HomotopyCategory (pbcModules X (pbcAdicCompletion X d)) (.up ℤ)) :=
    fun K ↦ P K.as
  have hres : ∀ K : HomotopyCategory (pbcModules X (pbcAdicCompletion X d)) (.up ℤ),
      ∃ (L : H.FullSubcategory) (f : L.obj ⟶ K),
        HomotopyCategory.quasiIso _ (.up ℤ) f := by
    intro K
    obtain ⟨L, f, hk, hf, hq, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients
        (C := X.ProEt) (J := ProEt.topology X) (R := R) K.as
    refine ⟨⟨(HomotopyCategory.quotient _ (.up ℤ)).obj L, hk, ?_⟩,
      (HomotopyCategory.quotient _ (.up ℤ)).map f, ?_⟩
    · intro n
      exact (exactFunctor (proEtaleRingModules X R) (proEtaleRingModules X R)).prop_of_iso
        (SheafOfModules.siteSheafTensorRightIso.{u + 1, u, u + 1}
          (C := X.ProEt) (J := ProEt.topology X) R (L.X n)).symm (hf n)
    · exact (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hq
  set_option backward.isDefEq.respectTransparency true in
    have hff := CategoryTheory.resolvingRepresentativesFullyFaithfulWhiskering
      (K := CochainComplex (pbcModules X (pbcAdicCompletion X d)) ℤ)
      (H := HomotopyCategory (pbcModules X (pbcAdicCompletion X d)) (.up ℤ))
      (D := PbcCompletedDerived X d) (PbcCompletedDerived X d)
      (HomotopyCategory.quotient _ (.up ℤ)) HomotopyCategory.quotient_obj_surjective
      (HomotopyCategory.quasiIso _ (.up ℤ)) DerivedCategory.Qh P H
      (fun _ ↦ Iff.rfl) hres
  obtain ⟨ff⟩ := hff
  let ff' := ff.ofIso ((Functor.whiskeringLeft _ _ (PbcCompletedDerived X d)).mapIso
    (NatIso.prod (Functor.isoWhiskerLeft P.ι (DerivedCategory.quotientCompQhIso _))
      (Functor.isoWhiskerLeft P.ι (DerivedCategory.quotientCompQhIso _))))
  exact WfTensorLinearity.uniqueComparison _ ff' i b.representative

/-- The existing pullback-comparison interface with this very localized tensor.
Source: Stacks 06YT; blueprint order 2107 (blueprint: prose-03-02). -/
def wfTensorModel : ProEtaleTensorModel X (pbcAdicCompletion X d) where
  tensor := wfOrdinaryDerivedTensor X d
  representative := (wfTensorRepresentative_exists X d).choose

/-- Integral completed tensor is ordinary derived tensor followed by the Koszul reflector.
Source: blueprint order 2107; Bhatt--Scholze Definition 3.4.10
(blueprint: prose-03-02). -/
def wfIntegralTensor : WfCompleteCategory X d r a ha × WfCompleteCategory X d r a ha ⥤
    WfCompleteCategory X d r a ha :=
  ((ObjectProperty.ι (WfIsComplete X d r a ha)).prod
    (ObjectProperty.ι (WfIsComplete X d r a ha))) ⋙
      wfOrdinaryDerivedTensor X d ⋙ wfCompletion X d r a ha

/-- The ambient rational category keeps all integral complete objects, without boundedness.
Source: blueprint order 2107 (blueprint: prose-03-02). -/
abbrev WfAmbientRationalCategory (p : A) :=
  ScalarLocalization A (WfCompleteCategory X d r a ha) p

/-- The underlying object of rational tensor, before specifying its localized Hom action.
Source: blueprint order 2107 (blueprint: prose-03-02). -/
def wfRationalTensorObj (p : A)
    (M N : WfAmbientRationalCategory X d r a ha p) :
    WfAmbientRationalCategory X d r a ha p :=
  ⟨(wfIntegralTensor X d r a ha).obj (M.obj, N.obj)⟩

private theorem wfCompletion_unit_map {M N : PbcCompletedDerived X d} (f : M ⟶ N) :
    wfCompletionUnit X d r a ha M ≫ ((wfCompletion X d r a ha).map f).hom =
      f ≫ wfCompletionUnit X d r a ha N := by
  exact (Equiv.ofBijective _
    ((wfCompletionReflector X d r a ha).2 M
      (wfCompletionObj X d r a ha N) ((wfCompletionReflector X d r a ha).1 N))).apply_symm_apply _

set_option backward.isDefEq.respectTransparency false in
private theorem completionLinear :
    (wfCompletion X d r a ha).Additive ∧ (wfCompletion X d r a ha).Linear A := by
  constructor
  · constructor
    intro M N f g
    apply ObjectProperty.hom_ext
    apply ((wfCompletionReflector X d r a ha).2 M
      (wfCompletionObj X d r a ha N) ((wfCompletionReflector X d r a ha).1 N)).1
    dsimp only
    change _ = wfCompletionUnit X d r a ha M ≫
      (((wfCompletion X d r a ha).map f).hom + ((wfCompletion X d r a ha).map g).hom)
    rw [Preadditive.comp_add, wfCompletion_unit_map, wfCompletion_unit_map,
      wfCompletion_unit_map, Preadditive.add_comp]
  · constructor
    intro M N f b
    apply ObjectProperty.hom_ext
    apply ((wfCompletionReflector X d r a ha).2 M
      (wfCompletionObj X d r a ha N) ((wfCompletionReflector X d r a ha).1 N)).1
    dsimp only
    change _ = wfCompletionUnit X d r a ha M ≫
      (b • ((wfCompletion X d r a ha).map f).hom)
    rw [Linear.comp_smul, wfCompletion_unit_map, wfCompletion_unit_map, Linear.smul_comp]

/-- Bilinear scalar extension is uniquely determined on pure tensors, including denominators.
Source: blueprint order 2107 (blueprint: prose-03-02).
Proof: sheaf tensor is linear in each variable. Its K-flat localization is linear by
extension of transformations from K-flat representatives; the reflector is linear by its
unit and the Hom bijection. Extend this bilinear map along A→A[1/p] in both variables.
The tensor-product universal property gives the displayed pure-tensor formula and uniqueness.
Writing coefficients as inverse powers gives precisely denominator p^(r+s). -/
theorem wfRationalTensorHom_exists (p : A)
    (M M' N N' : WfAmbientRationalCategory X d r a ha p) :
    ∃! b : (M ⟶ M') →ₗ[Localization.Away p] (N ⟶ N') →ₗ[Localization.Away p]
        (wfRationalTensorObj X d r a ha p M N ⟶ wfRationalTensorObj X d r a ha p M' N'),
      ∀ (f : M.obj ⟶ M'.obj) (g : N.obj ⟶ N'.obj) (s t : Localization.Away p),
        b (s ⊗ₜ[A] f) (t ⊗ₜ[A] g) =
          (s * t) ⊗ₜ[A] (wfIntegralTensor X d r a ha).map (Prod.mkHom f g) := by
  have hd := derivedBilinear X d
  let : ∀ P : PbcCompletedDerived X d,
      ((Functor.curry.obj (wfOrdinaryDerivedTensor X d)).obj P).Additive :=
    fun P ↦ (hd.1 P).1
  let : ∀ P : PbcCompletedDerived X d,
      ((Functor.curry.obj (wfOrdinaryDerivedTensor X d)).obj P).Linear A :=
    fun P ↦ (hd.1 P).2
  let : ∀ P : PbcCompletedDerived X d,
      ((Functor.curry.obj (wfOrdinaryDerivedTensor X d)).flip.obj P).Additive :=
    fun P ↦ (hd.2 P).1
  let : ∀ P : PbcCompletedDerived X d,
      ((Functor.curry.obj (wfOrdinaryDerivedTensor X d)).flip.obj P).Linear A :=
    fun P ↦ (hd.2 P).2
  have := (completionLinear X d r a ha).1
  have := (completionLinear X d r a ha).2
  let I := ObjectProperty.ι (WfIsComplete X d r a ha)
  let T := wfIntegralTensor X d r a ha
  let : ∀ P : WfCompleteCategory X d r a ha, ((Functor.curry.obj T).obj P).Additive := by
    intro P
    change (I ⋙ (Functor.curry.obj (wfOrdinaryDerivedTensor X d)).obj P.obj ⋙
      wfCompletion X d r a ha).Additive
    infer_instance
  let : ∀ P : WfCompleteCategory X d r a ha, ((Functor.curry.obj T).obj P).Linear A := by
    intro P
    change (I ⋙ (Functor.curry.obj (wfOrdinaryDerivedTensor X d)).obj P.obj ⋙
      wfCompletion X d r a ha).Linear A
    infer_instance
  let : ∀ P : WfCompleteCategory X d r a ha, ((Functor.curry.obj T).flip.obj P).Additive := by
    intro P
    change (I ⋙ (Functor.curry.obj (wfOrdinaryDerivedTensor X d)).flip.obj P.obj ⋙
      wfCompletion X d r a ha).Additive
    infer_instance
  let : ∀ P : WfCompleteCategory X d r a ha, ((Functor.curry.obj T).flip.obj P).Linear A := by
    intro P
    change (I ⋙ (Functor.curry.obj (wfOrdinaryDerivedTensor X d)).flip.obj P.obj ⋙
      wfCompletion X d r a ha).Linear A
    infer_instance
  exact WfTensorLinearity.rationalTensorHom_exists A T p M M' N N'

/-- The unique localized bilinear map; its values are prescribed on every numerator.
Source: blueprint order 2107 (blueprint: prose-03-02). -/
def wfRationalTensorHom (p : A)
    (M M' N N' : WfAmbientRationalCategory X d r a ha p) :=
  (wfRationalTensorHom_exists X d r a ha p M M' N N').exists.choose

private theorem wfRationalTensorHom_tmul (p : A)
    (M M' N N' : WfAmbientRationalCategory X d r a ha p)
    (f : M.obj ⟶ M'.obj) (g : N.obj ⟶ N'.obj) (s t : Localization.Away p) :
    wfRationalTensorHom X d r a ha p M M' N N' (s ⊗ₜ[A] f) (t ⊗ₜ[A] g) =
      (s * t) ⊗ₜ[A] (wfIntegralTensor X d r a ha).map (Prod.mkHom f g) :=
  (wfRationalTensorHom_exists X d r a ha p M M' N N').exists.choose_spec f g s t

attribute [local irreducible] wfRationalTensorHom

/-- The extended tensor maps satisfy the bifunctor laws.
Source: blueprint order 2107 (blueprint: prose-03-02).
Proof: on pure tensors the identity law follows from integral tensor's identity law and
1*1=1. Composition follows from integral functoriality and commutative multiplication of
localized scalars. Bilinearity extends these equations to all localized morphisms. -/
theorem wfRationalTensor_laws (p : A) :
    (∀ M N : WfAmbientRationalCategory X d r a ha p,
      wfRationalTensorHom X d r a ha p M M N N (𝟙 M) (𝟙 N) = 𝟙 _) ∧
    ∀ (M M' M'' N N' N'' : WfAmbientRationalCategory X d r a ha p)
      (f : M ⟶ M') (f' : M' ⟶ M'') (g : N ⟶ N') (g' : N' ⟶ N''),
      wfRationalTensorHom X d r a ha p M M'' N N'' (f ≫ f') (g ≫ g') =
        wfRationalTensorHom X d r a ha p M M' N N' f g ≫
          wfRationalTensorHom X d r a ha p M' M'' N' N'' f' g' := by
  constructor
  · intro M N
    change wfRationalTensorHom X d r a ha p M M N N
      ((1 : Localization.Away p) ⊗ₜ[A] 𝟙 M.obj)
      ((1 : Localization.Away p) ⊗ₜ[A] 𝟙 N.obj) =
        (1 : Localization.Away p) ⊗ₜ[A] 𝟙 _
    rw [wfRationalTensorHom_tmul, one_mul]
    congr 1
    exact (wfIntegralTensor X d r a ha).map_id (M.obj, N.obj)
  · intro M M' M'' N N' N'' f f' g g'
    change wfRationalTensorHom X d r a ha p M M'' N N''
      (ScalarLocalization.composition A (WfCompleteCategory X d r a ha) p _ _ _ f' f)
      (ScalarLocalization.composition A (WfCompleteCategory X d r a ha) p _ _ _ g' g) =
        ScalarLocalization.composition A (WfCompleteCategory X d r a ha) p _ _ _
          (wfRationalTensorHom X d r a ha p M' M'' N' N'' f' g')
          (wfRationalTensorHom X d r a ha p M M' N N' f g)
    induction f using TensorProduct.inductionOn with
    | add f₁ f₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
    | tmul s f =>
      induction f' using TensorProduct.inductionOn with
      | add f₁ f₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
      | tmul t f' =>
        induction g using TensorProduct.inductionOn with
        | add g₁ g₂ h₁ h₂ => simp only [map_add, h₁, h₂]
        | tmul u g =>
          induction g' using TensorProduct.inductionOn with
          | add g₁ g₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
          | tmul v g' =>
            rw [ScalarLocalization.composition_tmul, ScalarLocalization.composition_tmul,
              wfRationalTensorHom_tmul, wfRationalTensorHom_tmul,
              wfRationalTensorHom_tmul, ScalarLocalization.composition_tmul]
            have ht := (wfIntegralTensor X d r a ha).map_comp
              (Prod.mkHom f g) (Prod.mkHom f' g')
            rw [← ht]
            congr 1
            ac_rfl

/-- Completed tensor rationalized with the stated product-of-denominators convention.
Source: blueprint order 2107 (blueprint: prose-03-02). -/
def wfRationalTensor (p : A) :
    WfAmbientRationalCategory X d r a ha p × WfAmbientRationalCategory X d r a ha p ⥤
      WfAmbientRationalCategory X d r a ha p where
  obj MN := wfRationalTensorObj X d r a ha p MN.1 MN.2
  map {MN PQ} f := wfRationalTensorHom X d r a ha p MN.1 PQ.1 MN.2 PQ.2 f.1 f.2
  map_id MN := (wfRationalTensor_laws X d r a ha p).1 MN.1 MN.2
  map_comp f g := (wfRationalTensor_laws X d r a ha p).2 _ _ _ _ _ _ f.1 g.1 f.2 g.2

set_option backward.isDefEq.respectTransparency false in
private def wfRestrictId (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    pbcRestrict (𝟙 R) ≅ 𝟭 (pbcModules X R) :=
  NatIso.ofComponents (fun M ↦
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk
        (fun U ↦ (ModuleCat.restrictScalarsId (R.obj.obj U)).app (M.val.obj U))
        (fun {U V} f ↦ by ext x; rfl))) (fun _ ↦ by ext U x; rfl)

set_option backward.isDefEq.respectTransparency false in
private def wfPresentationBackEquiv :
    adicDatumModules X (intrinsicPresentationDatum d) ≌ pbcModules X (pbcAdicCompletion X d) :=
  CategoryTheory.Equivalence.mk (intrinsicPresentationModulesBack X d)
    (intrinsicPresentationModules X d)
    ((pbcRestrictComp (pbcCompletedComparison X d).hom (pbcCompletedComparison X d).inv
        (𝟙 _) (pbcCompletedComparison X d).hom_inv_id ≪≫
      wfRestrictId X _).symm)
    (intrinsicPresentationRoundTrip X d).symm

attribute [local irreducible] pbcCompletedComparison intrinsicPresentationRoundTrip wfRestrictId
attribute [local semireducible] intrinsicCompletionComplex

set_option backward.isDefEq.respectTransparency false in
private theorem wfComplete_of_presentation
    (M : PbcCompletedDerived X d) (s : ℕ) (b : Fin s → A)
    (hb : Ideal.span (Set.range b) = d.ideal)
    (C : CochainComplex (adicDatumModules X (intrinsicPresentationDatum d)) ℤ)
    (eC : (completedConstantQ _).obj C ≅
      (pbcDerivedExtend (pbcCompletedComparison X d).inv).obj M)
    (hC : IsCompletedIntrinsicallyDerivedComplete X (intrinsicPresentationDatum d)
      s b hb C eC) :
    WfIsComplete X d r a ha M := by
  let G := intrinsicPresentationModules X d
  let B := intrinsicPresentationModulesBack X d
  have : B.IsEquivalence := (wfPresentationBackEquiv X d).isEquivalence_functor
  let BD := B.mapDerivedCategory
  let GD := G.mapDerivedCategory
  have hBadd : B.Additive := pbcRestrict_additive _
  have hBD : BD.IsEquivalence := Functor.isEquivalence_mapDerivedCategory B
  let : BD.IsEquivalence := hBD
  have : (pbcDerivedRestrict (pbcCompletedComparison X d).inv).IsEquivalence := by
    change BD.IsEquivalence
    exact hBD
  let adj := pbcDerivedScalarAdjunction (pbcCompletedComparison X d).inv
  have : IsIso adj.unit := by dsimp [adj]; infer_instance
  let D := (B.mapHomologicalComplex (.up ℤ)).obj C
  let eD : DerivedCategory.Q.obj D ≅ M :=
    (B.mapDerivedCategoryFactors.app C).symm ≪≫ BD.mapIso eC ≪≫
      (asIso (adj.unit.app M)).symm
  let C' := (G.mapHomologicalComplex (.up ℤ)).obj D
  let j := (wfPresentationBackEquiv X d).unitIso
  let k : DerivedCategory.Q.obj C' ≅ DerivedCategory.Q.obj C :=
    (DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex j (.up ℤ)).app C)).symm
  obtain ⟨F, η, hF⟩ := completedIntrinsicCompletion_descends X
    (intrinsicPresentationDatum d) s b
  obtain ⟨iC, hiC⟩ := hF C
  obtain ⟨iC', hiC'⟩ := hF C'
  have hu : IsIso ((completedConstantQ _).map
      (completedKoszulUnitComplex X (intrinsicPresentationDatum d) s b C)) := by
    have : IsIso (eC.inv ≫ (completedConstantQ _).map
        (completedKoszulUnitComplex X (intrinsicPresentationDatum d) s b C)) := hC
    exact IsIso.of_isIso_comp_left eC.inv _
  have hη : IsIso (η.app (DerivedCategory.Q.obj C)) := by
    have : IsIso (η.app (DerivedCategory.Q.obj C) ≫ iC.hom) := by
      rw [hiC]
      exact hu
    exact IsIso.of_isIso_comp_right _ iC.hom
  have hη' : IsIso (η.app (DerivedCategory.Q.obj C')) := by
    have hn := η.naturality k.hom
    dsimp only [Functor.id_map] at hn
    have : IsIso (η.app (DerivedCategory.Q.obj C') ≫ F.map k.hom) := by
      rw [← hn]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (F.map k.hom)
  have hu' : IsIso ((completedConstantQ _).map
      (completedKoszulUnitComplex X (intrinsicPresentationDatum d) s b C')) := by
    rw [← hiC']
    infer_instance
  have hq : QuasiIso (completedKoszulUnitComplex X (intrinsicPresentationDatum d) s b C') :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1 hu'
  let t : D ≅ (B.mapHomologicalComplex (.up ℤ)).obj C' :=
    (NatIso.mapHomologicalComplex (intrinsicPresentationRoundTrip X d) (.up ℤ)).app D
  have hcomp : intrinsicCompletionComplexUnit X d s b D =
      t.hom ≫ (B.mapHomologicalComplex (.up ℤ)).map
        (completedKoszulUnitComplex X (intrinsicPresentationDatum d) s b C') := by
    unfold intrinsicCompletionComplexUnit intrinsicCompletionUnitComponent
    ext q
    rfl
  have hDC : QuasiIso (intrinsicCompletionComplexUnit X d s b D) := by
    rw [hcomp]
    infer_instance
  have hQu : IsIso (DerivedCategory.Q.map (intrinsicCompletionComplexUnit X d s b D)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hDC
  have hD : IsDerivedCompleteIntrinsic X d s b hb M D eD := by
    unfold IsDerivedCompleteIntrinsic intrinsicCompletionUnit intrinsicCompletion
    exact IsIso.comp_isIso' eD.isIso_inv hQu
  have : IsIso (intrinsicCompletionUnit X d s b hb M D eD) := hD
  obtain ⟨c, hc⟩ := completedKoszulQuotientComparison X d s b hb M D eD
  have hTower : d.TowerComplete X M := by
    change IsIso (d.completionUnit X M)
    change intrinsicCompletionUnit X d s b hb M D eD ≫ c.hom = d.completionUnit X M at hc
    rw [← hc]
    exact inferInstanceAs (IsIso (intrinsicCompletionUnit X d s b hb M D eD ≫ c.hom))
  exact (d.towerComplete_iff_intrinsic X M).1 hTower r a ha _ _

set_option backward.isDefEq.respectTransparency false in
private theorem wfPresentation_of_complete (M : PbcCompletedDerived X d)
    (hM : WfIsComplete X d r a ha M) : PbcIsIntrinsicallyComplete X d M := by
  let B := intrinsicPresentationModulesBack X d
  let G := intrinsicPresentationModules X d
  let E := wfPresentationBackEquiv X d
  have : B.IsEquivalence := E.isEquivalence_functor
  have : G.IsEquivalence := E.isEquivalence_inverse
  let C := wfCompletionRepresentative X d M
  let C' := (G.mapHomologicalComplex (.up ℤ)).obj C
  let real := DerivedCategory.Q.objObjPreimageIso M
  let adj := pbcDerivedScalarAdjunction (pbcCompletedComparison X d).inv
  have hBadd : E.functor.Additive := by
    exact pbcRestrict_additive _
  have : E.symm.functor.Additive := E.inverse_additive
  have : E.symm.inverse.Additive := hBadd
  let ej := E.symm.mapDerivedCategory.toAdjunction
  let j : G.mapDerivedCategory ≅ pbcDerivedExtend (pbcCompletedComparison X d).inv :=
    Adjunction.leftAdjointUniq ej adj
  let eC : (completedConstantQ _).obj C' ≅
      (pbcDerivedExtend (pbcCompletedComparison X d).inv).obj M :=
    (G.mapDerivedCategoryFactors.app C).symm ≪≫ G.mapDerivedCategory.mapIso real ≪≫ j.app M
  have hu : IsIso (DerivedCategory.Q.map (intrinsicCompletionComplexUnit X d r a C)) := by
    have : IsIso (real.inv ≫ DerivedCategory.Q.map
      (intrinsicCompletionComplexUnit X d r a C)) := by
      unfold WfIsComplete IsDerivedCompleteIntrinsic intrinsicCompletionUnit
        intrinsicCompletion at hM
      exact hM
    exact IsIso.of_isIso_comp_left real.inv _
  have hq : QuasiIso (intrinsicCompletionComplexUnit X d r a C) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1 hu
  let t : C ≅ (B.mapHomologicalComplex (.up ℤ)).obj C' :=
    (NatIso.mapHomologicalComplex (intrinsicPresentationRoundTrip X d) (.up ℤ)).app C
  have hcomp : intrinsicCompletionComplexUnit X d r a C =
      t.hom ≫ (B.mapHomologicalComplex (.up ℤ)).map
        (completedKoszulUnitComplex X (intrinsicPresentationDatum d) r a C') := by
    unfold intrinsicCompletionComplexUnit intrinsicCompletionUnitComponent
    ext q
    rfl
  have hBu : QuasiIso ((B.mapHomologicalComplex (.up ℤ)).map
      (completedKoszulUnitComplex X (intrinsicPresentationDatum d) r a C')) := by
    have : QuasiIso (t.hom ≫ (B.mapHomologicalComplex (.up ℤ)).map
        (completedKoszulUnitComplex X (intrinsicPresentationDatum d) r a C')) := by
      rw [← hcomp]
      exact hq
    exact quasiIso_of_comp_left t.hom _
  have hCu : QuasiIso (completedKoszulUnitComplex X (intrinsicPresentationDatum d) r a C') :=
    (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ B).1 hBu
  refine ⟨r, a, ha, C', eC, ?_⟩
  change IsIso (eC.inv ≫ (completedConstantQ _).map
    (completedKoszulUnitComplex X (intrinsicPresentationDatum d) r a C'))
  infer_instance

attribute [local irreducible] intrinsicCompletionComplex

private theorem wfComplete_iff_presentation (M : PbcCompletedDerived X d) :
    WfIsComplete X d r a ha M ↔ PbcIsIntrinsicallyComplete X d M := by
  constructor
  · exact wfPresentation_of_complete X d r a ha M
  · rintro ⟨s, b, hb, C, eC, hC⟩
    exact wfComplete_of_presentation X d r a ha M s b hb C eC hC

private theorem wfComplete_iso {M N : PbcCompletedDerived X d} (k : M ≅ N) :
    WfIsComplete X d r a ha M ↔ WfIsComplete X d r a ha N := by
  let η : 𝟭 _ ⟶ wfCompletion X d r a ha ⋙ ObjectProperty.ι (WfIsComplete X d r a ha) :=
    { app := wfCompletionUnit X d r a ha
      naturality := fun {_ _} f ↦ (wfCompletion_unit_map X d r a ha f).symm }
  change IsIso (η.app M) ↔ IsIso (η.app N)
  exact NatTrans.isIso_app_iff_of_iso η k

private theorem wfComplete_iff_actualUnit (M : PbcCompletedDerived X d) :
    WfIsComplete X d r a ha M ↔ IsIso ((pbcActualCompletionUnit d X).app M) := by
  let I := ObjectProperty.ι (PbcIsIntrinsicallyComplete X d)
  let adj := Adjunction.ofIsRightAdjoint I
  constructor
  · intro hM
    let L : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete X d) :=
      ⟨M, (wfComplete_iff_presentation X d r a ha M).mp hM⟩
    exact adj.isIso_unit_app_of_iso (X := L) (Iso.refl M)
  · intro hM
    obtain ⟨L, ⟨i⟩⟩ := (adj.isIso_unit_app_iff_mem_essImage).mp hM
    exact (wfComplete_iso X d r a ha i).mp
      ((wfComplete_iff_presentation X d r a ha L.obj).mpr L.property)

variable (e : Aut X)

set_option backward.isDefEq.respectTransparency false in
private theorem wfPullback_preservesComplete :
    (∀ M, WfIsComplete X d r a ha M →
      WfIsComplete X d r a ha ((pbcIsoAmbientPullback e.asIso.hom d).obj M)) ∧
    (∀ M, WfIsComplete X d r a ha M →
      WfIsComplete X d r a ha ((pbcActualDerivedPush e.asIso.hom d).obj M)) := by
  let H := pbcIsoAmbientPullback e.asIso.hom d
  let G := pbcActualDerivedPush e.asIso.hom d
  let adj : H ⊣ G := (pbcActualDerivedAdjunction e.asIso.hom d).ofNatIsoLeft
    (pbcIsoOrdinaryDerivedComparison e.asIso.hom d)
  have : H.IsEquivalence := inferInstance
  have : G.IsEquivalence := adj.isEquivalence_right_of_isEquivalence_left
  have hCompletion := pbcActualDirectCompletionIso_exists e.asIso.hom d
  obtain ⟨c, hc⟩ := hCompletion.exists
  have hG (M : PbcCompletedDerived X d) :
      WfIsComplete X d r a ha (G.obj M) ↔ WfIsComplete X d r a ha M := by
    rw [wfComplete_iff_actualUnit, wfComplete_iff_actualUnit]
    exact WfTensorLinearity.reflectsComplete (pbcActualCompletion d X) G
      (pbcActualCompletionUnit d X) c hc M
  refine ⟨?_, fun M hM ↦ (hG M).mpr hM⟩
  intro M hM
  apply (hG (H.obj M)).mp
  exact (wfComplete_iso X d r a ha (asIso (adj.unit.app M))).mp hM

set_option backward.isDefEq.respectTransparency false in
/-- The completion comparison is uniquely fixed by its unit square.
Source: blueprint order 2107 (blueprint: prose-03-02).
Proof: compare the canonical Koszul completeness predicate with completeness in the
presentation category, using the exact coefficient equivalence and independence of the
Koszul representative and generating list. Direct image commutes with completion and
its unit. For an automorphism, ordinary derived pullback and direct image are adjoint
equivalences; thus each preserves complete objects. Transport the reflector's Hom
bijection through this adjunction to obtain the universal property of the pulled-back
completion. The unique maps between the two reflections are inverse, and the same
Hom bijection proves uniqueness with the required unit equation. -/
theorem wfPullbackCompletion_exists (M : PbcCompletedDerived X d) :
    ∃! c : (pbcIsoAmbientPullback e.asIso.hom d).obj (wfCompletionObj X d r a ha M) ≅
        wfCompletionObj X d r a ha ((pbcIsoAmbientPullback e.asIso.hom d).obj M),
      (pbcIsoAmbientPullback e.asIso.hom d).map (wfCompletionUnit X d r a ha M) ≫ c.hom =
        wfCompletionUnit X d r a ha ((pbcIsoAmbientPullback e.asIso.hom d).obj M) := by
  let H := pbcIsoAmbientPullback e.asIso.hom d
  let G := pbcActualDerivedPush e.asIso.hom d
  let adj : H ⊣ G := (pbcActualDerivedAdjunction e.asIso.hom d).ofNatIsoLeft
    (pbcIsoOrdinaryDerivedComparison e.asIso.hom d)
  have hH := (wfPullback_preservesComplete X d r a ha e).1
  have hG := (wfPullback_preservesComplete X d r a ha e).2
  have hbij (L : PbcCompletedDerived X d) (hL : WfIsComplete X d r a ha L) :
      Function.Bijective (fun f : H.obj (wfCompletionObj X d r a ha M) ⟶ L ↦
        H.map (wfCompletionUnit X d r a ha M) ≫ f) := by
    have h := (wfCompletionReflector X d r a ha).2 M (G.obj L) (hG L hL)
    constructor
    · intro f g hfg
      apply (adj.homEquiv _ _).injective
      apply h.injective
      dsimp only at hfg ⊢
      rw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_left, hfg]
    · intro f
      obtain ⟨g, hg⟩ := h.surjective ((adj.homEquiv M L) f)
      refine ⟨(adj.homEquiv _ _).symm g, ?_⟩
      apply (adj.homEquiv M L).injective
      rw [adj.homEquiv_naturality_left, Equiv.apply_symm_apply]
      exact hg
  have hsource : WfIsComplete X d r a ha (H.obj (wfCompletionObj X d r a ha M)) :=
    hH _ ((wfCompletionReflector X d r a ha).1 M)
  have htarget := (wfCompletionReflector X d r a ha).1 (H.obj M)
  obtain ⟨f, hf⟩ := (hbij _ htarget).surjective
    (wfCompletionUnit X d r a ha (H.obj M))
  obtain ⟨g, hg⟩ := ((wfCompletionReflector X d r a ha).2 (H.obj M) _ hsource).surjective
    (H.map (wfCompletionUnit X d r a ha M))
  dsimp only at hf hg
  let c : H.obj (wfCompletionObj X d r a ha M) ≅
      wfCompletionObj X d r a ha (H.obj M) :=
    { hom := f
      inv := g
      hom_inv_id := by
        apply (hbij _ hsource).injective
        dsimp only
        rw [← Category.assoc, hf, hg, Category.comp_id]
      inv_hom_id := by
        apply ((wfCompletionReflector X d r a ha).2 (H.obj M) _ htarget).injective
        dsimp only
        rw [← Category.assoc, hg, hf, Category.comp_id] }
  refine ⟨c, hf, ?_⟩
  intro c' hc'
  apply Iso.ext
  exact (hbij _ htarget).injective (hc'.trans hf.symm)

set_option backward.isDefEq.respectTransparency false in
/-- Exact coefficient transport preserves intrinsic completeness for the actual scalar list.
Source: blueprint order 2107 (blueprint: prose-03-02).
Proof: the finite coefficient comparisons preserve every constant section a_j, and commute
with quotient maps. Their limit fixes a_j on the completed ring. Apply the exact inverse
site equivalences to the strict Koszul tower. They preserve products and both finite
fiber summands; the projection comparison commutes with 1-shift and with the signed
fiber differential. It identifies the (u,0) units, hence preserves their invertibility. -/
theorem wfIsoPullback_complete (M : WfCompleteCategory X d r a ha) :
    WfIsComplete X d r a ha ((pbcIsoAmbientPullback e.asIso.hom d).obj M.obj) := by
  change IsIso (wfCompletionUnit X d r a ha
    ((pbcIsoAmbientPullback e.asIso.hom d).obj M.obj))
  obtain ⟨c, hc, _⟩ := wfPullbackCompletion_exists X d r a ha e M.obj
  have : IsIso (wfCompletionUnit X d r a ha M.obj) := M.property
  rw [← hc]
  infer_instance

/-- The same exact transport on all complete objects, before raw rationalization.
Source: blueprint order 2107 (blueprint: prose-03-02). -/
def wfCompletePullback : WfCompleteCategory X d r a ha ⥤ WfCompleteCategory X d r a ha :=
  ObjectProperty.lift (WfIsComplete X d r a ha)
    (ObjectProperty.ι (WfIsComplete X d r a ha) ⋙ pbcIsoAmbientPullback e.asIso.hom d)
    (wfIsoPullback_complete X d r a ha e)

attribute [local semireducible] pbcCompletedComparison

set_option backward.isDefEq.respectTransparency false in
private theorem wfCompletedScalar_projection (n : ℕ) :
    pbcCompletedScalar X d ≫ pbcAdicProjection X d n =
      (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (Ideal.Quotient.mk (d.ideal ^ (n + 1)))) ≫
          (pbcLevelConstantComparison X d n).hom := by
  dsimp only [pbcCompletedScalar, pbcCompletedComparison, pbcAdicProjection]
  rw [Category.assoc]
  erw [HasLimit.isoOfNatIso_hom_π]
  rw [← Category.assoc]
  erw [(adicDatumScalar_exists X
    { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum,
      quotientFinite := d.quotientFinite }).exists.choose_spec n]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem wfCompletedScalar_pullback :
    proEtaleConstantInverseImageMap e.asIso.hom CommRingCat.{u + 1} (CommRingCat.of A) ≫
        pbcCompletedScalar X d =
      (proEtaleSheafInverseImage e.asIso.hom CommRingCat.{u + 1}).map
        (pbcCompletedScalar X d) ≫ completedCoefficientMap e.asIso.hom d := by
  let F := proEtaleSheafInverseImage e.asIso.hom CommRingCat.{u + 1}
  apply limit.hom_ext (F := pbcAdicRings X d)
  intro n
  change _ ≫ pbcAdicProjection X d n.unop = _ ≫ pbcAdicProjection X d n.unop
  rw [Category.assoc, wfCompletedScalar_projection]
  rw [Category.assoc]
  have hp : completedCoefficientMap e.asIso.hom d ≫ pbcAdicProjection X d n.unop =
      completedCoefficientComponent e.asIso.hom d n.unop := limit.lift_π _ n
  rw [hp]
  dsimp only [completedCoefficientComponent, completedFiniteCoefficientMap]
  rw [← F.map_comp_assoc, wfCompletedScalar_projection]
  rw [F.map_comp]
  simp only [Category.assoc]
  rw [← CategoryTheory.Functor.map_comp_assoc _ (pbcLevelConstantComparison X d n.unop).hom
    (pbcLevelConstantComparison X d n.unop).inv, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
    Category.id_comp]
  simpa only [Category.assoc] using congrArg
    (fun z ↦ z ≫ (pbcLevelConstantComparison X d n.unop).hom)
    ((proEtaleIso_constantComparison e.asIso.hom CommRingCat.{u + 1}).2
      (CommRingCat.of A) (CommRingCat.of (A ⧸ d.ideal ^ (n.unop + 1)))
      (CommRingCat.ofHom (Ideal.Quotient.mk (d.ideal ^ (n.unop + 1)))))

set_option backward.isDefEq.respectTransparency false in
private theorem wfCompletedScalar_directImage :
    pbcCompletedScalar X d ≫ proEtaleRingDirectImageMap e.asIso.hom
        (pbcAdicCompletion X d) (pbcAdicCompletion X d)
          (asIso (completedCoefficientMap e.asIso.hom d)) =
      proEtaleConstantDirectImageMap e.asIso.hom CommRingCat.{u + 1} (CommRingCat.of A) ≫
        (proEtaleSheafDirectImage e.asIso.hom CommRingCat.{u + 1}).map
          (pbcCompletedScalar X d) := by
  let G := proEtaleSheafDirectImage e.asIso.hom CommRingCat.{u + 1}
  let adj := proEtaleSheafAdjunction e.asIso.hom CommRingCat.{u + 1}
  dsimp only [proEtaleRingDirectImageMap, asIso_hom]
  have hn := adj.unit.naturality (pbcCompletedScalar X d)
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  rw [← Category.assoc, hn]
  rw [Category.assoc, ← G.map_comp, ← wfCompletedScalar_pullback X d e, G.map_comp,
    ← Category.assoc]
  congr 1
  exact (adj.homEquiv _ _).apply_symm_apply _

set_option backward.isDefEq.respectTransparency false in
private theorem wfCompletedSection_directImage (U : X.ProEtᵒᵖ) (b : A) :
    (proEtaleRingDirectImageMap e.asIso.hom (pbcAdicCompletion X d) (pbcAdicCompletion X d)
      (asIso (completedCoefficientMap e.asIso.hom d))).hom.app U (pbcCompletedSection X d U b) =
        pbcCompletedSection X d ((proEtaleBaseChange e.asIso.hom).op.obj U) b := by
  have hn := Equiv.apply_symm_apply
    ((sheafificationAdjunction (ProEt.topology X) CommRingCat.{u + 1}).homEquiv
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A))
      ((proEtaleSheafDirectImage e.asIso.hom CommRingCat.{u + 1}).obj
        ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj (CommRingCat.of A))))
    (Functor.whiskerLeft (proEtaleBaseChange e.asIso.hom).op
      (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A))))
  change _ ≫ (proEtaleConstantDirectImageMap e.asIso.hom CommRingCat.{u + 1}
    (CommRingCat.of A)).hom = _ at hn
  have hu := ConcreteCategory.congr_hom (congr_app hn U) b
  change (proEtaleConstantDirectImageMap e.asIso.hom CommRingCat.{u + 1}
      (CommRingCat.of A)).hom.app U
        ((toSheafify (ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A))).app U b) =
    (toSheafify (ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A))).app
        ((proEtaleBaseChange e.asIso.hom).op.obj U) b at hu
  have h := ConcreteCategory.congr_hom
    (congrArg (fun z ↦ z.hom.app U) (wfCompletedScalar_directImage X d e))
      ((toSheafify (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A))).app U b)
  change _ = (pbcCompletedScalar X d).hom.app
    ((proEtaleBaseChange e.asIso.hom).op.obj U)
      ((proEtaleConstantDirectImageMap e.asIso.hom CommRingCat.{u + 1}
        (CommRingCat.of A)).hom.app U _) at h
  rw [hu] at h
  exact h

/-- Constant sections are fixed by the completed coefficient identification.
Source: blueprint order 2107 (blueprint: prose-03-02).
Proof: check the scalar action after every finite quotient projection. The constant
inverse-image comparison is adjoint to identity on constants, so fixes each residue.
The limit map therefore fixes every scalar. The sectionwise linear equation descends
through complexes and localization, and restricts to the complete full subcategory. -/
theorem wfCompletePullback_linear :
    (wfCompletePullback X d r a ha e).Additive ∧
      (wfCompletePullback X d r a ha e).Linear A := by
  have hAdd : (pbcIsoModulePullback e.asIso.hom d).Additive := by
    rw [pbcIsoModulePullback_eq_completed]
    infer_instance
  have : (pbcIsoAmbientPullback e.asIso.hom d).Additive := inferInstance
  constructor
  · constructor
    intro M N f g
    apply ObjectProperty.hom_ext
    exact (pbcIsoAmbientPullback e.asIso.hom d).map_add
  · let G := proEtaleRingModuleDirectImage e.asIso.hom (pbcAdicCompletion X d)
      (pbcAdicCompletion X d) (asIso (completedCoefficientMap e.asIso.hom d))
    have : G.Linear A := by
      constructor
      intro M N f b
      ext U x
      change pbcCompletedSection X d ((proEtaleBaseChange e.asIso.hom).op.obj U) b •
          ((f.val.app ((proEtaleBaseChange e.asIso.hom).op.obj U)).hom x) =
        (proEtaleRingDirectImageMap e.asIso.hom (pbcAdicCompletion X d) (pbcAdicCompletion X d)
          (asIso (completedCoefficientMap e.asIso.hom d))).hom.app U
            (pbcCompletedSection X d U b) •
              ((f.val.app ((proEtaleBaseChange e.asIso.hom).op.obj U)).hom x)
      rw [wfCompletedSection_directImage]
    have : (pbcIsoModulePullback e.asIso.hom d).Linear A :=
      (proEtaleRingModuleAdjunction e.asIso.hom (pbcAdicCompletion X d) (pbcAdicCompletion X d)
        (asIso (completedCoefficientMap e.asIso.hom d))).left_adjoint_linear
    have : (pbcIsoAmbientPullback e.asIso.hom d).Linear A := inferInstance
    constructor
    intro M N f b
    apply ObjectProperty.hom_ext
    exact (pbcIsoAmbientPullback e.asIso.hom d).map_smul b f.hom

/-- The additive part of the specified coefficient transport.
Source: blueprint order 2107 (blueprint: prose-03-02). -/
instance wfCompletePullback_additive : (wfCompletePullback X d r a ha e).Additive :=
  (wfCompletePullback_linear X d r a ha e).1

/-- The A-linear part of the specified coefficient transport.
Source: blueprint order 2107 (blueprint: prose-03-02). -/
instance wfCompletePullback_isLinear : (wfCompletePullback X d r a ha e).Linear A :=
  (wfCompletePullback_linear X d r a ha e).2

/-- Frobenius transport on the ambient raw rationalization, on every complete object.
Source: blueprint order 2107 (blueprint: prose-03-02). -/
abbrev wfAmbientRationalPullback (p : A) :=
  ScalarLocalization.map A (WfCompleteCategory X d r a ha) p
    (wfCompletePullback X d r a ha e)

/-- The specified product/fiber comparison, determined equivalently by the unit square.
Source: blueprint order 2107 (blueprint: prose-03-02). -/
def wfPullbackCompletion (M : PbcCompletedDerived X d) :=
  (wfPullbackCompletion_exists X d r a ha e M).exists.choose

/-- The integral comparison is the completed canonical derived tensor comparison.
Source: blueprint order 2107 (blueprint: prose-03-02). -/
def wfIntegralTensorPullback (M N : WfCompleteCategory X d r a ha) :
    (wfCompletePullback X d r a ha e).obj ((wfIntegralTensor X d r a ha).obj (M, N)) ≅
      (wfIntegralTensor X d r a ha).obj
        ((wfCompletePullback X d r a ha e).obj M, (wfCompletePullback X d r a ha e).obj N) :=
  ObjectProperty.isoMk _
    (wfPullbackCompletion X d r a ha e ((wfOrdinaryDerivedTensor X d).obj (M.obj, N.obj)) ≪≫
      (ObjectProperty.ι (WfIsComplete X d r a ha)).mapIso
        ((wfCompletion X d r a ha).mapIso
          ((proEtaleCanonicalTensorComparison e.asIso.hom (pbcAdicCompletion X d)
            (pbcAdicCompletion X d) (asIso (completedCoefficientMap e.asIso.hom d))
            (wfTensorModel X d) (wfTensorModel X d)).app (M.obj, N.obj))))

private theorem wfPullbackCompletion_naturality {M N : PbcCompletedDerived X d}
    (f : M ⟶ N) :
    (pbcIsoAmbientPullback e.asIso.hom d).map (((wfCompletion X d r a ha).map f).hom) ≫
        (wfPullbackCompletion X d r a ha e N).hom =
      (wfPullbackCompletion X d r a ha e M).hom ≫
        ((wfCompletion X d r a ha).map ((pbcIsoAmbientPullback e.asIso.hom d).map f)).hom := by
  let H := pbcIsoAmbientPullback e.asIso.hom d
  let cM := wfPullbackCompletion X d r a ha e M
  have hc (K : PbcCompletedDerived X d) :
      H.map (wfCompletionUnit X d r a ha K) ≫
          (wfPullbackCompletion X d r a ha e K).hom =
        wfCompletionUnit X d r a ha (H.obj K) :=
    (wfPullbackCompletion_exists X d r a ha e K).exists.choose_spec
  apply (cancel_epi cM.inv).1
  apply ((wfCompletionReflector X d r a ha).2 (H.obj M)
    (wfCompletionObj X d r a ha (H.obj N))
    ((wfCompletionReflector X d r a ha).1 (H.obj N))).1
  have hm : wfCompletionUnit X d r a ha (H.obj M) ≫ cM.inv =
      H.map (wfCompletionUnit X d r a ha M) := by
    rw [← hc M, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  dsimp only
  rw [← Category.assoc, hm, ← Category.assoc, ← H.map_comp,
    wfCompletion_unit_map, H.map_comp, Category.assoc, hc N]
  change H.map f ≫ wfCompletionUnit X d r a ha (H.obj N) =
    wfCompletionUnit X d r a ha (H.obj M) ≫ cM.inv ≫ cM.hom ≫
      ((wfCompletion X d r a ha).map (H.map f)).hom
  rw [Iso.inv_hom_id_assoc, wfCompletion_unit_map]

set_option backward.isDefEq.respectTransparency false in
private theorem wfIntegralTensorPullback_naturality
    {M M' N N' : WfCompleteCategory X d r a ha} (f : M ⟶ M') (g : N ⟶ N') :
    (wfCompletePullback X d r a ha e).map
        ((wfIntegralTensor X d r a ha).map (Prod.mkHom f g)) ≫
          (wfIntegralTensorPullback X d r a ha e M' N').hom =
      (wfIntegralTensorPullback X d r a ha e M N).hom ≫
        (wfIntegralTensor X d r a ha).map (Prod.mkHom
          ((wfCompletePullback X d r a ha e).map f)
          ((wfCompletePullback X d r a ha e).map g)) := by
  apply ObjectProperty.hom_ext
  let T := wfOrdinaryDerivedTensor X d
  let H := pbcIsoAmbientPullback e.asIso.hom d
  let L := wfCompletion X d r a ha
  let alpha := proEtaleCanonicalTensorComparison e.asIso.hom (pbcAdicCompletion X d)
    (pbcAdicCompletion X d) (asIso (completedCoefficientMap e.asIso.hom d))
    (wfTensorModel X d) (wfTensorModel X d)
  change H.map ((L.map (T.map (Prod.mkHom f.hom g.hom))).hom) ≫
      (wfPullbackCompletion X d r a ha e (T.obj (M'.obj, N'.obj))).hom ≫
        (L.map (alpha.hom.app (M'.obj, N'.obj))).hom =
    ((wfPullbackCompletion X d r a ha e (T.obj (M.obj, N.obj))).hom ≫
      (L.map (alpha.hom.app (M.obj, N.obj))).hom) ≫
        (L.map (T.map (Prod.mkHom (H.map f.hom) (H.map g.hom)))).hom
  rw [← Category.assoc, wfPullbackCompletion_naturality, Category.assoc]
  rw [Category.assoc]
  congr 1
  exact congrArg ((ObjectProperty.ι (WfIsComplete X d r a ha)).map)
    ((Functor.whiskerRight alpha.hom L).naturality (Prod.mkHom f.hom g.hom))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Rationalizing the constructed integral comparison fixes every component uniquely.
Source: blueprint order 2107 (blueprint: prose-03-02).
Proof: tensor with one the integral comparison and its inverse on Hom modules. The
integral comparison is natural by naturality of the canonical tensor comparison and
of the product/fiber comparison. Its naturality extends to all fractions by A-linearity
and inversion of p. Every object is an original integral object, so the component
formula gives uniqueness. The two displayed directions are thus fixed, not chosen. -/
theorem wfRationalTensorPullback_exists (p : A) :
    ∃! mu : wfRationalTensor X d r a ha p ⋙ wfAmbientRationalPullback X d r a ha e p ≅
        ((wfAmbientRationalPullback X d r a ha e p).prod
          (wfAmbientRationalPullback X d r a ha e p)) ⋙ wfRationalTensor X d r a ha p,
      ∀ M N : WfCompleteCategory X d r a ha,
        mu.hom.app (⟨M⟩, ⟨N⟩) =
          (ScalarLocalization.localization A (WfCompleteCategory X d r a ha) p).map
            (wfIntegralTensorPullback X d r a ha e M N).hom  := by
  let Q := ScalarLocalization.localization A (WfCompleteCategory X d r a ha) p
  let mu : wfRationalTensor X d r a ha p ⋙ wfAmbientRationalPullback X d r a ha e p ≅
      ((wfAmbientRationalPullback X d r a ha e p).prod
        (wfAmbientRationalPullback X d r a ha e p)) ⋙ wfRationalTensor X d r a ha p :=
    NatIso.ofComponents
    (fun MN ↦ Q.mapIso
      (wfIntegralTensorPullback X d r a ha e MN.1.obj MN.2.obj)) (by
        intro MN PQ v
        rcases MN with ⟨M, N⟩
        rcases PQ with ⟨M', N'⟩
        rcases v with ⟨f, g⟩
        change ScalarLocalization.composition A (WfCompleteCategory X d r a ha) p _ _ _
            (1 ⊗ₜ[A] (wfIntegralTensorPullback X d r a ha e M'.obj N'.obj).hom)
            (ScalarLocalization.mapHom A (WfCompleteCategory X d r a ha) p
              (wfCompletePullback X d r a ha e) _ _
              (wfRationalTensorHom X d r a ha p M M' N N' f g)) =
          ScalarLocalization.composition A (WfCompleteCategory X d r a ha) p _ _ _
            (wfRationalTensorHom X d r a ha p _ _ _ _
              (ScalarLocalization.mapHom A (WfCompleteCategory X d r a ha) p
                (wfCompletePullback X d r a ha e) _ _ f)
              (ScalarLocalization.mapHom A (WfCompleteCategory X d r a ha) p
                (wfCompletePullback X d r a ha e) _ _ g))
            (1 ⊗ₜ[A] (wfIntegralTensorPullback X d r a ha e M.obj N.obj).hom)
        exact scalarLocalization_bilinear_naturality p
          (wfCompletePullback X d r a ha e)
          (wfRationalTensorHom X d r a ha p M M' N N')
          (wfRationalTensorHom X d r a ha p _ _ _ _)
          (fun f g ↦ (wfIntegralTensor X d r a ha).map (Prod.mkHom f g))
          (fun f g ↦ (wfIntegralTensor X d r a ha).map (Prod.mkHom f g))
          (wfRationalTensorHom_tmul X d r a ha p M M' N N')
          (wfRationalTensorHom_tmul X d r a ha p _ _ _ _)
          (wfIntegralTensorPullback X d r a ha e M.obj N.obj).hom
          (wfIntegralTensorPullback X d r a ha e M'.obj N'.obj).hom
          (wfIntegralTensorPullback_naturality X d r a ha e) f g)
  refine ⟨mu, (fun M N ↦ rfl), ?_⟩
  intro nu hnu
  apply Iso.ext
  apply NatTrans.ext
  funext MN
  exact hnu MN.1.obj MN.2.obj

/-- The typed pullback/tensor comparison in the displayed direction of the source.
Source: blueprint order 2107 (blueprint: prose-03-02). -/
def wfRationalTensorPullback (p : A) :=
  (wfRationalTensorPullback_exists X d r a ha e p).exists.choose

/-- The exact PBC integral subcategory lies in this same intrinsically complete category.
Source: blueprint order 2107 (blueprint: prose-03-02).
Proof: its first defining condition supplies an intrinsic-completion witness after the
canonical completed-ring presentation comparison. The mutually inverse exact coefficient
restrictions preserve the strict Koszul tower and unit. The Koszul reflector shows
independence of the generating tuple and representative. Therefore the canonical
representative and the given generating tuple have invertible intrinsic unit. -/
theorem wfConstructible_complete (M : PbcBoundedConstructibleComplete X d) :
    WfIsComplete X d r a ha M.obj := by
  obtain ⟨s, b, hb, C, eC, hC⟩ := M.property.1
  exact wfComplete_of_presentation X d r a ha M.obj s b hb C eC hC

/-- Inclusion of the specified constructible objects, retaining all their derived arrows.
Source: blueprint order 2107 (blueprint: prose-03-02). -/
def wfIntegralConstructibleInclusion :
    PbcBoundedConstructibleComplete X d ⥤ WfCompleteCategory X d r a ha :=
  ObjectProperty.lift (WfIsComplete X d r a ha)
    (ObjectProperty.ι (PbcIsBoundedConstructibleComplete X d))
    (wfConstructible_complete X d r a ha)

/-- The inclusion on rational coefficients is uniquely determined by integral localization.
Source: blueprint order 2107 (blueprint: prose-03-02).
Proof: the inclusion is A-linear since its underlying maps are unchanged. Extend its
Hom maps by tensor with the identity of A[1/p]. This respects the given composition
and identity formulas. Every localized morphism is a fraction of an integral morphism,
and the objects are unchanged, so the equality determines the functor uniquely. -/
theorem wfConstructibleInclusion_exists (p : A) :
    ∃! F : PbcRationalCategory X d p ⥤ WfAmbientRationalCategory X d r a ha p,
      pbcRationalization X d p ⋙ F =
        wfIntegralConstructibleInclusion X d r a ha ⋙
          ScalarLocalization.localization A (WfCompleteCategory X d r a ha) p := by
  let I := wfIntegralConstructibleInclusion X d r a ha
  let : I.Additive := ⟨fun {_ _ _ _} ↦ rfl⟩
  let : I.Linear A := ⟨fun {_ _} _ _ ↦ rfl⟩
  let F : PbcRationalCategory X d p ⥤ WfAmbientRationalCategory X d r a ha p :=
    { obj := fun M ↦ ⟨I.obj M.obj⟩
      map := fun f ↦ (I.mapLinearMap A).baseChange (Localization.Away p) f
      map_id := fun M ↦ by
        change (I.mapLinearMap A).baseChange (Localization.Away p)
          (1 ⊗ₜ[A] 𝟙 M.obj) = (1 : Localization.Away p) ⊗ₜ[A] 𝟙 (I.obj M.obj)
        rw [LinearMap.baseChange_tmul]
        rfl
      map_comp := fun {M N P} f g ↦ by
        change (I.mapLinearMap A).baseChange (Localization.Away p)
            (ScalarLocalization.composition A _ p _ _ _ g f) =
          ScalarLocalization.composition A _ p _ _ _
            ((I.mapLinearMap A).baseChange (Localization.Away p) g)
            ((I.mapLinearMap A).baseChange (Localization.Away p) f)
        induction f using TensorProduct.inductionOn with
        | add f f' hf hf' => simp only [map_add, hf, hf']
        | tmul s f =>
          induction g using TensorProduct.inductionOn with
          | add g g' hg hg' => simp only [map_add, LinearMap.add_apply, hg, hg']
          | tmul t g => simp only [ScalarLocalization.composition_tmul, LinearMap.baseChange_tmul,
              Functor.coe_mapLinearMap, Functor.map_comp] }
  have hF : pbcRationalization X d p ⋙ F = I ⋙
      ScalarLocalization.localization A (WfCompleteCategory X d r a ha) p := by
    refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
    intro M N f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    exact LinearMap.baseChange_tmul (I.mapLinearMap A) 1 f
  refine ⟨F, hF, ?_⟩
  intro G hG
  exact scalarLocalization_precomp_injective p G F (hG.trans hF.symm)

/-- The raw rational inclusion with its actual unchanged integral object function.
Source: blueprint order 2107 (blueprint: prose-03-02). -/
def wfConstructibleInclusion (p : A) :=
  (wfConstructibleInclusion_exists X d r a ha p).exists.choose

/-- Inclusion commutes with the same coefficient transport, normalized by identity on objects.
Source: blueprint order 2107 (blueprint: prose-03-02).
Proof: both inclusions and both pullbacks act on the same ambient derived objects and
maps. Their integral composites agree after the faithful ambient inclusion. The unique
rational extension retains these object identities and sends every integral arrow to
itself tensored with one. Thus the displayed object equality is literal. -/
theorem wfConstructiblePullback_obj (p : A) (M : PbcRationalCategory X d p) :
    (wfAmbientRationalPullback X d r a ha e p).obj
        ((wfConstructibleInclusion X d r a ha p).obj M) =
      (wfConstructibleInclusion X d r a ha p).obj
        ((pbcRationalIsoPullback e d p).obj M) := by
  have hobj (K : PbcBoundedConstructibleComplete X d) :
      (wfConstructibleInclusion X d r a ha p).obj ⟨K⟩ =
        (ScalarLocalization.localization A (WfCompleteCategory X d r a ha) p).obj
          ((wfIntegralConstructibleInclusion X d r a ha).obj K) :=
    Functor.congr_obj (wfConstructibleInclusion_exists X d r a ha p).exists.choose_spec K
  rcases M with ⟨M⟩
  change (wfAmbientRationalPullback X d r a ha e p).obj
      ((wfConstructibleInclusion X d r a ha p).obj ⟨M⟩) =
    (wfConstructibleInclusion X d r a ha p).obj ⟨(pbcIsoIntegralPullback e.asIso.hom d).obj M⟩
  rw [hobj, hobj]
  apply congrArg (ScalarLocalization.mk (R := A) (p := p))
  apply ObjectProperty.FullSubcategory.ext
  rfl

end AlgebraicGeometry.Scheme

namespace WeilConjectures
open AlgebraicGeometry AlgebraicGeometry.Scheme

-- These boundaries must remain active in the namespace that constructs the Weil maps.
attribute [local irreducible] wfRationalTensor wfConstructibleInclusion
  wfRationalTensorPullback intrinsicCompletion intrinsicCompletionUnit
  intrinsicCompletionComplex intrinsicCompletionComplexUnit
  ScalarLocalization.category ScalarLocalization.preadditive
  ScalarLocalization.linear ScalarLocalization.linearOriginal

variable (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
  (X₀ : Over (Spec (CommRingCat.of D.k₀)))
  [IsSeparated X₀.hom] [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  (E : Padic.FiniteCoefficientFields c.l c.Qbar)

/-- The singleton generator is exactly the stipulated uniformizer ideal.
Source: blueprint order 2107 (blueprint: prose-03-02).
Proof: the range of the constant function on Fin 1 is the singleton uniformizer, and
pbcIntegralDatum defines its ideal as the span of that singleton. -/
theorem wfUniformizer_generates :
    Ideal.span (Set.range (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)) =
      (pbcStageDatum.{u} c.l c.Qbar E).ideal := by
  rw [Set.range_const]
  change Ideal.span {pbcUniformizer c.l (pbcFiniteField c.l c.Qbar E)} = _
  rfl

/-- The actual ambient rational category at the finite coefficient field E.
Source: blueprint order 2107 (blueprint: prose-03-02). -/
abbrev WfAmbient := WfAmbientRationalCategory (D.geometricFiber X₀).left
  (pbcStageDatum.{u} c.l c.Qbar E) 1 (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)
  (wfUniformizer_generates D c E) (pbcStageUniformizer.{u} c.l c.Qbar E)

/-- Completed tensor at E on arbitrary ambient objects, with the specified scalar ring.
Source: blueprint order 2107 (blueprint: prose-03-02). -/
abbrev wfTensor := wfRationalTensor (D.geometricFiber X₀).left
  (pbcStageDatum.{u} c.l c.Qbar E) 1 (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)
  (wfUniformizer_generates D c E) (pbcStageUniformizer.{u} c.l c.Qbar E)

/-- Geometric Frobenius on this ambient category, using the coefficient-limit identification.
Source: blueprint order 2107 (blueprint: prose-03-02). -/
abbrev wfAmbientFrobenius := wfAmbientRationalPullback (D.geometricFiber X₀).left
  (pbcStageDatum.{u} c.l c.Qbar E) 1 (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)
  (wfUniformizer_generates D c E) (D.geometricFrobenius X₀) (pbcStageUniformizer.{u} c.l c.Qbar E)

/-- Inclusion of the node's Weil-complex carriers into the stipulated ambient category.
Source: blueprint order 2107 (blueprint: prose-03-02). -/
abbrev wfWeilCarrier (K : WeilD D c X₀ E) : WfAmbient D c X₀ E :=
  (wfConstructibleInclusion (D.geometricFiber X₀).left
    (pbcStageDatum.{u} c.l c.Qbar E) 1 (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)
    (wfUniformizer_generates D c E) (pbcStageUniformizer.{u} c.l c.Qbar E)).obj K.carrier

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The given Weil isomorphism, transported by the faithful ambient coefficient inclusion.
Source: blueprint order 2107 (blueprint: prose-03-02). -/
def wfWeilStructure (K : WeilD D c X₀ E) :
    (wfAmbientFrobenius D c X₀ E).obj (wfWeilCarrier D c X₀ E K) ≅
      wfWeilCarrier D c X₀ E K :=
  eqToIso (wfConstructiblePullback_obj (D.geometricFiber X₀).left
    (pbcStageDatum.{u} c.l c.Qbar E) 1 (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)
    (wfUniformizer_generates D c E) (D.geometricFrobenius X₀)
    (pbcStageUniformizer.{u} c.l c.Qbar E) K.carrier) ≪≫
      (wfConstructibleInclusion (D.geometricFiber X₀).left
        (pbcStageDatum.{u} c.l c.Qbar E) 1 (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)
        (wfUniformizer_generates D c E) (pbcStageUniformizer.{u} c.l c.Qbar E)).mapIso K.str

attribute [local irreducible] wfWeilStructure

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Tensor Frobenius is mu followed by tensor of the two given Weil isomorphisms.
The output is ambient; restriction to an exact bifunctor of Weil complexes is separate.
Source: blueprint order 2107 (blueprint: prose-03-02). -/
def wfTensorFrobenius (K L : WeilD D c X₀ E) :
    (wfAmbientFrobenius D c X₀ E).obj
        ((wfTensor D c X₀ E).obj (wfWeilCarrier D c X₀ E K, wfWeilCarrier D c X₀ E L)) ≅
      (wfTensor D c X₀ E).obj (wfWeilCarrier D c X₀ E K, wfWeilCarrier D c X₀ E L) := by
  let make {C : Type _} [Category.{_} C] (T : C × C ⥤ C) (F : C ⥤ C)
      (μ : T ⋙ F ≅ (F.prod F) ⋙ T) {M N : C}
      (α : F.obj M ≅ M) (β : F.obj N ≅ N) :
      F.obj (T.obj (M, N)) ≅ T.obj (M, N) :=
    μ.app (M, N) ≪≫ T.mapIso (Iso.prod α β)
  exact make (wfTensor D c X₀ E) (wfAmbientFrobenius D c X₀ E)
    (wfRationalTensorPullback (D.geometricFiber X₀).left (pbcStageDatum.{u} c.l c.Qbar E)
      1 (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E) (wfUniformizer_generates D c E)
      (D.geometricFrobenius X₀) (pbcStageUniformizer.{u} c.l c.Qbar E))
    (wfWeilStructure D c X₀ E K) (wfWeilStructure D c X₀ E L)

end WeilConjectures

namespace WeilConjectures

open scoped CategoryTheory.Obj
open AlgebraicGeometry AlgebraicGeometry.ProEtale CategoryTheory.Endofunctor

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})

variable {Y} (g : Y ⟶ Y)

end WeilConjectures
