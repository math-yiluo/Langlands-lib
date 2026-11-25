/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleCoefficientSheaf
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ModuleDerivedCategory
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleCoefficientHomologyTriangulated
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Homology.ChangeOfRingsComplex
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Homology.HomologicalComplex
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
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorCancellation
import Mathlib.Algebra.Homology.Functor
import Mathlib.Data.Fin.SuccPred
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Finite coefficient filtrations preserve constructibility and cohomological bounds

Source: Stacks Project, proetale.tex, Tag 09B5, lemma-constructible-serre;
agent-written finite-filtration application
(blueprint: lem-sf-filtered-coefficient-tensor-bounds).

The coefficient tensor is constructed as `(B_Y ⊗_R P) ⊗_{B_Y} U_Y`.
The canonical balanced identification sends `(b ⊗ p) ⊗ v` to `p ⊗ bv`;
its inverse sends `p ⊗ v` to `(1 ⊗ p) ⊗ v`. Thus this is precisely
`P ⊗_R U_Y`, with its B_Y-action, including its differential.

## Main declarations

* `filteredCoefficientTensorFunctor` and `filteredCoefficientTensorDifferential`:
  the termwise tensor functor and its actual differential.
* `filteredCoefficientTensorComplex_laws`: the shape and square-zero proof obligations.
* `filteredCoefficientTensorComplex`: the resulting cochain complex.
* `filteredCoefficientTensor_constructible_bounds`: finite coefficient devissage.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

variable (Y : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
  (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (ρ : R ⟶ adicLisseConstantRing Y B)
  (P : CochainComplex (pbcModules Y R) ℤ)

/-- Tensoring constant B-modules on the pro-etale site.
Source: Stacks Project, Modules on Sites, Tag 03EK
(blueprint: lem-sf-filtered-coefficient-tensor-bounds). -/
noncomputable def filteredCoefficientTensorFunctor (U : ModuleCat.{u + 1} B) :
    pbcModules Y (adicLisseConstantRing Y B) ⥤ pbcModules Y (adicLisseConstantRing Y B) :=
  SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
    (C := Y.ProEt) (J := ProEt.topology Y)
    (A := adicLisseConstantRing Y B) ((adicLisseConstantModules Y B).obj U)

/-- Differential obtained by extending scalars and tensoring with the constant module.
Source: Stacks Project, Modules on Sites, Tag 03EK
(blueprint: lem-sf-filtered-coefficient-tensor-bounds). -/
noncomputable def filteredCoefficientTensorDifferential
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (ρ : R ⟶ adicLisseConstantRing Y B) (P : CochainComplex (pbcModules Y R) ℤ)
    (U : ModuleCat.{u + 1} B) (i j : ℤ) :
    (filteredCoefficientTensorFunctor Y B U).obj
        (SheafOfModules.changeOfRings.{u, u + 1, u + 1} ρ (P.X i)) ⟶
      (filteredCoefficientTensorFunctor Y B U).obj
        (SheafOfModules.changeOfRings.{u, u + 1, u + 1} ρ (P.X j)) :=
  (filteredCoefficientTensorFunctor Y B U).map
    (SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1} ρ (P.X i) (P.d i j))

/-- Well-definedness of the termwise coefficient tensor differential.
Source: Stacks Project, Modules on Sites, Tag 03EK
(blueprint: lem-sf-filtered-coefficient-tensor-bounds).
Proof: sectionwise change of rings sends d to 1 tensor d, preserves composition
and zero, and sheafification is additive. Tensoring with U_Y again preserves
composition and zero, as can be checked on pure tensors before sheafification.
Consequently the shape and square-zero equations follow from those of P.
These are only the proof fields needed by the displayed tensor construction. -/
theorem filteredCoefficientTensorComplex_laws (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (ρ : R ⟶ adicLisseConstantRing Y B) (P : CochainComplex (pbcModules Y R) ℤ)
    (U : ModuleCat.{u + 1} B) :
    (∀ (i j : ℤ), ¬ (ComplexShape.up ℤ).Rel i j →
      filteredCoefficientTensorDifferential Y B R ρ P U i j = 0) ∧
    (∀ i j k : ℤ,
      filteredCoefficientTensorDifferential Y B R ρ P U i j ≫
        filteredCoefficientTensorDifferential Y B R ρ P U j k = 0) := by
  constructor
  · intro i j hij
    unfold filteredCoefficientTensorDifferential
    rw [SheafOfModules.changeOfRingsComplex_shape ρ P i j hij]
    exact
      (SheafOfModules.siteSheafTensorRight_preservesZeroMorphisms
        ((adicLisseConstantModules Y B).obj U)).map_zero _ _
  · intro i j k
    unfold filteredCoefficientTensorDifferential
    rw [← Functor.map_comp]
    rw [SheafOfModules.changeOfRingsComplex_comp ρ P i j k]
    exact
      (SheafOfModules.siteSheafTensorRight_preservesZeroMorphisms
        ((adicLisseConstantModules Y B).obj U)).map_zero _ _

/-- The actual B_Y-complex P tensor_R U_Y, formed by ordinary sheaf tensors.
Its associative presentation first extends P to B_Y and then tensors with U_Y.
The balanced mutually inverse formulas in the module documentation identify
this with the direct R-tensor, and commute with d_P tensor 1.
Source: Stacks Project, Modules on Sites, Tag 03EK
(blueprint: lem-sf-filtered-coefficient-tensor-bounds). -/
def filteredCoefficientTensorComplex (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (ρ : R ⟶ adicLisseConstantRing Y B) (P : CochainComplex (pbcModules Y R) ℤ)
    (U : ModuleCat.{u + 1} B) :
    CochainComplex (pbcModules Y (adicLisseConstantRing Y B)) ℤ where
  X i := (filteredCoefficientTensorFunctor Y B U).obj
    (SheafOfModules.changeOfRings.{u, u + 1, u + 1} ρ (P.X i))
  d i j := filteredCoefficientTensorDifferential Y B R ρ P U i j
  shape := (filteredCoefficientTensorComplex_laws Y B R ρ P U).1
  d_comp_d' i j k _ _ := by
    exact (filteredCoefficientTensorComplex_laws Y B R ρ P U).2 i j k

private theorem tensorSiteSmall : EssentiallySmall.{u + 1} Y.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

attribute [local instance] tensorSiteSmall
  SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

open MonoidalCategory in
private noncomputable def coefficientTensorFunctor
    (Q : CochainComplex (pbcModules Y (adicLisseConstantRing Y B)) ℤ) :
    ModuleCat.{u + 1} B ⥤ CochainComplex (pbcModules Y (adicLisseConstantRing Y B)) ℤ :=
  let := SheafOfModules.monoidalCategory (adicLisseConstantRing Y B)
  adicLisseConstantModules Y B ⋙
    (((curriedTensor _).mapHomologicalComplex (.up ℤ)).obj Q).asFunctor

private theorem coefficientConstant_exact :
    PreservesFiniteLimits (adicLisseConstantModules Y B) ∧
      PreservesFiniteColimits (adicLisseConstantModules Y B) := by
  let T : ModuleCat.{u + 1} B ⥤
      PresheafOfModules.{u + 1} ((Functor.const Y.ProEtᵒᵖ).obj (RingCat.of B)) :=
    siteConstantModulePresheaf (C := Discrete (ULift.{u + 1} Unit)) B ⋙
      PresheafOfModules.pushforward₀
        ((Functor.const Y.ProEt).obj (Discrete.mk (ULift.up ())))
        ((Functor.const (Discrete (ULift.{u + 1} Unit))ᵒᵖ).obj (RingCat.of B))
  have : PreservesFiniteLimits T := by
    constructor
    intro K _ _
    constructor
    intro F
    constructor
    intro c hc
    exact ⟨PresheafOfModules.evaluationJointlyReflectsLimits _ _ (fun X ↦ hc)⟩
  have : PreservesFiniteColimits T := by
    constructor
    intro K _ _
    constructor
    intro F
    constructor
    intro c hc
    exact ⟨PresheafOfModules.evaluationJointlyReflectsColimits _ _ (fun X ↦ hc)⟩
  exact ⟨comp_preservesFiniteLimits T
    (PresheafOfModules.sheafification (adicLisseConstantUnit Y B)),
    comp_preservesFiniteColimits T
      (PresheafOfModules.sheafification (adicLisseConstantUnit Y B))⟩

open MonoidalCategory in
private theorem coefficientTensorFunctor_preservesZero
    (Q : CochainComplex (pbcModules Y (adicLisseConstantRing Y B)) ℤ) :
    (coefficientTensorFunctor Y B Q).PreservesZeroMorphisms := by
  let := SheafOfModules.monoidalCategory (adicLisseConstantRing Y B)
  have : (adicLisseConstantModules Y B).Additive :=
    (exactFunctor_le_additiveFunctor _ _) _ (coefficientConstant_exact Y B)
  constructor
  intro M N
  apply HomologicalComplex.Hom.ext
  funext i
  change (tensorLeft (Q.X i)).map ((adicLisseConstantModules Y B).map 0) = 0
  rw [Functor.map_zero, Functor.map_zero]

open MonoidalCategory in
private noncomputable def coefficientTensorIso (U : ModuleCat.{u + 1} B) :
    filteredCoefficientTensorComplex Y B R ρ P U ≅
      (coefficientTensorFunctor Y B (SheafOfModules.changeOfRingsComplex.{u + 1, u}
        (C := Y.ProEt) (J := ProEt.topology Y) ρ P)).obj U := by
  let := SheafOfModules.monoidalCategory (adicLisseConstantRing Y B)
  have := SheafOfModules.siteSheafTensorRight_preservesZeroMorphisms
    ((adicLisseConstantModules Y B).obj U)
  exact (NatIso.mapHomologicalComplex
    (SheafOfModules.siteSheafTensorRightIso (adicLisseConstantRing Y B)
      ((adicLisseConstantModules Y B).obj U)) (.up ℤ)).app
        (SheafOfModules.changeOfRingsComplex.{u + 1, u}
        (C := Y.ProEt) (J := ProEt.topology Y) ρ P)

open MonoidalCategory in
private theorem coefficientTensor_flat
    (hP : ∀ q : ℤ, SheafOfModules.IsFlatOnSite
      (C := Y.ProEt) (J := ProEt.topology Y) (R := R) (P.X q))
    (q : ℤ) :
    let := SheafOfModules.monoidalCategory (adicLisseConstantRing Y B)
    exactFunctor _ _ (tensorLeft ((SheafOfModules.changeOfRingsComplex.{u + 1, u}
        (C := Y.ProEt) (J := ProEt.topology Y) ρ P).X q)) := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory (adicLisseConstantRing Y B)
  let := SheafOfModules.symmetricCategory (adicLisseConstantRing Y B)
  let A := (adicLisseForget Y).obj R
  let D := (adicLisseForget Y).obj (adicLisseConstantRing Y B)
  let U := SheafOfModules.restrictScalars ((adicLisseForget Y).map ρ)
  have : PreservesFiniteLimits (U ⋙ SheafOfModules.toSheaf A) :=
    inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf D))
  have : PreservesFiniteColimits (U ⋙ SheafOfModules.toSheaf A) :=
    inferInstanceAs (PreservesFiniteColimits (SheafOfModules.toSheaf D))
  have : PreservesFiniteLimits U :=
    preservesFiniteLimits_of_reflects_of_preserves U (SheafOfModules.toSheaf A)
  have : PreservesFiniteColimits U :=
    preservesFiniteColimits_of_reflects_of_preserves U (SheafOfModules.toSheaf A)
  have : U.ReflectsIsomorphisms := by
    have : (U ⋙ SheafOfModules.toSheaf A).ReflectsIsomorphisms :=
      inferInstanceAs (SheafOfModules.toSheaf D).ReflectsIsomorphisms
    exact reflectsIsomorphisms_of_comp U (SheafOfModules.toSheaf A)
  let T := tensorRight (P.X q)
  have hT : exactFunctor _ _ T :=
    (exactFunctor _ _).prop_of_iso (SheafOfModules.siteSheafTensorRightIso R (P.X q))
      (hP q)
  have : PreservesFiniteLimits T := hT.1
  have : PreservesFiniteColimits T := hT.2
  let S := tensorRight ((SheafOfModules.changeOfRingsComplex.{u + 1, u}
        (C := Y.ProEt) (J := ProEt.topology Y) ρ P).X q)
  obtain ⟨e, he⟩ := SheafOfModules.exists_changeOfRings_tensorCancellation ρ
  have hid : SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1}
        (C := Y.ProEt) (J := ProEt.topology Y) ρ (P.X q) (𝟙 (P.X q)) = 𝟙 _ := by
    let a := PresheafOfModules.sheafification
      (𝟙 ((adicLisseForget Y).obj (adicLisseConstantRing Y B)).obj)
    let t : SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
        (C := Y.ProEt) (J := ProEt.topology Y) ρ (P.X q) ⟶
        SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
        (C := Y.ProEt) (J := ProEt.topology Y) ρ (P.X q) :=
      { app := fun Z ↦ (ModuleCat.extendScalars (ρ.hom.app Z).hom).map
          (𝟙 ((P.X q).val.obj Z))
        naturality := SheafOfModules.changeOfRingsHom_naturality.{u, u + 1, u + 1}
          (C := Y.ProEt) (J := ProEt.topology Y) ρ (P.X q) (𝟙 _) }
    have ht : t = 𝟙 _ := by
      apply PresheafOfModules.hom_ext
      intro Z
      exact (ModuleCat.extendScalars (ρ.hom.app Z).hom).map_id ((P.X q).val.obj Z)
    change a.map t = 𝟙 _
    rw [ht]
    exact a.map_id _
  let e' : S ⋙ U ≅ U ⋙ T := NatIso.ofComponents (fun M ↦ e M (P.X q)) (by
    intro M N f
    change U.map (whiskerRight f (SheafOfModules.changeOfRings.{u, u + 1, u + 1}
        (C := Y.ProEt) (J := ProEt.topology Y) ρ (P.X q))) ≫
      (e N (P.X q)).hom = (e M (P.X q)).hom ≫ whiskerRight (U.map f) (P.X q)
    simpa only [hid, tensorHom_id] using he f (𝟙 (P.X q)))
  have : PreservesFiniteLimits (U ⋙ T) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (U ⋙ T) := comp_preservesFiniteColimits _ _
  have : PreservesFiniteLimits (S ⋙ U) := preservesFiniteLimits_of_natIso e'.symm
  have : PreservesFiniteColimits (S ⋙ U) := preservesFiniteColimits_of_natIso e'.symm
  have : PreservesFiniteLimits S :=
    preservesFiniteLimits_of_reflects_of_preserves S U
  have : PreservesFiniteColimits S :=
    preservesFiniteColimits_of_reflects_of_preserves S U
  exact (exactFunctor _ _).prop_of_iso
    (BraidedCategory.tensorLeftIsoTensorRight _).symm
      ((exactFunctor_iff S).2 ⟨inferInstance, inferInstance⟩)

open MonoidalCategory in
private theorem coefficientTensor_shortExact
    (hP : ∀ q : ℤ, SheafOfModules.IsFlatOnSite
      (C := Y.ProEt) (J := ProEt.topology Y) (R := R) (P.X q))
    (S : ShortComplex (ModuleCat.{u + 1} B)) (hS : S.ShortExact) :
    let := coefficientTensorFunctor_preservesZero Y B
      (SheafOfModules.changeOfRingsComplex.{u + 1, u}
        (C := Y.ProEt) (J := ProEt.topology Y) ρ P)
    (S.map (coefficientTensorFunctor Y B
      (SheafOfModules.changeOfRingsComplex.{u + 1, u}
        (C := Y.ProEt) (J := ProEt.topology Y) ρ P))).ShortExact := by
  let := SheafOfModules.monoidalCategory (adicLisseConstantRing Y B)
  have := coefficientTensorFunctor_preservesZero Y B
    (SheafOfModules.changeOfRingsComplex.{u + 1, u}
        (C := Y.ProEt) (J := ProEt.topology Y) ρ P)
  have : (adicLisseConstantModules Y B).Additive :=
    (exactFunctor_le_additiveFunctor _ _) _ (coefficientConstant_exact Y B)
  have : PreservesFiniteLimits (adicLisseConstantModules Y B) :=
    (coefficientConstant_exact Y B).1
  have : PreservesFiniteColimits (adicLisseConstantModules Y B) :=
    (coefficientConstant_exact Y B).2
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  have hflat := coefficientTensor_flat Y B R ρ P hP i
  have : PreservesFiniteLimits
      (tensorLeft ((SheafOfModules.changeOfRingsComplex.{u + 1, u}
        (C := Y.ProEt) (J := ProEt.topology Y) ρ P).X i)) := hflat.1
  have : PreservesFiniteColimits
      (tensorLeft ((SheafOfModules.changeOfRingsComplex.{u + 1, u}
        (C := Y.ProEt) (J := ProEt.topology Y) ρ P).X i)) := hflat.2
  exact (hS.map_of_exact (adicLisseConstantModules Y B)).map_of_exact
    (tensorLeft ((SheafOfModules.changeOfRingsComplex.{u + 1, u}
        (C := Y.ProEt) (J := ProEt.topology Y) ρ P).X i))

private theorem coefficientConstructible_iso [Finite B]
    {M N : pbcModules Y (adicLisseConstantRing Y B)} (e : M ≅ N)
    (h : IsConstructibleProEtaleCoefficientModuleSheaf Y B M) :
    IsConstructibleProEtaleCoefficientModuleSheaf Y B N := by
  obtain ⟨S, hn, hc, h⟩ := h
  refine ⟨S, hn, hc, fun i ↦ ?_⟩
  obtain ⟨V, hV, htriv⟩ := h i
  refine ⟨V, hV, fun U f hf ↦ ?_⟩
  obtain ⟨M, hM, ⟨eM⟩⟩ := htriv U f hf
  refine ⟨M, hM, ⟨?_⟩⟩
  exact (SheafOfModules.overFunctor _ U).mapIso
    ((proEtaleModuleInverseImage (S.immersion i) (adicLisseConstantRing Y B)).mapIso
      e.symm) ≪≫ eM

private def coefficientGood [Finite B]
    (K : CochainComplex (pbcModules Y (adicLisseConstantRing Y B)) ℤ) (r s : ℤ) : Prop :=
  ∀ n : ℤ, IsConstructibleProEtaleCoefficientModuleSheaf Y B (K.homology n) ∧
    ((n < r ∨ s < n) → IsZero (K.homology n))

private theorem coefficientGood_iso [Finite B]
    {K L : CochainComplex (pbcModules Y (adicLisseConstantRing Y B)) ℤ}
    (e : K ≅ L) {r s : ℤ} (h : coefficientGood Y B K r s) :
    coefficientGood Y B L r s := by
  intro n
  let e' := (HomologicalComplex.homologyFunctor _ (.up ℤ) n).mapIso e
  exact ⟨coefficientConstructible_iso Y B e' (h n).1,
    fun hn ↦ (h n).2 hn |>.of_iso e'.symm⟩

private theorem coefficientGood_isZero [Finite B]
    (K : CochainComplex (pbcModules Y (adicLisseConstantRing Y B)) ℤ)
    (hK : IsZero K) (r s : ℤ) : coefficientGood Y B K r s := by
  let C := pbcModules Y (adicLisseConstantRing Y B)
  let T := DerivedCategory.homologyProperty
    (IsConstructibleProEtaleCoefficientModuleSheaf Y B)
  have : T.IsClosedUnderIsomorphisms := (constructibleCoefficientHomology_isTriangulated Y B).1
  have : T.IsTriangulated := (constructibleCoefficientHomology_isTriangulated Y B).2
  have h : T (DerivedCategory.Q.obj K) :=
    T.prop_of_isZero (DerivedCategory.Q.map_isZero hK)
  intro n
  exact ⟨coefficientConstructible_iso Y B
      ((DerivedCategory.homologyFunctorFactors C n).app K) (h n),
    fun _ ↦ (HomologicalComplex.homologyFunctor _ (.up ℤ) n).map_isZero hK⟩

private theorem coefficientGood_extension [Finite B]
    (S : ShortComplex (CochainComplex (pbcModules Y (adicLisseConstantRing Y B)) ℤ))
    (hS : S.ShortExact) {r s : ℤ}
    (h₁ : coefficientGood Y B S.X₁ r s) (h₃ : coefficientGood Y B S.X₃ r s) :
    coefficientGood Y B S.X₂ r s := by
  let C := pbcModules Y (adicLisseConstantRing Y B)
  let T := DerivedCategory.homologyProperty
    (IsConstructibleProEtaleCoefficientModuleSheaf Y B)
  have : T.IsClosedUnderIsomorphisms := (constructibleCoefficientHomology_isTriangulated Y B).1
  have : T.IsTriangulated := (constructibleCoefficientHomology_isTriangulated Y B).2
  have h : T (DerivedCategory.Q.obj S.X₂) :=
    T.ext_of_isTriangulatedClosed₂ (DerivedCategory.triangleOfSES hS)
      (DerivedCategory.triangleOfSES_distinguished hS)
      (fun n ↦ coefficientConstructible_iso Y B
        ((DerivedCategory.homologyFunctorFactors C n).app S.X₁).symm (h₁ n).1)
      (fun n ↦ coefficientConstructible_iso Y B
        ((DerivedCategory.homologyFunctorFactors C n).app S.X₃).symm (h₃ n).1)
  intro n
  refine ⟨coefficientConstructible_iso Y B
    ((DerivedCategory.homologyFunctorFactors C n).app S.X₂) (h n), ?_⟩
  intro hn
  exact (hS.homology_exact₂ n).isZero_X₂
    (((h₁ n).2 hn).eq_of_src _ _) (((h₃ n).2 hn).eq_of_tgt _ _)

/-- Finite coefficient devissage keeps exactly the common cohomological interval.
Source: Stacks Project, proetale.tex, Tag 09B5; finite-filtration application
(blueprint: lem-sf-filtered-coefficient-tensor-bounds).

Proof:
1. For j<t, take the quotient sequence 0→V_(j+1)→V_j→W_j→0.
Constant presheaves are sectionwise exact; exact module sheafification
(lem-weil-pbc-site-r-module-presheaf-sheafification-exact) gives the constant
B_Y-module sequence. Restriction through rho retains its underlying additive
sheaves and exactness (def-pc-sheaf-restrict-scalars).
2. Flatness of each P^q gives a short exact sequence after tensoring with P^q
(def-pc-flat-sheaf-modules). The maps commute with d_P tensor 1 and are B_Y-linear,
as verified on pure tensors (def-pur-sheaf-tensor-product). Thus the sequence
of coefficient complexes is degreewise short exact in Mod(B_Y).
3. Descend from j=t. The zero coefficient gives the zero complex and zero
cohomology, constructible using a single stratum, even for the empty scheme.
This also handles t=0. At each step use the assertion for V_(j+1) and the
assumed assertion for W_j.
4. The long exact cohomology sequence
(lem-weil-pbc-complex-ses-homology-long-exact) gives exactness of the same-degree
segment. Outside [r,s] both outer cohomology sheaves vanish, hence the middle
one vanishes. Neither endpoint moves.
5. The short exact complex sequence gives a distinguished triangle
(lem-weil-pbc-complex-ses-triangle). Derived cohomology agrees with cohomology
of these representatives (def-weil-derived-cohomology-sheaves and
 def-weil-abstract-derived-category). The middle-vertex clause of
lem-weil-proetale-dbc-triangulated preserves constructibility and boundedness
for the finite ring B on arbitrary Y. Descending induction proves every V_j;
V_0=V proves the final assertion. The interval is independent of t. -/
theorem filteredCoefficientTensor_constructible_bounds [Finite B]
    (hP : ∀ q : ℤ, SheafOfModules.IsFlatOnSite (C := Y.ProEt)
      (J := ProEt.topology Y) (R := R)
      (P.X q : SheafOfModules.{u + 1}
        ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)))
    (V : Type (u + 1)) [AddCommGroup V] [Module B V] [Finite V]
    (t : ℕ) (F : Fin (t + 1) → Submodule B V) (hF : Antitone F)
    (hF₀ : F 0 = ⊤) (hFt : F (Fin.last t) = ⊥)
    (r s : ℤ) (hrs : r ≤ s)
    (hW : ∀ (j : Fin t) (n : ℤ),
      IsConstructibleProEtaleCoefficientModuleSheaf Y B
        ((filteredCoefficientTensorComplex Y B R ρ P
          (ModuleCat.of B ((F j.castSucc) ⧸
            (F j.succ).comap (F j.castSucc).subtype))).homology n) ∧
      ((n < r ∨ s < n) → IsZero
        ((filteredCoefficientTensorComplex Y B R ρ P
          (ModuleCat.of B ((F j.castSucc) ⧸
            (F j.succ).comap (F j.castSucc).subtype))).homology n))) :
    (∀ (j : Fin (t + 1)) (n : ℤ),
      IsConstructibleProEtaleCoefficientModuleSheaf Y B
        ((filteredCoefficientTensorComplex Y B R ρ P (ModuleCat.of B (F j))).homology n) ∧
      ((n < r ∨ s < n) → IsZero
        ((filteredCoefficientTensorComplex Y B R ρ P (ModuleCat.of B (F j))).homology n))) ∧
    (∀ n : ℤ,
      IsConstructibleProEtaleCoefficientModuleSheaf Y B
        ((filteredCoefficientTensorComplex Y B R ρ P (ModuleCat.of B V)).homology n) ∧
      ((n < r ∨ s < n) → IsZero
        ((filteredCoefficientTensorComplex Y B R ρ P (ModuleCat.of B V)).homology n))) := by
  have _hrs := hrs
  let Q := SheafOfModules.changeOfRingsComplex.{u + 1, u}
        (C := Y.ProEt) (J := ProEt.topology Y) ρ P
  let G := coefficientTensorFunctor Y B Q
  have : G.PreservesZeroMorphisms := coefficientTensorFunctor_preservesZero Y B Q
  have hlayer (j : Fin t) : coefficientGood Y B
      (G.obj (ModuleCat.of B ((F j.castSucc) ⧸
        (F j.succ).comap (F j.castSucc).subtype))) r s :=
    coefficientGood_iso Y B (coefficientTensorIso Y B R ρ P _) (hW j)
  have hstage (j : Fin (t + 1)) :
      coefficientGood Y B (G.obj (ModuleCat.of B (F j))) r s := by
    induction j using Fin.reverseInduction with
    | last =>
      have hz : IsZero (ModuleCat.of B (F (Fin.last t))) := by
        rw [hFt]
        exact ModuleCat.isZero_of_subsingleton _
      exact coefficientGood_isZero Y B _ (G.map_isZero hz) r s
    | cast j ih =>
      have hsub : F j.succ ≤ F j.castSucc := hF (Fin.castSucc_le_succ j)
      let f : F j.succ →ₗ[B] F j.castSucc := Submodule.inclusion hsub
      let K := (F j.succ).comap (F j.castSucc).subtype
      have hex : Function.Exact f K.mkQ := by
        apply LinearMap.exact_iff.mpr
        rw [Submodule.ker_mkQ]
        ext x
        change (x : V) ∈ F j.succ ↔ ∃ y : F j.succ, f y = x
        constructor
        · intro hx
          exact ⟨⟨x, hx⟩, rfl⟩
        · rintro ⟨y, rfl⟩
          exact y.property
      let S := ModuleCat.shortComplexOfCompEqZero f K.mkQ hex.linearMap_comp_eq_zero
      have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S hex
        (Submodule.inclusion_injective hsub) K.mkQ_surjective
      exact coefficientGood_extension Y B (S.map G)
        (coefficientTensor_shortExact Y B R ρ P hP S hS) ih (hlayer j)
  refine ⟨fun j ↦ coefficientGood_iso Y B
    (coefficientTensorIso Y B R ρ P _).symm (hstage j), ?_⟩
  let e : ModuleCat.of B (F 0) ≅ ModuleCat.of B V :=
    (LinearEquiv.ofEq (F 0) ⊤ hF₀ ≪≫ₗ Submodule.topEquiv).toModuleIso
  exact coefficientGood_iso Y B (coefficientTensorIso Y B R ρ P _).symm
    (coefficientGood_iso Y B (G.mapIso e) (hstage 0))

end AlgebraicGeometry.Scheme
