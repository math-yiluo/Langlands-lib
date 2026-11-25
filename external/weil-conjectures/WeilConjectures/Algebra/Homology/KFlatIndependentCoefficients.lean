/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall

/-! # K-flat complexes with an independent coefficient universe

The tensor product is the same sheafified tensor product as in `KFlat`. Relative
essential smallness permits the coefficient universe to differ from both site universes.
-/

@[expose] public section

universe u v w

open CategoryTheory MonoidalCategory Limits

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{w})

/-- Tensor localization is monoidal after transporting the site to its small model in
the coefficient universe. Source: Stacks Project, Modules on Sites, Section 03EK.

Proof: transport the topology, ring sheaf, and module presheaves along the equivalence
with the small model in universe `w`. There the sectionwise tensor/internal-Hom
adjunction shows that tensoring a locally bijective map induces bijections into every
module sheaf. The sheafification adjunction makes its tensor an isomorphism. Symmetry
handles the other variable, and transport preserves these properties. -/
theorem isMonoidal_W_independentCoefficients :
    (J.W.inverseImage (PresheafOfModules.toPresheaf.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R).obj)).IsMonoidal := by
  let e := equivSmallModel.{w} C
  let K := e.inverse.inducedTopology J
  have : ∀ X : Cᵒᵖ,
      HasLimitsOfShape (StructuredArrow X e.inverse.op) AddCommGrpCat.{w} :=
    fun _ ↦ hasLimitsOfShape_of_essentiallySmall.{w} _ _
  let S := (e.inverse.sheafPushforwardContinuous CommRingCat.{w} K J).obj R
  let T := PresheafOfModules.pushforward₀OfCommRingCat.{w} e.inverse R.obj
  let W := J.W.inverseImage (PresheafOfModules.toPresheaf.{w}
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R).obj)
  let V := K.W.inverseImage (PresheafOfModules.toPresheaf.{w}
    ((sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).obj S).obj)
  have hw {P Q : PresheafOfModules.{w} (R.obj ⋙ forget₂ _ _)} (f : P ⟶ Q) :
      W f ↔ V (T.map f) := by
    change J.W _ ↔ K.W _
    rw [← J.W_inverseImage_whiskeringLeft K e.inverse]
    rfl
  have hleft (F : PresheafOfModules.{w} (R.obj ⋙ forget₂ _ _))
      {P Q : PresheafOfModules.{w} (R.obj ⋙ forget₂ _ _)} {f : P ⟶ Q}
      (hf : W f) : W (F ◁ f) := by
    apply (hw _).2
    exact V.whiskerLeft_mem (T.obj F) (T.map f) ((hw f).1 hf)
  refine ⟨?_, ?_⟩
  · intro F P Q f hf
    exact hleft F hf
  · intro P Q f hf G
    exact (W.arrow_mk_iso_iff (Arrow.isoMk (β_ P G) (β_ Q G))).2 (hleft G hf)

/-- Tensoring a zero morphism on the left is zero for module sheaves over a relatively
small site. Source: Stacks Project, Cohomology on Sites, Tag 06YN.

Proof: the zero module sheaf has zero underlying presheaf. Sectionwise tensoring it
with any module presheaf gives zero; sheafification preserves the zero object as a
left adjoint between additive categories. Factor a zero morphism through the zero
sheaf and tensor both factors. -/
theorem preservesZeroMorphisms_curriedTensor_independentCoefficients :
    letI := isMonoidal_W_independentCoefficients R
    letI := monoidalCategory R
    (curriedTensor (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R))).PreservesZeroMorphisms := by
  let 𝓡 := (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R
  let := isMonoidal_W_independentCoefficients R
  let := monoidalCategory R
  let := HasZeroObject.zero' (SheafOfModules.{w} 𝓡)
  let a := PresheafOfModules.sheafification.{w} (𝟙 𝓡.obj)
  let i := SheafOfModules.forget 𝓡
  have hzero (M : SheafOfModules.{w} 𝓡) :
      IsZero ((0 : SheafOfModules.{w} 𝓡) ⊗ M) := by
    have hp : IsZero ((0 : SheafOfModules.{w} 𝓡).val) := by
      exact Functor.map_isZero i (isZero_zero _)
    have : (tensorRight M.val).PreservesZeroMorphisms := by
      refine ⟨fun P Q ↦ ?_⟩
      change (0 : P ⟶ Q) ▷ M.val = 0
      ext U : 1
      change whiskerRight (C := ModuleCat (R.obj.obj U)) ((0 : P ⟶ Q).app U)
        (M.val.obj U) = 0
      simp
    have ht : IsZero ((0 : SheafOfModules.{w} 𝓡).val ⊗ M.val) := by
      exact Functor.map_isZero (tensorRight M.val) hp
    exact (Functor.map_isZero a ht).of_iso (tensorObjIsoSheafification (R := R)
      (0 : SheafOfModules.{w} 𝓡) M)
  refine ⟨fun X Y ↦ ?_⟩
  apply NatTrans.ext
  funext M
  change (0 : X ⟶ Y) ▷ M = 0
  have hz := hzero M
  have h : (0 : X ⟶ Y) =
      (0 : X ⟶ (0 : SheafOfModules.{w} 𝓡)) ≫
        (0 : (0 : SheafOfModules.{w} 𝓡) ⟶ Y) := by simp
  rw [h, comp_whiskerRight,
    hz.eq_of_src ((0 : (0 : SheafOfModules.{w} 𝓡) ⟶ Y) ▷ M) 0,
    comp_zero]

/-- Tensoring a zero morphism on the right is zero, by symmetry of the tensor product.
Source: Stacks Project, Cohomology on Sites, Tag 06YN.

Proof: conjugate the left-variable statement by the symmetry isomorphism of the
sheafified tensor product. Naturality of that isomorphism carries `0 ▷ M` to
`M ◁ 0`, and conjugation preserves zero morphisms. -/
theorem preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
    (M : SheafOfModules.{w} ((sheafCompose J
      (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) :
    letI := isMonoidal_W_independentCoefficients R
    letI := monoidalCategory R
    let T := curriedTensor (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R))
    (T.obj M).PreservesZeroMorphisms := by
  let := isMonoidal_W_independentCoefficients R
  let := monoidalCategory R
  let := symmetricCategory R
  let := preservesZeroMorphisms_curriedTensor_independentCoefficients R
  refine ⟨fun X Y ↦ ?_⟩
  change M ◁ (0 : X ⟶ Y) = 0
  have h : (0 : X ⟶ Y) ▷ M = 0 :=
    congrArg (fun t ↦ t.app M) ((curriedTensor _).map_zero X Y)
  apply (cancel_mono (β_ M Y).hom).1
  rw [BraidedCategory.braiding_naturality_right, h, comp_zero, zero_comp]

end SheafOfModules

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{w}}

set_option synthInstance.maxSize 256 in
/-- K-flatness against every acyclic complex, using the sheafified total tensor complex
at an independent coefficient universe. Source: Stacks Project, Tag 06YN. -/
def IsKFlatIndependentCoefficients
    (K : CochainComplex (SheafOfModules.{w} ((sheafCompose J
      (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ) : Prop :=
  letI := SheafOfModules.isMonoidal_W_independentCoefficients R
  letI := SheafOfModules.monoidalCategory R
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  ∀ F : CochainComplex (SheafOfModules.{w} ((sheafCompose J
      (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ,
    F.Acyclic → (mapBifunctor F K (curriedTensor _)).Acyclic

/-- A quasi-isomorphism from a K-flat complex, with independent coefficient and site
universes. Source: Stacks Project, Tag 06YS. -/
def IsKFlatResolutionIndependentCoefficients
    {K G : CochainComplex (SheafOfModules.{w} ((sheafCompose J
      (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ}
    (f : K ⟶ G) : Prop :=
  QuasiIso f ∧ K.IsKFlatIndependentCoefficients

/-- In the coefficient universe `max u v`, the independent predicate is
`CochainComplex.IsKFlatTensor`.
Source: Stacks Project, Cohomology on Sites, Tag 06YN.

Proof: unfold both predicates. The underlying module categories and tensor functors
are definitionally the same at `w = max u v`. The two local witnesses for monoidality
and preservation of zero morphisms are proofs of propositions, so proof irrelevance
identifies the resulting total tensor complexes. Both predicates quantify over the
same acyclic complexes. -/
theorem isKFlatIndependentCoefficients_iff_isKFlat
    {C : Type u} [Category.{v} C] [EssentiallySmall.{max u v} C]
    {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{max u v}}
    (K : CochainComplex (SheafOfModules.{max u v} ((sheafCompose J
      (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ) :
    IsKFlatIndependentCoefficients K ↔ IsKFlatTensor K := by
  rfl

/-- The independent resolution predicate specializes to `CochainComplex.IsKFlatTensorResolution`
when the coefficient universe is the maximum of the site universes.
Source: Stacks Project, Cohomology on Sites, Tag 06YS.

Proof: unfold both resolution predicates. Their quasi-isomorphism conjuncts are
identical, and the K-flat conjuncts agree by
`isKFlatIndependentCoefficients_iff_isKFlat`. -/
theorem isKFlatResolutionIndependentCoefficients_iff_isKFlatResolution
    {C : Type u} [Category.{v} C] [EssentiallySmall.{max u v} C]
    {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{max u v}}
    {K G : CochainComplex (SheafOfModules.{max u v} ((sheafCompose J
      (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ}
    (f : K ⟶ G) :
    IsKFlatResolutionIndependentCoefficients f ↔ IsKFlatTensorResolution f := by
  rfl


end CochainComplex
