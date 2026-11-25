/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # TensorColimitsIndependentCoefficients

Source: Stacks Project, Tag 03EP (lemma-tensor-commute-colimits), item (2).
(auxiliary; not a blueprint node). -/

@[expose] public section

universe u v w
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits MonoidalCategory
namespace SheafOfModules
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{w})

set_option backward.isDefEq.respectTransparency false in
/-- Tensoring on the left preserves coefficient-sized colimits of module sheaves.
Source: Stacks Project, Modules on Sites, Tag 03EP, lemma-tensor-commute-colimits,
item (2), with tensor product constructed by sheafification
(auxiliary; not a blueprint node).

Proof: write a for module sheafification. Its counit is an isomorphism on a sheaf M.
The monoidal comparison of a identifies a followed by tensorLeft M with presheaf
sectionwise tensorLeft M.val followed by a. The presheaf tensor functor preserves
colimits sectionwise, and a preserves colimits as a left adjoint. A functor out of
a reflective category preserves colimits if its precomposition with the reflector
does, by Adjunction.preservesColimitsOfSize_iff. Apply this to the sheafification
adjunction, whose right adjoint is fully faithful. -/
theorem tensorLeft_preservesColimits_independentCoefficients
    (M : SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) :
    letI := isMonoidal_W_independentCoefficients R
    letI := monoidalCategory R
    PreservesColimitsOfSize.{w, w} (tensorLeft M) := by
  let := isMonoidal_W_independentCoefficients R
  let := monoidalCategory R
  let O := (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R
  let := siteTensor_identity_locallyInjective O
  let := siteTensor_identity_locallySurjective O
  let a := PresheafOfModules.sheafification (𝟙 O.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 O.obj)
  let eM := (asIso adj.counit).app M
  let e : a ⋙ tensorLeft M ≅ tensorLeft M.val ⋙ a :=
    isoWhiskerLeft a ((curriedTensor _).mapIso eM.symm) ≪≫
      Functor.Monoidal.commTensorLeft a M.val
  have : PreservesColimitsOfSize.{w, w} (tensorLeft M.val) := by
    change PreservesColimitsOfSize.{w, w} (tensorLeft
      (show PresheafOfModules.{w} (R.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w}) from M.val))
    infer_instance
  have : PreservesColimitsOfSize.{w, w} a := adj.leftAdjoint_preservesColimits
  have : PreservesColimitsOfSize.{w, w} (a ⋙ tensorLeft M) :=
    preservesColimits_of_natIso e.symm
  exact (adj.preservesColimitsOfSize_iff (tensorLeft M)).mpr inferInstance

set_option backward.isDefEq.respectTransparency false in
/-- Tensoring module sheaves is additive at independent coefficient universes.
Source: Stacks Project, Modules on Sites, Tag 03EP, item (2).
(auxiliary; not a blueprint node).

Proof: tensor preserves coefficient-sized colimits and zero morphisms. Shrink its
colimit preservation to finite diagrams, so it preserves binary coproducts and hence
binary biproducts. A zero-preserving functor preserving binary biproducts is additive. -/
theorem tensorLeft_additive_independent
    (M : SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) :
    letI := isMonoidal_W_independentCoefficients R
    letI := monoidalCategory R
    (tensorLeft M).Additive := by
  let := isMonoidal_W_independentCoefficients R
  let := monoidalCategory R
  let := preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  have := tensorLeft_preservesColimits_independentCoefficients R M
  have : PreservesColimitsOfSize.{0, 0} (tensorLeft M) :=
    preservesColimitsOfSize_shrink (tensorLeft M)
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (tensorLeft M)
  exact Functor.additive_of_preservesBinaryBiproducts _

set_option backward.isDefEq.respectTransparency false in
/-- The explicit sectionwise tensor functor agrees with the presheaf monoidal tensor.
Source: Stacks Project, Tag 03EK (auxiliary; not a blueprint node).
The identity on each section commutes with restrictions and tensor maps. -/
noncomputable def siteTensorRightIso
    (M : PresheafOfModules.{w}
      (((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R).obj)) :
    siteTensorRight M ≅ tensorRight M := by
  refine NatIso.ofComponents (fun N ↦ ?_) ?_
  · refine PresheafOfModules.isoMk (fun U ↦ Iso.refl _) ?_
    intro U V f
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro x y
    rfl
  · intro N N' f
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro x y
    rfl
set_option backward.isDefEq.respectTransparency false in
/-- The monoidal sheaf tensor is sheafification of the tensor of underlying presheaves.
Source: Stacks Project, Tag 03EK (auxiliary; not a blueprint node).
Apply the monoidal sheafification comparison and its invertible counit on sheaves. -/
noncomputable def tensorRightPresentation
    (M : SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) :
    let := isMonoidal_W_independentCoefficients R
    let := monoidalCategory R
    tensorRight M ≅ forget _ ⋙ tensorRight M.val ⋙
      PresheafOfModules.sheafification (𝟙 _ ) := by
  let := isMonoidal_W_independentCoefficients R
  let := monoidalCategory R
  let a := PresheafOfModules.sheafification (𝟙
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R).obj)
  let i := SheafOfModules.forget.{w} ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)
  let e : i ⋙ a ≅ 𝟭 _ := NatIso.ofComponents
    (fun N ↦ (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 _)).counit).app N)
    (by intro N N' f; exact
      (PresheafOfModules.sheafificationAdjunction (𝟙 _)).counit.naturality f)
  exact (curriedTensor _).flip.mapIso (e.app M).symm ≪≫
    isoWhiskerRight e.symm (tensorRight (a.obj M.val)) ≪≫
    isoWhiskerLeft i (Functor.Monoidal.commTensorRight a M.val)

set_option backward.isDefEq.respectTransparency false in
/-- The explicit site tensor functor agrees with the monoidal tensor of module sheaves.
Source: Stacks Project, Tag 03EK (auxiliary; not a blueprint node).
Sheafify the sectionwise comparison and compose with the monoidal presentation. -/
noncomputable def siteSheafTensorRightIso
    (M : SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) :
    letI := isMonoidal_W_independentCoefficients R
    letI := monoidalCategory R
    siteSheafTensorRight (A := R) M ≅ tensorRight M := by
  let := isMonoidal_W_independentCoefficients R
  let := monoidalCategory R
  let := siteTensor_identity_locallyInjective
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)
  let := siteTensor_identity_locallySurjective
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)
  exact isoWhiskerLeft (forget _) (isoWhiskerRight (siteTensorRightIso R M.val)
    (PresheafOfModules.sheafification (J := J) (𝟙
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R).obj))) ≪≫
      (tensorRightPresentation R M).symm

end SheafOfModules
