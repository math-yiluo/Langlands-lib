/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.PrincipalKoszulQuotientTowers
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! # K-flat tensor transport at independent coefficient universes

Source: Stacks Project, Cohomology on Sites, Tags 06YN and 06YP
(auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false

universe uC vC r

open CategoryTheory MonoidalCategory Limits

namespace CategoryTheory

-- Prove the tensorator calculation abstractly so its rewrites do not unfold sheafification.
private theorem tensorRight_comparison_naturality
    {A B : Type*} [Category A] [Category B] [MonoidalCategory A] [MonoidalCategory B]
    (F : A ⥤ B) [F.LaxMonoidal] {M M' N : B} {X X' Y : A}
    (f : M ⟶ M') (g : X ⟶ X')
    (a : M ⟶ F.obj X) (a' : M' ⟶ F.obj X') (b : N ⟶ F.obj Y)
    (h : f ≫ a' = a ≫ F.map g) :
    f ▷ N ≫ ((a' ⊗ₘ b) ≫ Functor.LaxMonoidal.μ F X' Y) =
      (a ⊗ₘ b) ≫ Functor.LaxMonoidal.μ F X Y ≫ F.map (g ▷ Y) := by
  rw [← Functor.LaxMonoidal.μ_natural_left, ← Category.assoc, ← Category.assoc,
    whiskerRight_comp_tensorHom, tensorHom_comp_whiskerRight, h]

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C]
variable {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})

set_option hygiene false in
local notation "𝓞" => (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R
set_option hygiene false in
local notation "𝒜" => ringedSiteModules.{r} 𝓞

attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
attribute [local instance] SheafOfModules.monoidalCategory
attribute [local instance]
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
attribute [local instance]
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

set_option backward.isDefEq.respectTransparency false in
-- Tensor comparison naturality unfolds the sheafification localization interface.
private theorem tensorRight_additive_reconstruction (N : 𝒜) :
    (MonoidalCategory.tensorRight N).Additive := by
  let S := PresheafOfModules.sheafification.{r} (𝟙 (𝓞).obj)
  have : S.Additive := by
    have := preservesBinaryBiproducts_of_preservesBinaryCoproducts S
    exact Functor.additive_of_preservesBinaryBiproducts S
  have : (MonoidalCategory.tensorRight N.val).Additive := by
    refine ⟨?_⟩
    intro M M' f g
    ext U : 1
    let : CommRing ((𝓞).obj.obj U) := inferInstanceAs (CommRing (R.obj.obj U))
    change (f.app U + g.app U) ▷ N.val.obj U =
      f.app U ▷ N.val.obj U + g.app U ▷ N.val.obj U
    simp
  have hn {M M' : 𝒜} (f : M ⟶ M') :
      f ▷ N ≫ (SheafOfModules.tensorObjIsoSheafification (R := R) M' N).hom =
        (SheafOfModules.tensorObjIsoSheafification (R := R) M N).hom ≫
          S.map (f.val ▷ N.val) := by
    let c := asIso (PresheafOfModules.sheafificationAdjunction.{r}
      (𝟙 (𝓞).obj)).counit
    have h : f ≫ c.inv.app M' = c.inv.app M ≫ S.map f.val := by
      exact c.inv.naturality f
    exact tensorRight_comparison_naturality S f f.val
      (c.inv.app M) (c.inv.app M') (c.inv.app N) h
  refine ⟨?_⟩
  intro M M' f g
  apply (cancel_mono (SheafOfModules.tensorObjIsoSheafification (R := R) M' N).hom).1
  change (f + g) ▷ N ≫ _ = (f ▷ N + g ▷ N) ≫ _
  rw [hn, Preadditive.add_comp, hn, hn]
  change _ = _ ≫ S.map ((MonoidalCategory.tensorRight N.val).map f.val) +
    _ ≫ S.map ((MonoidalCategory.tensorRight N.val).map g.val)
  rw [← Preadditive.comp_add, ← Functor.map_add, ← Functor.map_add]
  rfl

/-- Tensor in the K-flat second variable preserves quasi-isomorphisms.

Source: Stacks Project, Cohomology on Sites, Tags 06YN and 06YP,
lemma-K-flat-quasi-isomorphism (auxiliary; not a blueprint node).

Proof: the cone of a quasi-isomorphism is acyclic. By the stated K-flatness its
termwise total tensor with P is acyclic. The additive tensor bifunctor identifies
this total tensor with the cone of the tensored map, via
`CochainComplex.mapBifunctorMappingCone₁Iso`. Thus the latter cone is acyclic and
the tensored map is a quasi-isomorphism. Additivity of the sheaf tensor follows
from its identification with sheafification of the presheaf tensor: the latter
is sectionwise additive and sheafification is additive. No regular element,
strict tower, derived-limit functor, or countable-product hypothesis is used.
-/
theorem kFlatTensorPreservesQuasiIsoIndependentCoefficients
    (P : CochainComplex 𝒜 ℤ) (hP : CochainComplex.IsKFlatIndependentCoefficients P)
    {X Y : CochainComplex 𝒜 ℤ} (f : X ⟶ Y) (hf : QuasiIso f) :
    QuasiIso ((koszulTensorFunctor R P).map f) := by
  have : (MonoidalCategory.curriedTensor 𝒜).Additive :=
    ⟨by
      intro X Y f g
      apply NatTrans.ext
      funext N
      exact (tensorRight_additive_reconstruction R N).map_add⟩
  have hc := hP (CochainComplex.mappingCone f)
    ((CochainComplex.mappingCone.quasiIso_iff_acyclic f).1 hf)
  let e := CochainComplex.mapBifunctorMappingCone₁Iso f P
    (MonoidalCategory.curriedTensor 𝒜)
  apply (CochainComplex.mappingCone.quasiIso_iff_acyclic _).2
  intro i
  exact (hc i).of_iso e

end CategoryTheory
