/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Limits.Colimits

/-!
# Left Kan extension along a left adjoint, left Kan extension is monoidal

If `L : C ⥤ D` admits a right adjoint `R`, the left Kan extension functor `L.lan` is
precomposition with `R` (`CategoryTheory.Functor.lanIsoWhiskeringLeft`): both are left
adjoint to precomposition with `L`. Consequently `L.lan` preserves every limit that exists
in the target category (`CategoryTheory.Functor.preservesLimitsOfShape_lan`), since limits
in functor categories are computed pointwise.

This is complementary to `CategoryTheory.lan_preservesFiniteLimits_of_flat`, which holds for
an arbitrary representably flat `L` but computes `L.lan` as a filtered colimit and therefore
assumes the source and target sites to be small and the coefficient category to be concrete
with filtered colimits commuting with finite limits. Along a left adjoint no such hypothesis
is needed, because the colimit is over a category with a terminal object.

For a monoidal category `H`, left Kan extension `L.lan : (C ⥤ H) ⥤ (D ⥤ H)` is oplax monoidal
for the pointwise tensor products, being left adjoint to the monoidal restriction functor
(`CategoryTheory.Functor.lanOplaxMonoidal`). Its comparison maps are isomorphisms when the
categories `CostructuredArrow L X` are sifted and tensoring in `H` preserves colimits of these
shapes in each variable (`CategoryTheory.Functor.isIso_lan_δ`), respectively connected
(`CategoryTheory.Functor.isIso_lan_η`): at `X` they compare two colimits over
`CostructuredArrow L X`. This applies to a representably coflat `L`, whose comma categories
`CostructuredArrow L X` are filtered, hence sifted.
-/

@[expose] public section

namespace CategoryTheory.Functor

open Limits

universe vC uC vD uD vH uH w₁ w₂

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {H : Type uH} [Category.{vH} H] {L : C ⥤ D} {R : D ⥤ C}

section Adjunction

variable [∀ F : C ⥤ H, L.HasLeftKanExtension F]

/-- If `adj : L ⊣ R`, then the left Kan extension along `L` is precomposition with `R`:
both are left adjoint to precomposition with `L`. -/
noncomputable def lanIsoWhiskeringLeft (adj : L ⊣ R) :
    (L.lan : (C ⥤ H) ⥤ D ⥤ H) ≅ (whiskeringLeft D C H).obj R :=
  (L.lanAdjunction H).leftAdjointUniq (Adjunction.whiskerLeft H adj)

/-- Left Kan extension along a left adjoint preserves limits of any shape that exists in the
target category. -/
lemma preservesLimitsOfShape_lan_of_adjunction (adj : L ⊣ R) (E : Type w₁) [Category.{w₂} E]
    [HasLimitsOfShape E H] : PreservesLimitsOfShape E (L.lan : (C ⥤ H) ⥤ D ⥤ H) :=
  preservesLimitsOfShape_of_natIso (lanIsoWhiskeringLeft (H := H) adj).symm

end Adjunction

section IsLeftAdjoint

variable (L) [L.IsLeftAdjoint] [∀ F : C ⥤ H, L.HasLeftKanExtension F]

/-- Left Kan extension along a left adjoint preserves limits of any shape that exists in the
target category. -/
instance preservesLimitsOfShape_lan (E : Type w₁) [Category.{w₂} E] [HasLimitsOfShape E H] :
    PreservesLimitsOfShape E (L.lan : (C ⥤ H) ⥤ D ⥤ H) :=
  preservesLimitsOfShape_lan_of_adjunction (Adjunction.ofIsLeftAdjoint L) E

/-- Left Kan extension along a left adjoint is left exact. -/
instance preservesFiniteLimits_lan [HasFiniteLimits H] :
    PreservesFiniteLimits (L.lan : (C ⥤ H) ⥤ D ⥤ H) where
  preservesFiniteLimits _ := inferInstance

end IsLeftAdjoint

section Monoidal

open MonoidalCategory Limits

variable (L) (H) [MonoidalCategory H] [∀ F : C ⥤ H, L.HasPointwiseLeftKanExtension F]

/-- Left Kan extension `L.lan` is oplax monoidal for the pointwise tensor products, being
left adjoint to the monoidal restriction functor along `L`. -/
noncomputable instance lanOplaxMonoidal : (L.lan : (C ⥤ H) ⥤ (D ⥤ H)).OplaxMonoidal :=
  (L.lanAdjunction H).leftAdjointOplaxMonoidal

/-- The adjunction `L.lan ⊣ (whiskeringLeft C D H).obj L` is monoidal. -/
instance isMonoidal_lanAdjunction : (L.lanAdjunction H).IsMonoidal := by
  let := (L.lanAdjunction H).leftAdjointOplaxMonoidal
  infer_instance

variable {H}

/-- The comparison map `δ : L.lan (P ⊗ Q) ⟶ L.lan P ⊗ L.lan Q` restricts along the units to
the tensor product of the units, i.e. the following diagram commutes:
```
  (P ⊗ Q).obj c ──(lanUnit (P ⊗ Q)).app c──▶ (L.lan (P ⊗ Q)).obj (L.obj c)
        ‖                                          │ δ.app (L.obj c)
        ‖                                          ▼
  P.obj c ⊗ Q.obj c ──unit_P ⊗ unit_Q──▶ (L.lan P).obj (L.obj c) ⊗ (L.lan Q).obj (L.obj c)
```
-/
@[reassoc (attr := simp)]
lemma lanUnit_app_app_δ_app (P Q : C ⥤ H) (c : C) :
    (L.lanUnit.app (P ⊗ Q)).app c ≫ (OplaxMonoidal.δ L.lan P Q).app (L.obj c) =
      (L.lanUnit.app P).app c ⊗ₘ (L.lanUnit.app Q).app c := by
  simpa using congr_app (Adjunction.unit_app_tensor_comp_map_δ (L.lanAdjunction H) P Q) c

/-- The comparison map `η : L.lan 𝟙 ⟶ 𝟙` restricts along the unit to the identity, i.e. the
composite
```
  𝟙_ H ──(lanUnit 𝟙).app c──▶ (L.lan 𝟙).obj (L.obj c) ──η.app (L.obj c)──▶ 𝟙_ H
```
is the identity. -/
@[reassoc (attr := simp)]
lemma lanUnit_app_app_η_app (c : C) :
    (L.lanUnit.app (𝟙_ (C ⥤ H))).app c ≫ (OplaxMonoidal.η (L.lan (H := H))).app (L.obj c) =
      𝟙 _ := by
  simpa using congr_app (Adjunction.unit_app_unit_comp_map_η (L.lanAdjunction H)) c

/-- The comparison map `δ : L.lan (P ⊗ Q) ⟶ L.lan P ⊗ L.lan Q` is an isomorphism if the
categories `CostructuredArrow L X` are sifted and the tensor product preserves colimits of
these shapes in each variable. At `X`, both sides are colimits over `CostructuredArrow L X`
(the right one because the category is sifted), and `δ.app X` is the morphism of cocones
```
  (P ⊗ Q).obj c ──ι_f──▶ colim (P ⊗ Q) = (L.lan (P ⊗ Q)).obj X
        ‖                         │ δ.app X
        ‖                         ▼
  P.obj c ⊗ Q.obj c ──ι_f ⊗ ι_f──▶ (L.lan P).obj X ⊗ (L.lan Q).obj X
```
over the legs indexed by `f : L.obj c ⟶ X`. This applies to a representably coflat `L`. -/
instance isIso_lan_δ [∀ X : D, IsSifted (CostructuredArrow L X)]
    [∀ (X : D) (M : H), PreservesColimitsOfShape (CostructuredArrow L X) (tensorLeft M)]
    [∀ (X : D) (M : H), PreservesColimitsOfShape (CostructuredArrow L X) (tensorRight M)]
    (P Q : C ⥤ H) : IsIso (OplaxMonoidal.δ L.lan P Q) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  have : PreservesColimit₂ (CostructuredArrow.proj L X ⋙ P) (CostructuredArrow.proj L X ⋙ Q)
      (curriedTensor H) :=
    PreservesColimit₂.of_preservesColimits_in_each_variable _
  let φ : (LeftExtension.mk _ (L.leftKanExtensionUnit (P ⊗ Q))).coconeAt X ⟶
      ((LeftExtension.mk _ (L.leftKanExtensionUnit P)).coconeAt X).tensor
        ((LeftExtension.mk _ (L.leftKanExtensionUnit Q)).coconeAt X) :=
    { hom := (OplaxMonoidal.δ L.lan P Q).app X
      w f := by
        -- `LeftExtension.coconeAt_ι_app` produces a goal that is not type correct at reducible
        -- transparency, since `L.leftKanExtension P` is only defeq to `L.lan.obj P`
        change ((L.lanUnit.app (P ⊗ Q)).app f.left ≫ (L.lan.obj (P ⊗ Q)).map f.hom) ≫
            (OplaxMonoidal.δ L.lan P Q).app X =
          ((L.lanUnit.app P).app f.left ≫ (L.lan.obj P).map f.hom) ⊗ₘ
            ((L.lanUnit.app Q).app f.left ≫ (L.lan.obj Q).map f.hom)
        rw [Category.assoc, (OplaxMonoidal.δ L.lan P Q).naturality f.hom,
          lanUnit_app_app_δ_app_assoc]
        exact tensorHom_comp_tensorHom _ _ _ _ }
  have := IsColimit.hom_isIso (L.isPointwiseLeftKanExtensionLeftKanExtensionUnit (P ⊗ Q) X)
    ((L.isPointwiseLeftKanExtensionLeftKanExtensionUnit P X).tensor
      (L.isPointwiseLeftKanExtensionLeftKanExtensionUnit Q X)) φ
  exact (Cocone.forget _).map_isIso φ

/-- The comparison map `η : L.lan 𝟙 ⟶ 𝟙` is an isomorphism if the categories
`CostructuredArrow L X` are connected: at `X` it is the colimit of a constant functor over
`CostructuredArrow L X`. This applies to a representably coflat `L`. -/
instance isIso_lan_η [∀ X : D, IsConnected (CostructuredArrow L X)] :
    IsIso (OplaxMonoidal.η (L.lan (H := H))) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  let φ : (LeftExtension.mk _ (L.leftKanExtensionUnit (𝟙_ (C ⥤ H)))).coconeAt X ⟶
      constCocone (CostructuredArrow L X) (𝟙_ H) :=
    { hom := (OplaxMonoidal.η (L.lan (H := H))).app X
      w f := by
        change ((L.lanUnit.app (𝟙_ (C ⥤ H))).app f.left ≫
            (L.lan.obj (𝟙_ (C ⥤ H))).map f.hom) ≫ (OplaxMonoidal.η (L.lan (H := H))).app X =
          𝟙 (𝟙_ H)
        rw [Category.assoc, (OplaxMonoidal.η (L.lan (H := H))).naturality f.hom,
          lanUnit_app_app_η_app_assoc]
        rfl }
  have := IsColimit.hom_isIso (L.isPointwiseLeftKanExtensionLeftKanExtensionUnit _ X)
    (isColimitConstCocone _ _) φ
  exact (Cocone.forget _).map_isIso φ

end Monoidal

end CategoryTheory.Functor
