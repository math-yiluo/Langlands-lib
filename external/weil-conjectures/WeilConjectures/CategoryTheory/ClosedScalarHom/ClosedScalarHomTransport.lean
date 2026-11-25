/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.ClosedScalarHom.ClosedScalarHomComparison
import all WeilConjectures.CategoryTheory.ClosedScalarHom.ClosedScalarHomComparison
/-! # Transport of the normalized closed-Hom comparison along adjoint isomorphisms -/
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u₁ v₁ u₂ v₂
open CategoryTheory Opposite WeilConjectures
namespace CategoryTheory.ClosedScalarHom
variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
  {H : Aᵒᵖ × A ⥤ A} {I : Bᵒᵖ × B ⥤ B}
  (S : CoefficientClosedStructure H) (T : CoefficientClosedStructure I)
  {F F' : A ⥤ B} {U U' : B ⥤ A} (adj : F ⊣ U) (adj' : F' ⊣ U')
  (d : U' ≅ U) (c : F ≅ F')
  (hc : ∀ X N (f : F'.obj X ⟶ N),
    adj.homEquiv X N (c.hom.app X ≫ f) = adj'.homEquiv X N f ≫ d.hom.app N)
  (μ : S.tensor ⋙ F ≅ (F.prod F) ⋙ T.tensor)
  (ν : S.tensor ⋙ F' ≅ (F'.prod F') ⋙ T.tensor)
  (hμ : ∀ X K, μ.hom.app (X, K) ≫
    T.tensor.map (Prod.mkHom (c.hom.app X) (c.hom.app K)) =
      c.hom.app (S.tensor.obj (X, K)) ≫ ν.hom.app (X, K))

include hc hμ in
/-- Transporting a scalar adjunction and its tensor comparison transports the closed-Hom map.
Source: Stacks 07A6 and 0D6D (blueprint: lem-sfb-closed-scalar-hom-transport).
Proof: apply the closed transpose, followed by the inverse scalar transpose, to both
sides. The adjunction compatibility moves d across the scalar transpose. Naturality
of evaluation moves c in the internal-Hom input to the second tensor factor. The
compatibility of mu and nu then identifies the two maps. -/
theorem transport (K : A) (N : B) :
    (iso S T adj' ν).hom.app (op K, N) ≫ H.map (Prod.mkHom (𝟙 (op K)) (d.hom.app N)) =
      d.hom.app (I.obj (op (F'.obj K), N)) ≫
        U.map (I.map (Prod.mkHom (c.hom.app K).op (𝟙 N))) ≫
          (iso S T adj μ).hom.app (op K, N) := by
  rw [← representing S T adj μ, ← bijection_precomp]
  let Z := I.obj (op (F'.obj K), N)
  let X := U'.obj Z
  let t : F'.obj X ⟶ Z := (adj'.homEquiv X Z).symm (𝟙 X)
  let j := I.map (Prod.mkHom (c.hom.app K).op (𝟙 N))
  have hj : (adj.homEquiv X _).symm (d.hom.app Z ≫ U.map j) =
      c.hom.app X ≫ t ≫ j := by
    apply (adj.homEquiv X _).injective
    rw [Equiv.apply_symm_apply, hc, adj'.homEquiv_naturality_right,
      Equiv.apply_symm_apply, Category.id_comp]
    exact (d.hom.naturality j).symm
  have hl := representing S T adj' ν X K N (𝟙 X)
  simp only [Category.id_comp] at hl
  rw [← hl]
  dsimp only [bijection, Equiv.trans_apply, Iso.homCongr,
    Equiv.coe_fn_mk, Iso.symm_inv, Iso.refl_hom]
  simp only [Category.comp_id]
  have hS (f : S.tensor.obj (X, K) ⟶ U'.obj N) :
      S.transpose _ _ _ f ≫ H.map (Prod.mkHom (𝟙 (op K)) (d.hom.app N)) =
        S.transpose X K (U.obj N) (f ≫ d.hom.app N) := by
    exact ((S.adjunction K).homEquiv_naturality_right f (d.hom.app N)).symm
  rw [hS]
  apply congrArg (S.transpose X K (U.obj N))
  erw [← hc]
  apply congrArg (adj.homEquiv _ N)
  change c.hom.app (S.tensor.obj (X, K)) ≫ ν.hom.app (X, K) ≫
      (T.transpose _ _ N).symm t =
    μ.hom.app (X, K) ≫ (T.transpose _ _ N).symm
      ((adj.homEquiv X _).symm (d.hom.app Z ≫ U.map j))
  rw [hj, ← reassoc_of% (hμ X K)]
  let := T.monoidal
  have hT : (T.transpose (F.obj X) (F.obj K) N).symm
      (c.hom.app X ≫ t ≫ j) =
      T.tensor.map (Prod.mkHom (c.hom.app X) (c.hom.app K)) ≫
        (T.transpose (F'.obj X) (F'.obj K) N).symm t := by
    rw [← Category.assoc]
    change (T.transpose _ _ N).symm
      ((c.hom.app X ≫ t) ≫ I.map (Prod.mkHom (c.hom.app K).op (𝟙 N))) = _
    rw [uncurry_naturality]
    have hp := (T.adjunction (F'.obj K)).homEquiv_naturality_left_symm
      (c.hom.app X) t
    change (T.transpose _ _ N).symm (c.hom.app X ≫ t) =
      (@MonoidalCategory.tensorRight B _ T.monoidal (F'.obj K)).map (c.hom.app X) ≫
        (T.transpose _ _ N).symm t at hp
    rw [hp]
    simp only [CoefficientClosedStructure.tensor, MonoidalCategory.tensorRight,
      MonoidalCategory.tensor, MonoidalCategory.curriedTensor, Functor.flip,
      Category.comp_id, MonoidalCategory.id_tensorHom]
    erw [← MonoidalCategory.tensorHom_def'_assoc]
  rw [hT]

/-- The canonical left-adjoint uniqueness map has the required transpose compatibility.
Source: adjoint uniqueness, Stacks 07A6 (blueprint: lem-sfb-closed-scalar-hom-transport).
Proof: naturality moves the final map past the hom equivalence. The unit identity
for leftAdjointUniq and the transported-adjunction hom equivalence finish. -/
theorem adjunction_compatibility (X : A) (N : B) (f : F'.obj X ⟶ N) :
    adj.homEquiv X N
        ((Adjunction.leftAdjointUniq adj (adj'.ofNatIsoRight d)).hom.app X ≫ f) =
      adj'.homEquiv X N f ≫ d.hom.app N := by
  rw [adj.homEquiv_naturality_right, Adjunction.homEquiv_leftAdjointUniq_hom_app]
  rw [← Adjunction.homEquiv_unit]
  exact Adjunction.homEquiv_ofNatIsoRight_apply adj' d f

/-- The closed-Hom comparison for the identity tensor adjunction is the identity.
Source: Stacks 07A6 (blueprint: lem-sfb-closed-scalar-hom-transport).
Proof: expand the five equivalences; the identity scalar equivalences and tensor
comparison disappear and the two closed transposes cancel. -/
theorem identity (K N : A) :
    (iso S S Adjunction.id (Iso.refl S.tensor)).hom.app (op K, N) = 𝟙 _ := by
  have hi (X Y : A) (f : X ⟶ Y) : Adjunction.id.homEquiv X Y f = f := by
    rw [Adjunction.homEquiv_unit]
    simp
  have hi' (X Y : A) (f : X ⟶ Y) : (Adjunction.id.homEquiv X Y).symm f = f := by
    apply (Adjunction.id.homEquiv X Y).injective
    rw [Equiv.apply_symm_apply, hi]
  change bijection S S Adjunction.id (Iso.refl S.tensor) _ K N (𝟙 _) = _
  dsimp only [bijection, Equiv.trans_apply, Iso.homCongr, Equiv.coe_fn_mk,
    Iso.symm_inv, Iso.refl_hom]
  simp only [hi, hi', Iso.app_hom, Iso.refl_hom, NatTrans.id_app, Category.comp_id,
    Functor.id_obj]
  change S.transpose (H.obj (op K, N)) K N
    (𝟙 _ ≫ (S.transpose _ K N).symm (𝟙 _)) = 𝟙 _
  rw [Category.id_comp, Equiv.apply_symm_apply]

/-- Identity transport of the five-Hom comparison, with its identity map simplified.
Source: Stacks 07A6 (blueprint: lem-sfb-closed-scalar-hom-transport).
Proof: specialize transport to the identity adjunction and use the identity
comparison proved above. The last identity morphism disappears. -/
theorem transport_identity {F₀ U₀ : A ⥤ A} (a₀ : F₀ ⊣ U₀)
    (d₀ : U₀ ≅ 𝟭 A) (c₀ : 𝟭 A ≅ F₀)
    (hc₀ : ∀ X N (f : F₀.obj X ⟶ N),
      Adjunction.id.homEquiv X N (c₀.hom.app X ≫ f) =
        a₀.homEquiv X N f ≫ d₀.hom.app N)
    (ν₀ : S.tensor ⋙ F₀ ≅ (F₀.prod F₀) ⋙ S.tensor)
    (hν₀ : ∀ X K, S.tensor.map (Prod.mkHom (c₀.hom.app X) (c₀.hom.app K)) =
      c₀.hom.app (S.tensor.obj (X, K)) ≫ ν₀.hom.app (X, K))
    (K N : A) :
    (iso S S a₀ ν₀).hom.app (op K, N) ≫
        H.map (Prod.mkHom (𝟙 (op K)) (d₀.hom.app N)) =
      d₀.hom.app (H.obj (op (F₀.obj K), N)) ≫
        H.map (Prod.mkHom (c₀.hom.app K).op (𝟙 N)) := by
  have ht := transport S S Adjunction.id a₀ d₀ c₀ hc₀ (Iso.refl S.tensor) ν₀
    (by
      intro X K
      change (𝟙 _) ≫ S.tensor.map (Prod.mkHom (c₀.hom.app X) (c₀.hom.app K)) = _
      erw [Category.id_comp]
      exact hν₀ X K) K N
  rw [identity] at ht
  erw [Category.comp_id] at ht
  exact ht

end CategoryTheory.ClosedScalarHom
