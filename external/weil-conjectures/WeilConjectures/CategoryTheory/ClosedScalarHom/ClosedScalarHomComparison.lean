/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Internal Hom comparison for a tensor preserving left adjoint

The five Hom equivalences of Stacks 07A6 and 08J9 give the comparison and its
restricted-evaluation normalization, independently of the choice of representatives.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u₁ v₁ u₂ v₂
open CategoryTheory Opposite WeilConjectures
namespace CategoryTheory
namespace ClosedScalarHom
variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
  {H : Aᵒᵖ × A ⥤ A} {I : Bᵒᵖ × B ⥤ B}
  (S : CoefficientClosedStructure H) (T : CoefficientClosedStructure I)
  {F : A ⥤ B} {U : B ⥤ A} (adj : F ⊣ U)
  (μ : S.tensor ⋙ F ≅ (F.prod F) ⋙ T.tensor)

/-- The five scalar and closed adjunction bijections.
Source: Stacks 07A6 and 08J9 (blueprint: lem-sfb-closed-scalar-hom-comparison). -/
def bijection (X K : A) (N : B) :
    (X ⟶ U.obj (I.obj (op (F.obj K), N))) ≃ (X ⟶ H.obj (op K, U.obj N)) :=
  (adj.homEquiv X _).symm.trans
    ((T.transpose _ _ _).symm.trans
      ((Iso.homCongr (μ.app (X, K)).symm (Iso.refl N)).trans
        ((adj.homEquiv _ N).trans (S.transpose _ _ _))))

/-- The five-bijection composite commutes with precomposition.
Source: Stacks 07A6 and 08J9 (blueprint: lem-sfb-closed-scalar-hom-comparison). -/
theorem bijection_precomp {X Y : A} (f : X ⟶ Y) (K : A) (N : B)
    (g : Y ⟶ U.obj (I.obj (op (F.obj K), N))) :
    bijection S T adj μ X K N (f ≫ g) = f ≫ bijection S T adj μ Y K N g := by
  dsimp only [bijection, Equiv.trans_apply]
  rw [adj.homEquiv_naturality_left_symm]
  change S.transpose _ _ _ (adj.homEquiv _ _
    ((μ.app (X, K)).hom ≫ (T.transpose _ _ _).symm
      (F.map f ≫ (adj.homEquiv Y _).symm g) ≫ 𝟙 N)) = _
  have hT : (T.transpose (F.obj X) (F.obj K) N).symm
      (F.map f ≫ (adj.homEquiv Y _).symm g) =
      T.tensor.map (Prod.mkHom (F.map f) (𝟙 (F.obj K))) ≫
        (T.transpose (F.obj Y) (F.obj K) N).symm ((adj.homEquiv Y _).symm g) :=
    by simpa [CoefficientClosedStructure.transpose, CoefficientClosedStructure.tensor,
      Prod.sectR, Functor.comp_obj] using
      (T.adjunction (F.obj K)).homEquiv_naturality_left_symm (F.map f)
        ((adj.homEquiv Y _).symm g)
  rw [hT]
  dsimp only [Iso.homCongr, Equiv.coe_fn_mk, Iso.symm_inv, Iso.refl_hom]
  simp only [Category.comp_id]
  have hμ := μ.hom.naturality (Prod.mkHom f (𝟙 K))
  dsimp only [Functor.comp_map, Functor.prod_map] at hμ
  simp only [Functor.map_id] at hμ
  change F.map (S.tensor.map (Prod.mkHom f (𝟙 K))) ≫ (μ.app (Y, K)).hom =
    (μ.app (X, K)).hom ≫ T.tensor.map (Prod.mkHom (F.map f) (𝟙 (F.obj K))) at hμ
  rw [← Category.assoc, ← hμ, Category.assoc, adj.homEquiv_naturality_left]
  simpa [CoefficientClosedStructure.transpose, CoefficientClosedStructure.tensor,
      Prod.sectR, Functor.comp_obj] using
    (S.adjunction K).homEquiv_naturality_left f
      (adj.homEquiv _ _ ((μ.app (Y, K)).hom ≫
        (T.transpose _ _ _).symm ((adj.homEquiv Y _).symm g)))

private theorem uncurry_formula (X K N : A) (t : X ⟶ H.obj (op K, N)) :
    (S.transpose X K N).symm t =
      S.tensor.map (Prod.mkHom t (𝟙 K)) ≫ S.evaluation K N := by
  change (@MonoidalCategory.tensorRight A _ S.monoidal K).map t ≫
    S.evaluation K N = _
  let _ := S.monoidal
  simp [CoefficientClosedStructure.tensor]

private theorem evaluation_target (K N N' : A) (n : N ⟶ N') :
    S.tensor.map (Prod.mkHom (H.map (Prod.mkHom (𝟙 (op K)) n)) (𝟙 K)) ≫
      S.evaluation K N' = S.evaluation K N ≫ n := by
  simpa [CoefficientClosedStructure.evaluation, CoefficientClosedStructure.tensor,
    Prod.sectR] using (S.adjunction K).counit.naturality n

private theorem evaluation_source (K K' N : A) (f : K' ⟶ K) :
    S.tensor.map (Prod.mkHom (H.map (Prod.mkHom f.op (𝟙 N))) (𝟙 K')) ≫
      S.evaluation K' N =
    S.tensor.map (Prod.mkHom (𝟙 (H.obj (op K, N))) f) ≫ S.evaluation K N := by
  simpa [CoefficientClosedStructure.evaluation, CoefficientClosedStructure.tensor,
    Prod.sectR] using S.evaluation_naturality K K' N f

private theorem evaluation_both (K K' N N' : A) (f : K' ⟶ K) (n : N ⟶ N') :
    S.tensor.map (Prod.mkHom (H.map (Prod.mkHom f.op n)) (𝟙 K')) ≫
      S.evaluation K' N' =
    S.tensor.map (Prod.mkHom (𝟙 (H.obj (op K, N))) f) ≫ S.evaluation K N ≫ n := by
  have hf : Prod.mkHom f.op n =
      Prod.mkHom f.op (𝟙 N) ≫ Prod.mkHom (𝟙 (op K')) n := by simp
  rw [hf, H.map_comp]
  have ht : Prod.mkHom
      (H.map (Prod.mkHom f.op (𝟙 N)) ≫ H.map (Prod.mkHom (𝟙 (op K')) n)) (𝟙 K') =
      Prod.mkHom (H.map (Prod.mkHom f.op (𝟙 N))) (𝟙 K') ≫
        Prod.mkHom (H.map (Prod.mkHom (𝟙 (op K')) n)) (𝟙 K') := by simp
  rw [ht, S.tensor.map_comp, Category.assoc, evaluation_target,
    ← Category.assoc, evaluation_source, Category.assoc]

private theorem uncurry_naturality (X K K' N N' : A)
    (t : X ⟶ H.obj (op K, N)) (f : K' ⟶ K) (n : N ⟶ N') :
    (S.transpose X K' N').symm (t ≫ H.map (Prod.mkHom f.op n)) =
      S.tensor.map (Prod.mkHom (𝟙 X) f) ≫ (S.transpose X K N).symm t ≫ n := by
  rw [uncurry_formula, uncurry_formula]
  have ht : Prod.mkHom (t ≫ H.map (Prod.mkHom f.op n)) (𝟙 K') =
      Prod.mkHom t (𝟙 K') ≫ Prod.mkHom (H.map (Prod.mkHom f.op n)) (𝟙 K') := by simp
  rw [ht, S.tensor.map_comp, Category.assoc, evaluation_both]
  have ht' : Prod.mkHom t (𝟙 K') ≫ Prod.mkHom (𝟙 (H.obj (op K, N))) f =
      Prod.mkHom (𝟙 X) f ≫ Prod.mkHom t (𝟙 K) := by simp
  rw [← Category.assoc, ← Category.assoc, ← S.tensor.map_comp, ht', S.tensor.map_comp]
  simp only [Category.assoc]

/-- The five-bijection composite is natural in its two remaining inputs.
Source: Stacks 07A6 and 08J9 (blueprint: lem-sfb-closed-scalar-hom-comparison). -/
theorem bijection_naturality (X K K' : A) (N N' : B)
    (g : X ⟶ U.obj (I.obj (op (F.obj K), N))) (f : K' ⟶ K) (n : N ⟶ N') :
    bijection S T adj μ X K' N'
        (g ≫ U.map (I.map (Prod.mkHom (F.map f).op n))) =
      bijection S T adj μ X K N g ≫ H.map (Prod.mkHom f.op (U.map n)) := by
  dsimp only [bijection, Equiv.trans_apply]
  rw [adj.homEquiv_naturality_right_symm, uncurry_naturality]
  dsimp only [Iso.homCongr, Equiv.coe_fn_mk, Iso.symm_inv, Iso.refl_hom]
  simp only [Category.comp_id]
  have hμ := μ.hom.naturality (Prod.mkHom (𝟙 X) f)
  change F.map (S.tensor.map (Prod.mkHom (𝟙 X) f)) ≫ (μ.app (X, K)).hom =
    (μ.app (X, K')).hom ≫ T.tensor.map (Prod.mkHom (F.map (𝟙 X)) (F.map f)) at hμ
  rw [F.map_id] at hμ
  rw [← Category.assoc, ← Category.assoc, ← hμ]
  simp only [Category.assoc]
  erw [adj.homEquiv_naturality_left
    (S.tensor.map (Prod.mkHom (𝟙 X) f))]
  rw [← Category.assoc ((μ.app (X, K)).hom), adj.homEquiv_naturality_right]
  apply (S.transpose X K' (U.obj N')).symm.injective
  rw [Equiv.symm_apply_apply, uncurry_naturality, Equiv.symm_apply_apply]
  rfl

/-- The representing isomorphism obtained by applying the bijection to identities.
Source: Stacks 07A6 and 08J9 (blueprint: lem-sfb-closed-scalar-hom-comparison). -/
def component (K : A) (N : B) :
    U.obj (I.obj (op (F.obj K), N)) ≅ H.obj (op K, U.obj N) := by
  let E := U.obj (I.obj (op (F.obj K), N))
  let V := H.obj (op K, U.obj N)
  let α := bijection S T adj μ E K N (𝟙 E)
  let β := (bijection S T adj μ V K N).symm (𝟙 V)
  have hβ : bijection S T adj μ V K N β = 𝟙 V := Equiv.apply_symm_apply _ _
  have hrep {X : A} (t : X ⟶ E) : bijection S T adj μ X K N t = t ≫ α := by
    simpa only [Category.comp_id] using bijection_precomp S T adj μ t K N (𝟙 E)
  refine ⟨α, β, ?_, ?_⟩
  · apply (bijection S T adj μ E K N).injective
    rw [bijection_precomp, hβ, Category.comp_id]
  · rw [← hrep, hβ]

/-- Postcomposition with the representing map is the five-bijection composite.
Source: Stacks 07A6 and 08J9 (blueprint: lem-sfb-closed-scalar-hom-comparison). -/
theorem component_rep (X K : A) (N : B)
    (t : X ⟶ U.obj (I.obj (op (F.obj K), N))) :
    bijection S T adj μ X K N t = t ≫ (component S T adj μ K N).hom := by
  change bijection S T adj μ X K N t = t ≫ bijection S T adj μ _ K N (𝟙 _)
  simpa only [Category.comp_id] using bijection_precomp S T adj μ t K N (𝟙 _)

/-- A tensor-preserving left adjoint carries the closed-Hom adjunction to its
restriction-of-scalars comparison, naturally in both inputs.
Source: Stacks 07A6 and 08J9; the five representing Hom bijections.
(blueprint: lem-sfb-closed-scalar-hom-comparison).
Proof: compose the two scalar transposes, the two closed transposes, and the
strong tensor comparison. Naturality in a testing object identifies this
bijection with postcomposition by its value at the identity. Apply the inverse
bijection to the target identity to obtain the inverse map. Naturality in the
two remaining objects gives naturality of these component isomorphisms. -/
def iso : ((F.op.prod (𝟭 B)) ⋙ I ⋙ U) ≅ ((𝟭 Aᵒᵖ).prod U ⋙ H) :=
  NatIso.ofComponents (fun p ↦ component S T adj μ p.1.unop p.2) (by
    rintro ⟨K, N⟩ ⟨K', N'⟩ ⟨f, n⟩
    have h := bijection_naturality S T adj μ
      (U.obj (I.obj (op (F.obj K.unop), N))) K.unop K'.unop N N' (𝟙 _) f.unop n
    rw [component_rep, component_rep, Category.id_comp] at h
    simpa using h)

/-- The comparison induces precisely the five defining Hom bijections.
Source: Stacks 07A6 and 08J9 (blueprint: lem-sfb-closed-scalar-hom-comparison). -/
theorem representing (X K : A) (N : B)
    (t : X ⟶ U.obj (I.obj (op (F.obj K), N))) :
    bijection S T adj μ X K N t = t ≫ (iso S T adj μ).hom.app (op K, N) := by
  exact component_rep S T adj μ X K N t

/-- The lax tensor map on the right adjoint is the mate of the strong tensor map.
Source: Stacks 07A4 and 07A6 (blueprint: lem-sfb-closed-scalar-hom-comparison). -/
def restrictionTensor (P Q : B) :
    S.tensor.obj (U.obj P, U.obj Q) ⟶ U.obj (T.tensor.obj (P, Q)) :=
  adj.unit.app _ ≫ U.map (μ.hom.app _ ≫
    T.tensor.map (Prod.mkHom (adj.counit.app P) (adj.counit.app Q)))

/-- Restricted evaluation preceded by the extension unit in the second tensor factor.
Source: Stacks 07A6 and 08J9 (blueprint: lem-sfb-closed-scalar-hom-comparison). -/
def restrictedEvaluation (K : A) (N : B) :
    S.tensor.obj (U.obj (I.obj (op (F.obj K), N)), K) ⟶ U.obj N :=
  S.tensor.map (Prod.mkHom (𝟙 _) (adj.unit.app K)) ≫
    restrictionTensor S T adj μ (I.obj (op (F.obj K), N)) (F.obj K) ≫
      U.map (T.evaluation (F.obj K) N)

private theorem restrictionTensor_unit (P : B) (K : A) :
    S.tensor.map (Prod.mkHom (𝟙 (U.obj P)) (adj.unit.app K)) ≫
        restrictionTensor S T adj μ P (F.obj K) =
      adj.unit.app _ ≫ U.map (μ.hom.app (U.obj P, K) ≫
        T.tensor.map (Prod.mkHom (adj.counit.app P) (𝟙 (F.obj K)))) := by
  dsimp only [restrictionTensor]
  rw [← Category.assoc]
  erw [← adj.unit_naturality]
  rw [Category.assoc, ← U.map_comp]
  have hμ := μ.hom.naturality (Prod.mkHom (𝟙 (U.obj P)) (adj.unit.app K))
  dsimp only [Functor.comp_map, Functor.prod_map] at hμ
  erw [← Category.assoc, hμ, Category.assoc, ← T.tensor.map_comp]
  simp

/-- Evaluation uniquely normalizes the comparison, using the scalar triangle identity.
Source: Stacks 07A6 and 08J9 (blueprint: lem-sfb-closed-scalar-hom-comparison).
Proof: unroll the five Hom bijections at the source identity. Naturality of the
scalar unit and of the strong tensor map moves the extra scalar unit to the
second factor, where the scalar counit cancels it by the triangle identity. -/
theorem evaluation (K : A) (N : B) :
    (S.transpose _ K (U.obj N)).symm ((iso S T adj μ).hom.app (op K, N)) =
      restrictedEvaluation S T adj μ K N := by
  change (S.transpose _ K (U.obj N)).symm
    (bijection S T adj μ _ K N (𝟙 _)) = _
  dsimp only [bijection, Equiv.trans_apply]
  rw [Equiv.symm_apply_apply, adj.homEquiv_symm_id]
  dsimp only [Iso.homCongr, Equiv.coe_fn_mk, Iso.symm_inv, Iso.refl_hom]
  simp only [Category.comp_id]
  rw [uncurry_formula]
  dsimp only [restrictedEvaluation]
  conv_rhs =>
    rw [← Category.assoc, restrictionTensor_unit]
  simp only [Category.assoc, ← U.map_comp]
  rfl

/-- Equality of restricted evaluations determines the natural isomorphism uniquely.
Source: Stacks 08J9 (blueprint: lem-sfb-closed-scalar-hom-comparison).
Proof: the closed transpose is bijective, so its prescribed value determines
each component. Natural transformations and natural isomorphisms are extensional. -/
theorem unique (β : ((F.op.prod (𝟭 B)) ⋙ I ⋙ U) ≅ ((𝟭 Aᵒᵖ).prod U ⋙ H))
    (hβ : ∀ (K : A) (N : B), (S.transpose _ K (U.obj N)).symm
      (β.hom.app (op K, N)) = restrictedEvaluation S T adj μ K N) :
    β = iso S T adj μ := by
  apply Iso.ext
  ext ⟨K, N⟩
  apply (S.transpose _ K.unop (U.obj N)).symm.injective
  exact (hβ K.unop N).trans (evaluation S T adj μ K.unop N).symm

end ClosedScalarHom
end CategoryTheory
