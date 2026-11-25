/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.SignedKoszulCompletionModel

/-!
# Transport of one signed Koszul summand

Source: Stacks Project, algebraization.tex, Tag 0A0E,
lemma-derived-completion-koszul, finite free tensor calculation.
(auxiliary; not a blueprint node).

This isolates the scalar-action and equality-transport calculation for one erased
index. It is strictly smaller than the finite sum differential theorem.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u z
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace CategoryTheory

private theorem tensor_degree_transport
    {E : Type*} [Category* E] [Preadditive E] [HasCountableCoproducts E]
    [MonoidalCategory E] [MonoidalPreadditive E]
    (K Q : CochainComplex E ℤ) (p p' n n' t : ℤ)
    (hp : p = p') (hn : n = n') (h : p + n = t) (h' : p' + n' = t)
    (β : MonoidalCategory.tensorUnit E ⟶ Q.X n') :
    (MonoidalCategory.rightUnitor (K.X p)).inv ≫
        (MonoidalCategory.tensorLeft (K.X p)).map
          (β ≫ eqToHom (congrArg Q.X hn.symm)) ≫
        CochainComplex.ιMapBifunctor K Q (MonoidalCategory.curriedTensor E) p n t h =
      (K.XIsoOfEq hp).hom ≫ (MonoidalCategory.rightUnitor (K.X p')).inv ≫
        MonoidalCategory.tensorHom (𝟙 _) β ≫
        CochainComplex.ιMapBifunctor K Q (MonoidalCategory.curriedTensor E) p' n' t h' := by
  subst p'
  subst n'
  simp only [eqToHom_refl, Category.comp_id, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_hom, Category.id_comp, MonoidalCategory.id_tensorHom]
  rfl

private theorem signed_tensor_degree_transport
    {E : Type*} [Category* E] [Preadditive E] [HasCountableCoproducts E]
    [MonoidalCategory E] [MonoidalPreadditive E]
    {R A : Type*} [CommRing R] [CommRing A] [Linear R E]
    (ρ : A →+* R) (b : A) (K Q : CochainComplex E ℤ)
    (p p' n n' t : ℤ) (hp : p = p') (hn : n = n')
    (h : p + n = t) (h' : p' + n' = t)
    (s : MonoidalCategory.tensorUnit E ⟶ MonoidalCategory.tensorUnit E)
    (hs : (MonoidalCategory.rightUnitor (K.X p)).inv ≫
      (MonoidalCategory.tensorLeft (K.X p)).map s =
        (ρ b) • (MonoidalCategory.rightUnitor (K.X p)).inv)
    (β : MonoidalCategory.tensorUnit E ⟶ Q.X n') :
    ((-1 : ℤˣ) ^ p) • (MonoidalCategory.rightUnitor (K.X p)).inv ≫
        (MonoidalCategory.tensorLeft (K.X p)).map
          (s ≫ β ≫ eqToHom (congrArg Q.X hn.symm)) ≫
        CochainComplex.ιMapBifunctor K Q (MonoidalCategory.curriedTensor E) p n t h =
      ((ρ ((if Even p then 1 else -1) * b)) • (K.XIsoOfEq hp).hom) ≫
        (MonoidalCategory.rightUnitor (K.X p')).inv ≫
        MonoidalCategory.tensorHom (𝟙 _) β ≫
        CochainComplex.ιMapBifunctor K Q (MonoidalCategory.curriedTensor E) p' n' t h' := by
  have ht := tensor_degree_transport K Q p p' n n' t hp hn h h' β
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc, hs]
  simp only [Linear.smul_comp]
  rw [ht, neg_one_zpow_eq_ite]
  by_cases he : Even p
  · simp only [ite_eq_left he, one_smul, one_mul]
  · simp only [ite_eq_right he, Units.smul_def, Units.val_neg, Units.val_one,
      neg_one_mul, map_neg, neg_smul, one_smul]

section Scalars

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (O : Sheaf J CommRingCat.{u})

private abbrev scalarModules :=
  SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)

set_option hygiene false in
local notation "E" => scalarModules O
set_option hygiene false in
local notation "S" => RingCat.sectionsSubring (O.obj ⋙ forget₂ CommRingCat RingCat)

attribute [local instance] SheafOfModules.monoidalCategory

@[instance_reducible]
private noncomputable def coefficientLinear : Linear S E :=
  SheafOfModules.homLinear O.obj
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).property

private theorem scalar_eq_smul (b : S) :
    (ringedKoszulScalar O ⟨b.val, b.property⟩).asHom =
      ringedKoszulCoefficientSMul O (RingHom.id S) b
        (𝟙 (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  refine ModuleCat.hom_ext (LinearMap.ext fun (x : O.obj.obj U) ↦ ?_)
  let c : O.obj.obj U := b.val U
  change x * c = c * x
  exact mul_comm _ _

private theorem tensorLeft_smul (M N P : E) (f : N ⟶ P) (b : S) :
    letI := SheafOfModules.monoidalCategory O
    (MonoidalCategory.tensorLeft M).map
        (ringedKoszulCoefficientSMul O (RingHom.id S) b f) =
      ringedKoszulCoefficientSMul O (RingHom.id S) b
        ((MonoidalCategory.tensorLeft M).map f) := by
  let := SheafOfModules.monoidalCategory O
  let := coefficientLinear O
  change (MonoidalCategory.tensorLeft M).map (b • f) =
    b • (MonoidalCategory.tensorLeft M).map f
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).obj)
  let pure (X Y : E) := adj.unit.app (X.val ⊗ Y.val) ≫
    (SheafOfModules.tensorObjIsoSheafification X Y).inv.val
  have natural {X Y : E} (g : X ⟶ Y) :
      pure M X ≫ ((MonoidalCategory.tensorLeft M).map g).val =
        (M.val ◁ g.val) ≫ pure M Y := by
    have h : (SheafOfModules.tensorObjIsoSheafification M X).inv ≫
        (MonoidalCategory.tensorLeft M).map g =
        (PresheafOfModules.sheafification (𝟙 _)).map (M.val ◁ g.val) ≫
          (SheafOfModules.tensorObjIsoSheafification M Y).inv := by
      rw [Iso.inv_comp_eq, ← Category.assoc,
        ← SheafOfModules.whiskerLeft_tensorObjIsoSheafification_hom (R := O),
        Category.assoc, Iso.hom_inv_id, Category.comp_id]
      rfl
    have hv := congrArg SheafOfModules.Hom.val h
    change (SheafOfModules.tensorObjIsoSheafification M X).inv.val ≫
        ((MonoidalCategory.tensorLeft M).map g).val =
      ((PresheafOfModules.sheafification (𝟙 _)).map (M.val ◁ g.val)).val ≫
        (SheafOfModules.tensorObjIsoSheafification M Y).inv.val at hv
    have hn := adj.unit.naturality (M.val ◁ g.val)
    change (M.val ◁ g.val) ≫ adj.unit.app (M.val ⊗ Y.val) =
      adj.unit.app (M.val ⊗ X.val) ≫
        ((PresheafOfModules.sheafification (𝟙 _)).map (M.val ◁ g.val)).val at hn
    dsimp only [pure]
    erw [Category.assoc, hv, ← Category.assoc, ← hn]
    rfl
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification M N).inv).mp
  apply (adj.homEquiv (M.val ⊗ N.val) (M ⊗ P)).injective
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  have h₁ := congrArg (fun h ↦ (h.app U) (x ⊗ₜ[O.obj.obj U] y)) (natural (b • f))
  have h₂ := congrArg (fun h ↦ (h.app U) (x ⊗ₜ[O.obj.obj U] y)) (natural f)
  change ((MonoidalCategory.tensorLeft M).map (b • f)).val.app U
      ((pure M N).app U (x ⊗ₜ[O.obj.obj U] y)) =
    b.val U • ((MonoidalCategory.tensorLeft M).map f).val.app U
      ((pure M N).app U (x ⊗ₜ[O.obj.obj U] y))
  change ((MonoidalCategory.tensorLeft M).map (b • f)).val.app U _ =
    (pure M P).app U (x ⊗ₜ[O.obj.obj U] (b • f).val.app U y) at h₁
  change ((MonoidalCategory.tensorLeft M).map f).val.app U _ =
    (pure M P).app U (x ⊗ₜ[O.obj.obj U] f.val.app U y) at h₂
  apply h₁.trans
  apply Eq.trans _ (congrArg (fun z ↦ b.val U • z) h₂.symm)
  let c : O.obj.obj U := b.val U
  change (pure M P).app U (x ⊗ₜ[O.obj.obj U] (c • f.val.app U y)) =
    c • (pure M P).app U (x ⊗ₜ[O.obj.obj U] f.val.app U y)
  have ht : x ⊗ₜ[O.obj.obj U] (c • f.val.app U y) =
      c • (x ⊗ₜ[O.obj.obj U] f.val.app U y) :=
    TensorProduct.tmul_smul c x (f.val.app U y)
  exact (congrArg (fun z ↦ (pure M P).app U z) ht).trans
    (((pure M P).app U).hom.map_smul
      (show ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).obj.obj U from c) _)

private theorem unitor_tensor_scalar (M : E) (b : S) :
    letI := SheafOfModules.monoidalCategory O
    (MonoidalCategory.rightUnitor M).inv ≫
        (MonoidalCategory.tensorLeft M).map
          (ringedKoszulScalar O ⟨b.val, b.property⟩).asHom =
      ringedKoszulCoefficientSMul O (RingHom.id S) b
        (MonoidalCategory.rightUnitor M).inv := by
  let := SheafOfModules.monoidalCategory O
  let := coefficientLinear O
  rw [scalar_eq_smul, tensorLeft_smul]
  change (MonoidalCategory.rightUnitor M).inv ≫
      (b • (MonoidalCategory.tensorLeft M).map (𝟙 _)) =
    b • (MonoidalCategory.rightUnitor M).inv
  rw [Functor.map_id, Linear.comp_smul]
  exact congrArg (fun f ↦ b • f) (Category.comp_id (MonoidalCategory.rightUnitor M).inv)

private noncomputable def scalarHom : S →+* End (SheafOfModules.unit
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) where
  toFun b := ringedKoszulScalar O ⟨b.val, b.property⟩
  map_one' := by
    apply End.ext
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    refine ModuleCat.hom_ext (LinearMap.ext fun (x : O.obj.obj U) ↦ ?_)
    change x * 1 = x
    exact mul_one x
  map_mul' b b' := by
    apply End.ext
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    refine ModuleCat.hom_ext (LinearMap.ext fun (x : O.obj.obj U) ↦ ?_)
    let c : O.obj.obj U := b.val U
    let c' : O.obj.obj U := b'.val U
    change x * (c * c') = (x * c') * c
    ring
  map_zero' := by
    apply End.ext
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    refine ModuleCat.hom_ext (LinearMap.ext fun (x : O.obj.obj U) ↦ ?_)
    change x * 0 = 0
    exact mul_zero x
  map_add' b b' := by
    apply End.ext
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    refine ModuleCat.hom_ext (LinearMap.ext fun (x : O.obj.obj U) ↦ ?_)
    let c : O.obj.obj U := b.val U
    let c' : O.obj.obj U := b'.val U
    change x * (c + c') = x * c + x * c'
    exact mul_add x c c'

/-- The signed power of a rank-one scalar is the rank-one scalar of the signed power. -/
private theorem signed_power_scalar {A : Type z} [CommRing A] (ρ : A →+* S) (b : A)
    (c m : ℕ) :
    (-1 : ℤ) ^ c • (ringedKoszulScalar O ⟨(ρ b).val, (ρ b).property⟩) ^ (m + 1) =
      ringedKoszulScalar O ⟨(ρ ((-1 : A) ^ c * b ^ (m + 1))).val,
        (ρ ((-1 : A) ^ c * b ^ (m + 1))).property⟩ := by
  change (-1 : ℤ) ^ c • (scalarHom O (ρ b)) ^ (m + 1) =
    scalarHom O (ρ ((-1 : A) ^ c * b ^ (m + 1)))
  rw [zsmul_eq_mul]
  simp only [map_mul, map_pow, map_neg, map_one, Int.cast_pow, Int.cast_neg, Int.cast_one]

-- The transport compares the canonical sheaf tensor and Hom scalar instances.
private theorem signed_scalar_degree_transport
    {A : Type z} [CommRing A]
    (ρ : A →+* S) (b : A) (K Q : CochainComplex E ℤ)
    (p p' n n' t : ℤ) (hp : p = p') (hn : n = n')
    (h : p + n = t) (h' : p' + n' = t) :
    letI : IsGrothendieckAbelian.{u} E := SheafOfModules.isGrothendieckAbelian _
    letI : HasColimitsOfSize.{u, u} E := IsGrothendieckAbelian.hasColimits E
    letI : HasCountableCoproducts E := inferInstance
    letI := SheafOfModules.monoidalCategory O
    letI := SheafOfModules.symmetricCategory O
    letI := Classical.choice (SheafOfModules.tensorClosed O).1
    letI := Classical.choice (SheafOfModules.tensorClosed O).2.1
    ∀ (β : MonoidalCategory.tensorUnit E ⟶ Q.X n'),
    ((-1 : ℤˣ) ^ p) • (MonoidalCategory.rightUnitor (K.X p)).inv ≫
        (MonoidalCategory.tensorLeft (K.X p)).map
          ((ringedKoszulScalar O ⟨(ρ b).val, (ρ b).property⟩).asHom ≫
            β ≫ eqToHom (congrArg Q.X hn.symm)) ≫
        CochainComplex.ιMapBifunctor K Q (MonoidalCategory.curriedTensor E) p n t h =
      ringedKoszulCoefficientSMul O ρ ((if Even p then 1 else -1) * b)
          (K.XIsoOfEq hp).hom ≫ (MonoidalCategory.rightUnitor (K.X p')).inv ≫
        MonoidalCategory.tensorHom (𝟙 _) β ≫
        CochainComplex.ιMapBifunctor K Q (MonoidalCategory.curriedTensor E) p' n' t h' := by
  let : IsGrothendieckAbelian.{u} E := SheafOfModules.isGrothendieckAbelian _
  let : HasColimitsOfSize.{u, u} E := IsGrothendieckAbelian.hasColimits E
  let : HasCountableCoproducts E := inferInstance
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := Classical.choice (SheafOfModules.tensorClosed O).1
  let := Classical.choice (SheafOfModules.tensorClosed O).2.1
  let := coefficientLinear O
  intro β
  exact signed_tensor_degree_transport ρ b K Q p p' n n' t hp hn h h'
    (ringedKoszulScalar O ⟨(ρ b).val, (ρ b).property⟩).asHom
    (unitor_tensor_scalar O (K.X p) (ρ b)) β

end Scalars

attribute [local irreducible] ringedNegativeKoszul ringedNegativeKoszulBasis

/-- One erased-index term after the ordered basis differential is tensorized.

Source: Stacks Project, algebraization.tex, Tag 0A0E.

Proof in words: rewrite the tensor-left map of a composite as the composite of
its tensor-left maps. On presheaf pure tensors, the signed (m+1)-st power of
multiplication by a_i acts by rho((-1)^c a_i^(m+1)), where c counts preceding
selected indices. Tensor balancing moves this scalar onto the coefficient
module; the equality descends to sheafification. Naturality of the right unitor
moves the equality
transport on the coefficient degree across the tensor inclusion. The global
section scalar action is the recorded `ringedKoszulCoefficientSMul`; its scalar
is the total-tensor sign times the earlier-index sign and the power of `a i`.
The two degree equalities identify the equality transports by proof
irrelevance. This statement is one summand of the finite sum and does not
assert the differential formula for the full subset.
(auxiliary; not a blueprint node).
-/
theorem ringedNegativeKoszulSummand_D₂_term
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) {A : Type z} [CommRing A]
    (ρ : A →+* RingCat.sectionsSubring (O.obj ⋙ forget₂ CommRingCat RingCat))
    (r : ℕ) (a : Fin (r + 1) → A) (m : ℕ) (K : ringedSiteComplex O) (q : ℤ)
    (I : Finset (Fin (r + 1))) (i : Fin (r + 1)) (hi : i ∈ I)
    (hdeg : q + (I.card : ℤ) = (q + 1) + ((I.erase i).card : ℤ))
    (hsrc : -(I.card : ℤ) + 1 = -((I.erase i).card : ℤ)) :
    letI : IsGrothendieckAbelian.{u} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
      SheafOfModules.isGrothendieckAbelian _
    letI := SheafOfModules.monoidalCategory O
    letI := SheafOfModules.symmetricCategory O
    letI := Classical.choice (SheafOfModules.tensorClosed O).1
    letI := Classical.choice (SheafOfModules.tensorClosed O).2.1
    let Q := ringedNegativeKoszul O (r + 1)
      (fun j ↦ ⟨(ρ (a j)).val, (ρ (a j)).property⟩) m
    ((-1 : ℤˣ) ^ (q + (I.card : ℤ))) •
        (MonoidalCategory.rightUnitor (K.X (q + I.card))).inv ≫
      (MonoidalCategory.tensorLeft (K.X (q + I.card))).map
        (((-1 : ℤ) ^ (I.filter (fun j ↦ j < i)).card •
            (ringedKoszulScalar O ⟨(ρ (a i)).val, (ρ (a i)).property⟩) ^ (m + 1)).asHom ≫
          ringedNegativeKoszulBasis O
            (r + 1) (fun j ↦ ⟨(ρ (a j)).val, (ρ (a j)).property⟩) m
            (I.erase i) (-((I.erase i).card : ℤ)) ≫
          eqToHom (congrArg Q.X hsrc.symm)) ≫
      CochainComplex.ιMapBifunctor K Q (MonoidalCategory.curriedTensor _)
        (q + I.card) (-(I.card : ℤ) + 1) (q + 1) (by omega) =
      ringedKoszulCoefficientSMul O ρ
          ((if Even (q + (I.card : ℤ)) then (1 : A) else -1) *
            (-1 : A) ^ (I.filter (fun j ↦ j < i)).card * a i ^ (m + 1))
        (K.XIsoOfEq hdeg).hom ≫
        (MonoidalCategory.rightUnitor (K.X (q + 1 + (I.erase i).card))).inv ≫
        (MonoidalCategory.tensorHom (𝟙 _)
          (ringedNegativeKoszulBasis O
            (r + 1) (fun j ↦ ⟨(ρ (a j)).val, (ρ (a j)).property⟩) m
            (I.erase i) (-((I.erase i).card : ℤ)))) ≫
        CochainComplex.ιMapBifunctor K Q (MonoidalCategory.curriedTensor _)
          (q + 1 + (I.erase i).card) (-((I.erase i).card : ℤ)) (q + 1) (by omega) := by
  have := hi
  let E := ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
  let : IsGrothendieckAbelian.{u} E := SheafOfModules.isGrothendieckAbelian _
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := Classical.choice (SheafOfModules.tensorClosed O).1
  let := Classical.choice (SheafOfModules.tensorClosed O).2.1
  rw [signed_power_scalar O ρ (a i) (I.filter (fun j ↦ j < i)).card m]
  simpa only [mul_assoc] using signed_scalar_degree_transport O ρ
    ((-1 : A) ^ (I.filter (fun j ↦ j < i)).card * a i ^ (m + 1)) K
    (ringedNegativeKoszul O (r + 1)
      (fun j ↦ ⟨(ρ (a j)).val, (ρ (a j)).property⟩) m)
    (q + I.card) (q + 1 + (I.erase i).card)
    (-(I.card : ℤ) + 1) (-((I.erase i).card : ℤ)) (q + 1)
    hdeg hsrc (by omega) (by omega)
    (ringedNegativeKoszulBasis O (r + 1)
      (fun j ↦ ⟨(ρ (a j)).val, (ρ (a j)).property⟩) m
      (I.erase i) (-((I.erase i).card : ℤ)))

end CategoryTheory
