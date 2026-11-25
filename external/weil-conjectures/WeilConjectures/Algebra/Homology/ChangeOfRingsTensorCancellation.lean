/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlat

/-! # Cancellation of extension of scalars in sheaf tensor products

Source: Stacks Project, Modules on Sites, Tag 05V4, displayed tensor identity.
-/

@[expose] public section

universe u v

open CategoryTheory MonoidalCategory
open scoped ChangeOfRings

namespace SheafOfModules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 512

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  {R S : Sheaf J CommRingCat.{max u v}}

set_option hygiene false in
local notation "𝓡" E =>
  (sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj E
set_option hygiene false in
local notation "𝓻" a =>
  (sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).map a

private noncomputable def cancellationChangeMap (α : R ⟶ S)
    {N N' : SheafOfModules.{max u v} (𝓡 R)} (g : N ⟶ N') :
    changeOfRingsPresheaf α N ⟶ changeOfRingsPresheaf α N' where
  app W := (ModuleCat.extendScalars (α.hom.app W).hom).map (g.val.app W)
  naturality := changeOfRingsHom_naturality α N g

private noncomputable def cancellationApp (α : R ⟶ S)
    (M : SheafOfModules.{max u v} (𝓡 S)) (N : SheafOfModules.{max u v} (𝓡 R))
    (W : Cᵒᵖ) :
    ((PresheafOfModules.restrictScalars (𝓻 α).hom).obj
      (M.val ⊗ changeOfRingsPresheaf α N)).obj W ≅
        (((restrictScalars (𝓻 α)).obj M).val ⊗ N.val).obj W := by
  let A := R.obj.obj W
  let B := S.obj.obj W
  let ρ := (α.hom.app W).hom
  let : Algebra A B := ρ.toAlgebra
  let : Module A (M.val.obj W) := Module.compHom (M.val.obj W) ρ
  let : IsScalarTower A B (M.val.obj W) :=
    IsScalarTower.of_algebraMap_smul (fun r m ↦ rfl)
  exact ((TensorProduct.AlgebraTensorModule.cancelBaseChange A B B
    (M.val.obj W) (N.val.obj W)).restrictScalars A).toModuleIso

private theorem cancellationApp_tmul (α : R ⟶ S)
    (M : SheafOfModules.{max u v} (𝓡 S)) (N : SheafOfModules.{max u v} (𝓡 R))
    (W : Cᵒᵖ) (m : M.val.obj W) (s : S.obj.obj W) (n : N.val.obj W) :
    (cancellationApp α M N W).hom
        (m ⊗ₜ[S.obj.obj W] (s ⊗ₜ[R.obj.obj W,(α.hom.app W).hom] n)) =
      (show ((restrictScalars (𝓻 α)).obj M).val.obj W from s • m)
        ⊗ₜ[R.obj.obj W] n := by
  rfl

private noncomputable def cancellationPresheafIso (α : R ⟶ S)
    (M : SheafOfModules.{max u v} (𝓡 S)) (N : SheafOfModules.{max u v} (𝓡 R)) :
    (PresheafOfModules.restrictScalars (𝓻 α).hom).obj
      (M.val ⊗ changeOfRingsPresheaf α N) ≅
        ((restrictScalars (𝓻 α)).obj M).val ⊗ N.val :=
  PresheafOfModules.isoMk (cancellationApp α M N) (by
    intro U V i
    ext t
    induction t using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul m z =>
      induction z using TensorProduct.inductionOn with
      | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
      | tmul s n =>
        change (cancellationApp α M N V).hom
            (show (M.val ⊗ changeOfRingsPresheaf α N).obj V from
              (M.val ⊗ changeOfRingsPresheaf α N).map i
                (m ⊗ₜ[S.obj.obj U] (s ⊗ₜ[R.obj.obj U,(α.hom.app U).hom] n))) =
          ((((restrictScalars (𝓻 α)).obj M).val ⊗ N.val).map i)
            ((cancellationApp α M N U).hom
              (m ⊗ₜ[S.obj.obj U] (s ⊗ₜ[R.obj.obj U,(α.hom.app U).hom] n)))
        erw [PresheafOfModules.Monoidal.tensorObj_map_tmul]
        erw [Classical.choose_spec (exists_changeOfRingsMap α N i)]
        refine (cancellationApp_tmul α M N V (M.val.map i m) (S.obj.map i s)
          (N.val.map i n)).trans ?_
        erw [cancellationApp_tmul α M N U m s n]
        erw [PresheafOfModules.Monoidal.tensorObj_map_tmul, M.val.map_smul]
        rfl)

private theorem cancellationPresheafIso_naturality (α : R ⟶ S)
    {M M' : SheafOfModules.{max u v} (𝓡 S)}
    {N N' : SheafOfModules.{max u v} (𝓡 R)} (f : M ⟶ M') (g : N ⟶ N') :
    (PresheafOfModules.restrictScalars (𝓻 α).hom).map
        (f.val ⊗ₘ cancellationChangeMap α g) ≫
      (cancellationPresheafIso α M' N').hom =
    (cancellationPresheafIso α M N).hom ≫
      (((restrictScalars (𝓻 α)).map f).val ⊗ₘ g.val) := by
  ext W t
  induction t using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul m z =>
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
    | tmul s n =>
      change S.obj.obj W at s
      change (cancellationApp α M' N' W).hom
          (f.val.app W m ⊗ₜ[S.obj.obj W]
            (s ⊗ₜ[R.obj.obj W,(α.hom.app W).hom] g.val.app W n)) =
        (show ((restrictScalars (𝓻 α)).obj M').val.obj W from
          f.val.app W (s • m)) ⊗ₜ[R.obj.obj W] g.val.app W n
      rw [cancellationApp_tmul, map_smul]

attribute [local irreducible] cancellationApp cancellationPresheafIso

private noncomputable def cancellationRestrictSheafifyHom
    {A B : Sheaf J RingCat.{max u v}} (α : A ⟶ B)
    (P : PresheafOfModules.{max u v} B.obj) :
    (PresheafOfModules.sheafification (𝟙 A.obj)).obj
      ((PresheafOfModules.restrictScalars α.hom).obj P) ⟶
    (restrictScalars α).obj
      ((PresheafOfModules.sheafification (𝟙 B.obj)).obj P) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 A.obj)).symm
    ((PresheafOfModules.restrictScalars α.hom).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 B.obj)).unit.app P))

omit [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})] in
private theorem cancellationRestrictSheafifyHom_toSheaf
    {A B : Sheaf J RingCat.{max u v}} (α : A ⟶ B)
    (P : PresheafOfModules.{max u v} B.obj) :
    (toSheaf A).map (cancellationRestrictSheafifyHom α P) =
      𝟙 ((PresheafOfModules.toPresheaf B.obj ⋙
        presheafToSheaf J AddCommGrpCat).obj P) := by
  rw [cancellationRestrictSheafifyHom,
    PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm]
  apply ((CategoryTheory.sheafificationAdjunction J AddCommGrpCat).homEquiv _ _).injective
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  rfl

private noncomputable def cancellationRestrictSheafifyIso
    {A B : Sheaf J RingCat.{max u v}} (α : A ⟶ B)
    (P : PresheafOfModules.{max u v} B.obj) :
    (PresheafOfModules.sheafification (𝟙 A.obj)).obj
      ((PresheafOfModules.restrictScalars α.hom).obj P) ≅
    (restrictScalars α).obj
      ((PresheafOfModules.sheafification (𝟙 B.obj)).obj P) := by
  have : IsIso (cancellationRestrictSheafifyHom α P) := by
    have : IsIso ((toSheaf A).map (cancellationRestrictSheafifyHom α P)) := by
      rw [cancellationRestrictSheafifyHom_toSheaf]
      exact IsIso.id _
    exact isIso_of_reflects_iso _ (toSheaf A)
  exact asIso (cancellationRestrictSheafifyHom α P)

omit [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})] in
private theorem cancellationRestrictSheafifyIso_naturality
    {A B : Sheaf J RingCat.{max u v}} (α : A ⟶ B)
    {P Q : PresheafOfModules.{max u v} B.obj} (f : P ⟶ Q) :
    (PresheafOfModules.sheafification (𝟙 A.obj)).map
        ((PresheafOfModules.restrictScalars α.hom).map f) ≫
      (cancellationRestrictSheafifyIso α Q).hom =
    (cancellationRestrictSheafifyIso α P).hom ≫
      (restrictScalars α).map
        ((PresheafOfModules.sheafification (𝟙 B.obj)).map f) := by
  apply (toSheaf A).map_injective
  simp only [Functor.map_comp]
  change _ ≫ (toSheaf A).map (cancellationRestrictSheafifyHom α Q) =
    (toSheaf A).map (cancellationRestrictSheafifyHom α P) ≫ _
  rw [cancellationRestrictSheafifyHom_toSheaf, cancellationRestrictSheafifyHom_toSheaf]
  change (presheafToSheaf J AddCommGrpCat).map
      ((PresheafOfModules.toPresheaf B.obj).map f) ≫ 𝟙 _ =
    𝟙 _ ≫ (presheafToSheaf J AddCommGrpCat).map
      ((PresheafOfModules.toPresheaf B.obj).map f)
  simp only [Category.comp_id, Category.id_comp]

private theorem cancellationTensorIso_naturality
    (A : Sheaf J CommRingCat.{max u v})
    {M M' N N' : SheafOfModules.{max u v} (𝓡 A)} (f : M ⟶ M') (g : N ⟶ N') :
    letI := monoidalCategory A
    (f ⊗ₘ g) ≫ (tensorObjIsoSheafification M' N').hom =
      (tensorObjIsoSheafification M N).hom ≫
        (PresheafOfModules.sheafification (𝟙 (𝓡 A).obj)).map (f.val ⊗ₘ g.val) := by
  let := monoidalCategory A
  let a := PresheafOfModules.sheafification (𝟙 (𝓡 A).obj)
  let ε := asIso (PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 A).obj)).counit
  have hf : f ≫ (ε.app M').inv = (ε.app M).inv ≫ a.map f.val :=
    ε.inv.naturality f
  have hg : g ≫ (ε.app N').inv = (ε.app N).inv ≫ a.map g.val :=
    ε.inv.naturality g
  change (f ⊗ₘ g) ≫ ((ε.app M').inv ⊗ₘ (ε.app N').inv) ≫
      Functor.LaxMonoidal.μ a M'.val N'.val =
    ((ε.app M).inv ⊗ₘ (ε.app N).inv) ≫
      Functor.LaxMonoidal.μ a M.val N.val ≫ a.map (f.val ⊗ₘ g.val)
  rw [← Functor.LaxMonoidal.μ_natural]
  simp only [← Category.assoc, tensorHom_comp_tensorHom, hf, hg]

attribute [local irreducible] cancellationRestrictSheafifyHom cancellationRestrictSheafifyIso

private noncomputable def cancellationTensorSheafifyIso (α : R ⟶ S)
    (M : SheafOfModules.{max u v} (𝓡 S)) (N : SheafOfModules.{max u v} (𝓡 R)) :
    (PresheafOfModules.sheafification (𝟙 (𝓡 S).obj)).obj
      (M.val ⊗ changeOfRingsPresheaf α N) ≅
        (monoidalCategory S).tensorObj M (changeOfRings α N) := by
  let := monoidalCategory S
  let a := PresheafOfModules.sheafification (𝟙 (𝓡 S).obj)
  let η := (PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 S).obj)).unit.app
    (changeOfRingsPresheaf α N)
  let W := J.W.inverseImage (PresheafOfModules.toPresheaf (𝓡 S).obj)
  have hη : W η := by
    dsimp only [W]
    rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
      (𝟙 (𝓡 S).obj)]
    change IsIso (a.map η)
    infer_instance
  have ht := W.whiskerLeft_mem M.val η hη
  have : IsIso (a.map (M.val ◁ η)) := by
    dsimp only [W] at ht
    rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
      (𝟙 (𝓡 S).obj)] at ht
    exact ht
  exact asIso (a.map (M.val ◁ η)) ≪≫
    (tensorObjIsoSheafification M (changeOfRings α N)).symm

private theorem cancellationTensorSheafifyIso_naturality (α : R ⟶ S)
    {M M' : SheafOfModules.{max u v} (𝓡 S)}
    {N N' : SheafOfModules.{max u v} (𝓡 R)} (f : M ⟶ M') (g : N ⟶ N') :
    (PresheafOfModules.sheafification (𝟙 (𝓡 S).obj)).map
        (f.val ⊗ₘ cancellationChangeMap α g) ≫
      (cancellationTensorSheafifyIso α M' N').hom =
    (cancellationTensorSheafifyIso α M N).hom ≫
      (monoidalCategory S).tensorHom f (changeOfRingsHom α N g) := by
  let := monoidalCategory S
  let a := PresheafOfModules.sheafification (𝟙 (𝓡 S).obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 S).obj)
  apply (cancel_mono (tensorObjIsoSheafification M' (changeOfRings α N')).hom).mp
  dsimp only [cancellationTensorSheafifyIso, Iso.trans_hom, Iso.symm_hom, asIso_hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [cancellationTensorIso_naturality S f (changeOfRingsHom α N g)]
  simp only [Iso.inv_hom_id_assoc]
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  change (f.val ⊗ₘ cancellationChangeMap α g) ≫
      (M'.val ◁ adj.unit.app (changeOfRingsPresheaf α N')) =
    (M.val ◁ adj.unit.app (changeOfRingsPresheaf α N)) ≫
      (f.val ⊗ₘ (a.map (cancellationChangeMap α g)).val)
  simp only [← id_tensorHom, tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
  congr 1
  exact adj.unit.naturality (cancellationChangeMap α g)

attribute [local irreducible] cancellationTensorSheafifyIso

private noncomputable def cancellationSheafIso (α : R ⟶ S)
    (M : SheafOfModules.{max u v} (𝓡 S)) (N : SheafOfModules.{max u v} (𝓡 R)) :
    (restrictScalars (𝓻 α)).obj
      ((monoidalCategory S).tensorObj M (changeOfRings α N)) ≅
    (monoidalCategory R).tensorObj ((restrictScalars (𝓻 α)).obj M) N :=
  ((restrictScalars (𝓻 α)).mapIso (cancellationTensorSheafifyIso α M N)).symm ≪≫
    (cancellationRestrictSheafifyIso (𝓻 α) (M.val ⊗ changeOfRingsPresheaf α N)).symm ≪≫
    (PresheafOfModules.sheafification (𝟙 (𝓡 R).obj)).mapIso
      (cancellationPresheafIso α M N) ≪≫
    (tensorObjIsoSheafification ((restrictScalars (𝓻 α)).obj M) N).symm

private theorem cancellation_inverse_naturality
    {D : Type*} [Category* D] {A B A' B' : D} (i : A ≅ B) (j : A' ≅ B')
    (f : A ⟶ A') (g : B ⟶ B') (h : f ≫ j.hom = i.hom ≫ g) :
    g ≫ j.inv = i.inv ≫ f := by
  apply (cancel_epi i.hom).mp
  rw [← Category.assoc, ← h]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]

/-- Restriction cancels the extension of the second tensor factor, naturally in both factors.
Source: Stacks Project, Modules on Sites, Tag 05V4, displayed tensor identity.

Proof: before sheafification use the balanced linear equivalence
`m ⊗ (s ⊗ n) ↦ (s • m) ⊗ n`, inverse `m ⊗ n ↦ m ⊗ (1 ⊗ n)`.
Tensor induction proves compatibility with restrictions and with maps of both factors.
Restriction of scalars commutes with sheafification because the underlying abelian
sheafification is unchanged. Tensoring the extension-presheaf unit becomes invertible
under sheafification by monoidal localization. Compose these identifications with the
sheaf tensor comparison. All comparisons are natural, hence so is their composite.
Zero modules and zero rings satisfy the same formulas; no flatness assumption is used.
(auxiliary; not a blueprint node) -/
theorem exists_changeOfRings_tensorCancellation (α : R ⟶ S) :
    ∃ e : ∀ (M : SheafOfModules.{max u v} (𝓡 S))
        (N : SheafOfModules.{max u v} (𝓡 R)),
      (restrictScalars (𝓻 α)).obj
        ((monoidalCategory S).tensorObj M (changeOfRings α N)) ≅
      (monoidalCategory R).tensorObj ((restrictScalars (𝓻 α)).obj M) N,
      ∀ {M M' : SheafOfModules.{max u v} (𝓡 S)}
        {N N' : SheafOfModules.{max u v} (𝓡 R)} (f : M ⟶ M') (g : N ⟶ N'),
        (restrictScalars (𝓻 α)).map
            ((monoidalCategory S).tensorHom f (changeOfRingsHom α N g)) ≫
          (e M' N').hom =
        (e M N).hom ≫
          (monoidalCategory R).tensorHom ((restrictScalars (𝓻 α)).map f) g := by
  refine ⟨cancellationSheafIso α, ?_⟩
  intro M M' N N' f g
  let U := restrictScalars (𝓻 α)
  let a := PresheafOfModules.sheafification (𝟙 (𝓡 R).obj)
  let hP := f.val ⊗ₘ cancellationChangeMap α g
  have hi := cancellation_inverse_naturality
    (cancellationTensorSheafifyIso α M N) (cancellationTensorSheafifyIso α M' N')
    _ _ (cancellationTensorSheafifyIso_naturality α f g)
  have hiU := congrArg U.map hi
  simp only [Functor.map_comp] at hiU
  have hj := cancellation_inverse_naturality
    (cancellationRestrictSheafifyIso (𝓻 α) (M.val ⊗ changeOfRingsPresheaf α N))
    (cancellationRestrictSheafifyIso (𝓻 α) (M'.val ⊗ changeOfRingsPresheaf α N'))
    _ _ (cancellationRestrictSheafifyIso_naturality (𝓻 α) hP)
  have hk := congrArg a.map (cancellationPresheafIso_naturality α f g)
  simp only [Functor.map_comp] at hk
  have ht := cancellation_inverse_naturality
    (tensorObjIsoSheafification (U.obj M) N)
    (tensorObjIsoSheafification (U.obj M') N')
    _ _ (cancellationTensorIso_naturality R (U.map f) g)
  dsimp only [cancellationSheafIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.mapIso_inv]
  simp only [Category.assoc]
  rw [reassoc_of% hiU, reassoc_of% hj, reassoc_of% hk, ht]

end SheafOfModules
