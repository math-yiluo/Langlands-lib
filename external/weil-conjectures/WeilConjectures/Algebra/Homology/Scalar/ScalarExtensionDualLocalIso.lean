/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionDualEvaluation
import Mathlib.CategoryTheory.Sites.LocalProperties

/-!
# Scalar extension of a locally free rank-one module

Source: Stacks Project, Tags 03EK, 03EM, 04TT.
(blueprint: lem-sp-scalar-extension-dual-local-iso).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

universe uC vC u m
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace SheafOfModules

attribute [local irreducible] scalarExtensionDualMap

section SliceExt

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

private theorem extension_over_hom_ext
    {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N : SheafOfModules.{m} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u m}]
    [HasWeakSheafify J AddCommGrpCat.{max u m}] (U : C)
    {H : SheafOfModules.{max u m}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).over U)}
    (f g : (changeOfRingsOfUniverses α N).over U ⟶ H)
    (h : ∀ (W : (Over U)ᵒᵖ) (s : S.obj.obj (op W.unop.left))
      (x : N.val.obj (op W.unop.left)),
      f.val.app W (scalarExtensionSection α N (op W.unop.left) s x) =
        g.val.app W (scalarExtensionSection α N (op W.unop.left) s x)) : f = g := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  let η := (PresheafOfModules.restrictOver S.obj U).map
    (scalarSheafificationUnit (changeOfRingsPresheafOfUniverses α N))
  have : PresheafOfModules.IsLocallySurjective (J.over U) η :=
    Presheaf.isLocallySurjective_whisker (J.over U) J (Over.forget U)
      ((PresheafOfModules.toPresheaf _).map
        (scalarSheafificationUnit (changeOfRingsPresheafOfUniverses α N)))
  apply H.isSheaf.isSeparated _ _
    (Presheaf.imageSieve_mem (J.over U) ((PresheafOfModules.toPresheaf _).map η) z)
  intro V i hi
  obtain ⟨t, ht⟩ := hi
  change η.app (op V) t = (changeOfRingsOfUniverses α N).val.map i.left.op z at ht
  change H.val.map i.op (f.val.app W z) = H.val.map i.op (g.val.app W z)
  have hp := PresheafOfModules.naturality_apply f.val i.op z
  have hq := PresheafOfModules.naturality_apply g.val i.op z
  refine hp.symm.trans (Eq.trans ?_ hq)
  change f.val.app (op V) ((changeOfRingsOfUniverses α N).val.map i.left.op z) =
    g.val.app (op V) ((changeOfRingsOfUniverses α N).val.map i.left.op z)
  rw [← ht]
  clear ht
  induction t using TensorProduct.inductionOn with
  | add t t' ht ht' =>
    erw [(η.app (op V)).hom.map_add, (f.val.app (op V)).hom.map_add,
      (g.val.app (op V)).hom.map_add, ht, ht']
  | tmul s x => exact h (op V) s x

end SliceExt

section LocalBasis

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
  (N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))

set_option hygiene false in
local notation:max "𝒪" R:arg => unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)

private noncomputable def localDual {U : C}
    (e : N.over U ≅ (𝒪 R).over U) : (homObj N (𝒪 R)).val.obj (op U) where
  app W := e.hom.val.app W
  naturality i := e.hom.val.naturality i

private noncomputable def localBasis {U : C}
    (e : N.over U ≅ (𝒪 R).over U) (W : (Over U)ᵒᵖ) :
    N.val.obj (op W.unop.left) := e.inv.val.app W (1 : R.obj.obj (op W.unop.left))

private theorem localBasis_natural {U : C}
    (e : N.over U ≅ (𝒪 R).over U) {W V : (Over U)ᵒᵖ} (i : W ⟶ V) :
    N.val.map i.unop.left.op (localBasis N e W) = localBasis N e V := by
  have h := PresheafOfModules.naturality_apply e.inv.val i (1 : R.obj.obj (op W.unop.left))
  change e.inv.val.app V (R.obj.map i.unop.left.op 1) =
    N.val.map i.unop.left.op (localBasis N e W) at h
  rw [map_one] at h
  exact h.symm

private theorem localDual_basis {U : C}
    (e : N.over U ≅ (𝒪 R).over U) (W : (Over U)ᵒᵖ) :
    (localDual N e).app W (localBasis N e W) = (1 : R.obj.obj (op W.unop.left)) := by
  exact congrArg (fun f ↦ f.val.app W (1 : R.obj.obj (op W.unop.left))) e.inv_hom_id

private noncomputable local instance {U : C} (W : (Over U)ᵒᵖ) :
    SMul (((PresheafOfModules.restrictOver R.obj U).obj (𝒪 R).val).obj W)
      (N.val.obj (op W.unop.left)) :=
  inferInstanceAs (SMul (R.obj.obj (op W.unop.left)) (N.val.obj (op W.unop.left)))

private theorem localBasis_coordinates {U : C}
    (e : N.over U ≅ (𝒪 R).over U) (W : (Over U)ᵒᵖ)
    (x : N.val.obj (op W.unop.left)) :
    (localDual N e).app W x • localBasis N e W = x := by
  have h := congrArg (fun f ↦ f.val.app W x) e.hom_inv_id
  have hs := (e.inv.val.app W).hom.map_smul
    (show R.obj.obj (op W.unop.left) from (localDual N e).app W x)
    (1 : R.obj.obj (op W.unop.left))
  change e.inv.val.app W
    ((show R.obj.obj (op W.unop.left) from (localDual N e).app W x) *
      (1 : R.obj.obj (op W.unop.left))) = _ at hs
  rw [mul_one] at hs
  exact hs.symm.trans h

set_option backward.isDefEq.respectTransparency false in
private noncomputable def extendedBasisMap {U : C}
    (e : N.over U ≅ (𝒪 R).over U) :
    (𝒪 S).over U ⟶ (changeOfRingsOfUniverses α N).over U where
  val :=
    { app := fun W ↦ ModuleCat.ofHom
        { toFun := fun s ↦ scalarExtensionSection α N (op W.unop.left) s (localBasis N e W)
          map_add' := by
            intro s t
            dsimp only [scalarExtensionSection]
            rw [TensorProduct.add_tmul, map_add]
          map_smul' := by
            intro s t
            change S.obj.obj (op W.unop.left) at s t
            change scalarExtensionSection α N (op W.unop.left) (s * t) _ = _
            exact (scalarExtensionSection_smul α N _ s t _).symm }
      naturality := by
        intro W V i
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro s
        change scalarExtensionSection α N (op V.unop.left)
            (S.obj.map i.unop.left.op s) (localBasis N e V) =
          (changeOfRingsOfUniverses α N).val.map i.unop.left.op
            (scalarExtensionSection α N (op W.unop.left) s (localBasis N e W))
        rw [scalarExtensionSection_naturality, localBasis_natural] }

private noncomputable def extendedCoordinateMap {U : C}
    (e : N.over U ≅ (𝒪 R).over U) :
    (changeOfRingsOfUniverses α N).over U ⟶ (𝒪 S).over U where
  val := scalarDualBaseSection α N (op U) (localDual N e)

private theorem extendedCoordinateMap_tmul {U : C}
    (e : N.over U ≅ (𝒪 R).over U) (W : (Over U)ᵒᵖ)
    (s : S.obj.obj (op W.unop.left)) (x : N.val.obj (op W.unop.left)) :
    (extendedCoordinateMap α N e).val.app W
      (scalarExtensionSection α N (op W.unop.left) s x) =
        α.hom.app (op W.unop.left) ((localDual N e).app W x) * s :=
  scalarDualBaseSection_tmul α N (op U) (localDual N e) W s x

set_option backward.isDefEq.respectTransparency false in
private noncomputable def extendedBasisIso {U : C}
    (e : N.over U ≅ (𝒪 R).over U) :
    (changeOfRingsOfUniverses α N).over U ≅ (𝒪 S).over U where
  hom := extendedCoordinateMap α N e
  inv := extendedBasisMap α N e
  hom_inv_id := by
    apply extension_over_hom_ext α N U
    intro W s x
    change scalarExtensionSection α N (op W.unop.left)
        ((extendedCoordinateMap α N e).val.app W
          (scalarExtensionSection α N (op W.unop.left) s x)) (localBasis N e W) =
      scalarExtensionSection α N (op W.unop.left) s x
    rw [extendedCoordinateMap_tmul, mul_comm, ← scalarExtensionSection_base_smul,
      localBasis_coordinates]
  inv_hom_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    change (extendedCoordinateMap α N e).val.app W
      (scalarExtensionSection α N (op W.unop.left) s (localBasis N e W)) = s
    rw [extendedCoordinateMap_tmul, localDual_basis, map_one, one_mul]

private noncomputable local instance {U : C} (W : (Over U)ᵒᵖ) :
    SMul (((PresheafOfModules.restrictOver R.obj W.unop.left).obj (𝒪 R).val).obj
        (op (Over.mk (𝟙 W.unop.left))))
      ((ModuleCat.restrictScalars
          (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj.map W.unop.hom.op).hom).obj
        ((homObj N (𝒪 R)).val.obj (op W.unop.left))) :=
  inferInstanceAs (SMul (R.obj.obj (op W.unop.left))
    ((homObj N (𝒪 R)).val.obj (op W.unop.left)))

set_option backward.isDefEq.respectTransparency false in
private theorem localDual_coordinates {U : C}
    (e : N.over U ≅ (𝒪 R).over U) (W : (Over U)ᵒᵖ)
    (φ : (homObj N (𝒪 R)).val.obj (op W.unop.left)) :
    φ = φ.app (op (Over.mk (𝟙 W.unop.left))) (localBasis N e W) •
      (homObj N (𝒪 R)).val.map W.unop.hom.op (localDual N e) := by
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  let Z : (Over U)ᵒᵖ := op (Over.mk (V.unop.hom ≫ W.unop.hom))
  have hx := localBasis_coordinates N e Z x
  have hb := localBasis_natural N e
    (show W ⟶ Z from (Over.homMk V.unop.hom).op)
  let k : Over.mk V.unop.hom ⟶ Over.mk (𝟙 W.unop.left) := Over.homMk V.unop.hom
  have hp := PresheafOfModules.naturality_apply φ k.op (localBasis N e W)
  change φ.app V (N.val.map V.unop.hom.op (localBasis N e W)) =
    R.obj.map V.unop.hom.op (φ.app (op (Over.mk (𝟙 W.unop.left)))
      (localBasis N e W)) at hp
  change N.val.map V.unop.hom.op (localBasis N e W) = localBasis N e Z at hb
  rw [hb] at hp
  change φ.app V x = R.obj.map V.unop.hom.op
    (φ.app (op (Over.mk (𝟙 W.unop.left))) (localBasis N e W)) *
      (show R.obj.obj (op V.unop.left) from (localDual N e).app Z x)
  conv_lhs => rw [← hx]
  rw [(φ.app V).hom.map_smul, hp]
  dsimp only [Functor.comp_obj, Functor.op_obj] at *
  change (show R.obj.obj (op V.unop.left) from (localDual N e).app Z x) *
      R.obj.map V.unop.hom.op
        (φ.app (op (Over.mk (𝟙 W.unop.left))) (localBasis N e W)) = _
  exact mul_comm _ _

private theorem extendedBasis_natural {U : C}
    (e : N.over U ≅ (𝒪 R).over U) {W V : (Over U)ᵒᵖ} (i : W ⟶ V) :
    (changeOfRingsOfUniverses α N).val.map i.unop.left.op
      (scalarExtensionSection α N (op W.unop.left) 1 (localBasis N e W)) =
    scalarExtensionSection α N (op V.unop.left) 1 (localBasis N e V) := by
  rw [scalarExtensionSection_naturality, map_one, localBasis_natural]

private theorem dualCoefficient_natural {U : C}
    (e : N.over U ≅ (𝒪 R).over U) {W V : (Over U)ᵒᵖ} (i : W ⟶ V)
    (φ : (homObj (changeOfRingsOfUniverses α N) (𝒪 S)).val.obj (op W.unop.left)) :
    S.obj.map i.unop.left.op
        (φ.app (op (Over.mk (𝟙 W.unop.left)))
          (scalarExtensionSection α N (op W.unop.left) 1 (localBasis N e W))) =
      (((homObj (changeOfRingsOfUniverses α N) (𝒪 S)).val.map i.unop.left.op φ).app
        (op (Over.mk (𝟙 V.unop.left))))
          (scalarExtensionSection α N (op V.unop.left) 1 (localBasis N e V)) := by
  let k : Over.mk i.unop.left ⟶ Over.mk (𝟙 W.unop.left) := Over.homMk i.unop.left
  have hp := PresheafOfModules.naturality_apply φ k.op
    (scalarExtensionSection α N (op W.unop.left) 1 (localBasis N e W))
  change φ.app (op (Over.mk i.unop.left))
      ((changeOfRingsOfUniverses α N).val.map i.unop.left.op _) = _ at hp
  rw [extendedBasis_natural α N e i] at hp
  refine hp.symm.trans ?_
  exact PresheafOfModules.restrictOver_hom_app_congr φ
    (Category.id_comp i.unop.left).symm _

section DualInverse

variable [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC u}]
  [HasWeakSheafify J AddCommGrpCat.{max uC vC u}]

set_option backward.isDefEq.respectTransparency false in
private noncomputable def localDualInverse {U : C}
    (e : N.over U ≅ (𝒪 R).over U) :
    (homObj (changeOfRingsOfUniverses α N) (𝒪 S)).over U ⟶
      (changeOfRingsOfUniverses α (homObj N (𝒪 R))).over U where
  val :=
    { app := fun W ↦ ModuleCat.ofHom
        { toFun := fun φ ↦ scalarExtensionSection α (homObj N (𝒪 R)) (op W.unop.left)
            (φ.app (op (Over.mk (𝟙 W.unop.left)))
              (scalarExtensionSection α N (op W.unop.left) 1 (localBasis N e W)))
            ((homObj N (𝒪 R)).val.map W.unop.hom.op (localDual N e))
          map_add' := by
            intro φ ψ
            change scalarExtensionSection α _ _ (_ + _) _ = _
            dsimp only [scalarExtensionSection]
            rw [TensorProduct.add_tmul, map_add]
          map_smul' := by
            intro s φ
            change scalarExtensionSection α _ _
              (S.obj.map (𝟙 W.unop.left).op s * _) _ = _
            change S.obj.obj (op W.unop.left) at s
            change scalarExtensionSection α _ _
              (S.obj.map (𝟙 (op W.unop.left)) s * _) _ = _
            erw [S.obj.map_id]
            change scalarExtensionSection α _ _ (s * _) _ = _
            exact (scalarExtensionSection_smul α _ _ s _ _).symm }
      naturality := by
        intro W V i
        ext φ
        change scalarExtensionSection α _ _ _ _ =
          (changeOfRingsOfUniverses α (homObj N (𝒪 R))).val.map i.unop.left.op
            (scalarExtensionSection α _ _ _ _)
        rw [scalarExtensionSection_naturality]
        erw [dualCoefficient_natural α N e i]
        congr 1
        change (homObj N (𝒪 R)).val.map V.unop.hom.op _ =
          (homObj N (𝒪 R)).val.map i.unop.left.op
            ((homObj N (𝒪 R)).val.map W.unop.hom.op _)
        rw [← PresheafOfModules.map_comp_apply, ← op_comp, Over.w] }

set_option backward.isDefEq.respectTransparency false in
private theorem dual_forward_inverse {U : C}
    (e : N.over U ≅ (𝒪 R).over U) :
    (scalarExtensionDualMap α N).over U ≫ localDualInverse α N e = 𝟙 _ := by
  apply extension_over_hom_ext α (homObj N (𝒪 R)) U
  intro W s φ
  change scalarExtensionSection α (homObj N (𝒪 R)) (op W.unop.left)
    (((scalarExtensionDualMap α N).val.app (op W.unop.left)
      (scalarExtensionSection α (homObj N (𝒪 R)) (op W.unop.left) s φ)).app
        (op (Over.mk (𝟙 W.unop.left)))
          (scalarExtensionSection α N (op W.unop.left) 1 (localBasis N e W)))
    ((homObj N (𝒪 R)).val.map W.unop.hom.op (localDual N e)) = _
  rw [scalarExtensionDualMap_tmul, mul_one]
  rw [← scalarExtensionSection_base_smul, ← localDual_coordinates N e W φ]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem dual_inverse_forward {U : C}
    (e : N.over U ≅ (𝒪 R).over U) :
    localDualInverse α N e ≫ (scalarExtensionDualMap α N).over U = 𝟙 _ := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  change (scalarExtensionDualMap α N).val.app (op W.unop.left)
      ((localDualInverse α N e).val.app W φ) = φ
  apply scalarDual_section_ext α N (op W.unop.left)
  intro V t x
  change (((scalarExtensionDualMap α N).val.app (op W.unop.left)
      (scalarExtensionSection α (homObj N (𝒪 R)) (op W.unop.left)
        (φ.app (op (Over.mk (𝟙 W.unop.left)))
          (scalarExtensionSection α N (op W.unop.left) 1 (localBasis N e W)))
        ((homObj N (𝒪 R)).val.map W.unop.hom.op (localDual N e)))).app V) _ = _
  rw [scalarExtensionDualMap_tmul_slice]
  let Z : (Over U)ᵒᵖ := op (Over.mk (V.unop.hom ≫ W.unop.hom))
  let k : Over.mk V.unop.hom ⟶ Over.mk (𝟙 W.unop.left) := Over.homMk V.unop.hom
  have hp := PresheafOfModules.naturality_apply φ k.op
    (scalarExtensionSection α N (op W.unop.left) 1 (localBasis N e W))
  change φ.app V
      ((changeOfRingsOfUniverses α N).val.map V.unop.hom.op _) = _ at hp
  have hb := extendedBasis_natural α N e
    (show W ⟶ Z from (Over.homMk V.unop.hom).op)
  change (changeOfRingsOfUniverses α N).val.map V.unop.hom.op
      (scalarExtensionSection α N (op W.unop.left) 1 (localBasis N e W)) =
    scalarExtensionSection α N (op V.unop.left) 1 (localBasis N e Z) at hb
  rw [hb] at hp
  change φ.app V
      (scalarExtensionSection α N (op V.unop.left) 1 (localBasis N e Z)) =
    S.obj.map V.unop.hom.op
      (φ.app (op (Over.mk (𝟙 W.unop.left)))
        (scalarExtensionSection α N (op W.unop.left) 1 (localBasis N e W))) at hp
  have hx : scalarExtensionSection α N (op V.unop.left) t x =
      (t * α.hom.app (op V.unop.left) ((localDual N e).app Z x)) •
        scalarExtensionSection α N (op V.unop.left) 1 (localBasis N e Z) := by
    rw [scalarExtensionSection_smul, mul_one, ← scalarExtensionSection_base_smul,
      localBasis_coordinates N e Z x]
  rw [hx, map_smul]
  erw [hp]
  change _ * t * α.hom.app (op V.unop.left) ((localDual N e).app Z x) =
    (t * α.hom.app (op V.unop.left) ((localDual N e).app Z x)) * _
  ac_rfl

private theorem dual_over_isIso {U : C}
    (e : N.over U ≅ (𝒪 R).over U) : IsIso ((scalarExtensionDualMap α N).over U) :=
  ⟨⟨localDualInverse α N e, dual_forward_inverse α N e, dual_inverse_forward α N e⟩⟩

end DualInverse

end LocalBasis

/-- Scalar extension preserves rank one, and its explicit internal-dual map is invertible.
Source: Stacks Project, Tags 03EK, 03EM and 04TT
(blueprint: lem-sp-scalar-extension-dual-local-iso).

Proof: choose local generators data witnessing that `N` is locally free of rank one.
Its presentation is an isomorphism from the free module on a singleton over every
member of the covering. Identify this free module with the unit. Restrict the scalar
extension to each such slice: the restricted sheafification unit is locally bijective,
so its universal property identifies it with sheafification of the restricted tensor
presheaf. Extend the two inverse trivialization maps sectionwise and descend them;
their composites are identities on pure tensors. The unit comparison then identifies
the extended module with the target unit on the same covering. These trivializations
witness that the extension is invertible.

For the dual map, the same argument applies to the internal Hom on every slice.
In the chosen basis the functional is determined by its value on the basis vector.
The map in `scalarExtensionDualMap_tmul` sends an extended functional to the
functional with the same scalar coefficient, since evaluation is `s*t*α(f(x))`.
Thus it is an isomorphism on each trivializing slice: its inverse sends the functional
with coefficient `s` to `s` times the extended dual basis vector. On overlaps these
inverses agree, as both invert the same map. Sheaf separatedness gives uniqueness and
the sheaf gluing property gives a global inverse. The two composites are identities
locally, hence globally. The internal Hom and its scalar extension use their actual
maximum universes; the argument uses locally bijective units in that universe and
the rank-one trivializations in the original module universe. Empty covering families
and the zero ring cause no exception, since their sheaf conditions force unique local
data. No flatness is used. -/
theorem scalarExtensionDual_localIsomorphism
    {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC u}]
    [HasWeakSheafify J AddCommGrpCat.{max uC vC u}]
    [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (R S : Sheaf J CommRingCat.{u}) (α : R ⟶ S)
    (N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    [N.IsInvertible] :
    (changeOfRingsOfUniverses α N).IsInvertible ∧ IsIso (scalarExtensionDualMap α N) := by
  classical
  obtain ⟨q, hq⟩ := IsInvertible.exists_isInvertibleData (M := N)
  have := hq
  let e (i : q.I) : N.over (q.X i) ≅ (unit
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).over (q.X i) :=
    have := (hq.nonempty_unique i).some
    (asIso (q.generators i).π).symm ≪≫ freeUniqueIso _
  constructor
  · exact isInvertible_of_forall_over_unit q.X q.coversTop
      (fun i ↦ ⟨extendedBasisIso α N (e i)⟩)
  · suffices h : IsIso ((toSheaf _).map (scalarExtensionDualMap α N)) by
      exact isIso_of_reflects_iso (scalarExtensionDualMap α N) (toSheaf _)
    apply Sheaf.isIso_of_coversTop q.coversTop
    intro i
    have := dual_over_isIso α N (e i)
    exact Functor.map_isIso (toSheaf _) ((scalarExtensionDualMap α N).over (q.X i))

end SheafOfModules
