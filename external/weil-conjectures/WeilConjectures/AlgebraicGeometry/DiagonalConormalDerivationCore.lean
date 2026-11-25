/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.DiagonalConormal
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# The normalized difference derivation into the diagonal conormal

Source: Stacks Project, Tag 08S2
(blueprint: lem-sc-diagonal-conormal-derivation-core-exists).

Over an open `U`, lift the difference of the projection pullbacks to the actual kernel
over the intersection of their inverse images of `U`. Apply the tensor-pullback unit
and restrict along the diagonal. The kernel inclusion is injective on sections, so
its lift is unique and respects addition and restrictions. Linearity of the unit
turns the product identity for the lifted differences into the Leibniz rule.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

noncomputable section
variable {X S : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private abbrev diagonalIdeal (f : X ⟶ S) :=
  kernel (SheafOfModules.unitToPushforwardObjUnit
    (pullback.diagonal f).toRingCatSheafHom)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private abbrev differenceOpen (f : X ⟶ S) (U : X.Opens) :=
  (pullback.fst f f) ⁻¹ᵁ U ⊓ (pullback.snd f f) ⁻¹ᵁ U

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem diagonal_le_differenceOpen (f : X ⟶ S) (U : X.Opens) :
    U ≤ (pullback.diagonal f) ⁻¹ᵁ differenceOpen f U := by
  simp only [differenceOpen, Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage,
    pullback.diagonal_fst, pullback.diagonal_snd, Scheme.Hom.id_preimage, inf_idem]
  exact le_rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private abbrev idealInclusion (f : X ⟶ S) (W : (pullback f f).Opens) :=
  (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
    (pullback.diagonal f).toRingCatSheafHom)).val.app (op W)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem idealInclusion_injective (f : X ⟶ S) (W : (pullback f f).Opens) :
    Function.Injective (idealInclusion f W) :=
  Scheme.Modules.injective_map_kernelι W _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem exists_kernelDifference (f : X ⟶ S) (U : X.Opens) (a : Γ(X, U)) :
    ∃ s : Γ(diagonalIdeal f, differenceOpen f U),
      idealInclusion f (differenceOpen f U) s =
        (pullback.snd f f).appLE U (differenceOpen f U) inf_le_right a -
          (pullback.fst f f).appLE U (differenceOpen f U) inf_le_left a := by
  let W := differenceOpen f U
  let δ := pullback.diagonal f
  let φ := SheafOfModules.unitToPushforwardObjUnit δ.toRingCatSheafHom
  let b := (pullback.snd f f).appLE U W inf_le_right a -
    (pullback.fst f f).appLE U W inf_le_left a
  have hb : (SheafOfModules.evaluation (pullback f f).ringCatSheaf (op W)).map φ b = 0 := by
    change δ.app W b = 0
    dsimp only [b]
    rw [map_sub]
    have hsnd : (pullback.snd f f).appLE U W inf_le_right ≫ δ.app W =
        (pullback.fst f f).appLE U W inf_le_left ≫ δ.app W := by
      rw [δ.app_eq_appLE, Scheme.Hom.appLE_comp_appLE,
        Scheme.Hom.appLE_comp_appLE]
      simp [δ]
    exact sub_eq_zero.mpr (ConcreteCategory.congr_hom hsnd a)
  have hb' : b ∈ Set.range
      ((SheafOfModules.evaluation (pullback f f).ringCatSheaf (op W)).map (kernel.ι φ)) := by
    rw [Scheme.Modules.range_map_kernelι]
    exact hb
  exact hb'

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def kernelDifference (f : X ⟶ S) (U : X.Opens) :
    Γ(X, U) →+ Γ(diagonalIdeal f, differenceOpen f U) where
  -- The kernel inclusion is injective, so this choice is the unique lift.
  toFun a := Classical.choose (exists_kernelDifference f U a)
  map_zero' := by
    apply idealInclusion_injective f (differenceOpen f U)
    rw [Classical.choose_spec (exists_kernelDifference f U 0)]
    simp
  map_add' a b := by
    apply idealInclusion_injective f (differenceOpen f U)
    refine (Classical.choose_spec (exists_kernelDifference f U (a + b))).trans ?_
    simp only [Classical.choose_spec (exists_kernelDifference f U a),
      Classical.choose_spec (exists_kernelDifference f U b), map_add]
    abel

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem kernelDifference_spec (f : X ⟶ S) (U : X.Opens) (a : Γ(X, U)) :
    idealInclusion f (differenceOpen f U) (kernelDifference f U a) =
      (pullback.snd f f).appLE U (differenceOpen f U) inf_le_right a -
        (pullback.fst f f).appLE U (differenceOpen f U) inf_le_left a :=
  Classical.choose_spec (exists_kernelDifference f U a)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def conormalClass (f : X ⟶ S) (U : X.Opens)
    (W : (pullback f f).Opens) (hδ : U ≤ (pullback.diagonal f) ⁻¹ᵁ W) :
    Γ(diagonalIdeal f, W) →+ Γ(diagonalConormal f, U) :=
  ((diagonalConormal f).val.map (homOfLE hδ).op).hom.toAddMonoidHom.comp
    ((((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction
      (pullback.diagonal f))).unit.app (diagonalIdeal f)).val.app (op W)).hom.toAddMonoidHom)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def conormalDifference (f : X ⟶ S) (U : X.Opens) :
    Γ(X, U) →+ Γ(diagonalConormal f, U) :=
  (conormalClass f U (differenceOpen f U) (diagonal_le_differenceOpen f U)).comp
    (kernelDifference f U)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem conormalClass_restrict (f : X ⟶ S) (U : X.Opens)
    (W W' : (pullback f f).Opens) (h : W' ≤ W)
    (hδ : U ≤ (pullback.diagonal f) ⁻¹ᵁ W)
    (hδ' : U ≤ (pullback.diagonal f) ⁻¹ᵁ W') (s : Γ(diagonalIdeal f, W)) :
    conormalClass f U W hδ s =
      conormalClass f U W' hδ' ((diagonalIdeal f).val.map (homOfLE h).op s) := by
  let η := ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction
    (pullback.diagonal f))).unit.app (diagonalIdeal f)).val
  have hn := PresheafOfModules.naturality_apply η (homOfLE h).op s
  change (diagonalConormal f).val.map (homOfLE hδ).op (η.app (op W) s) =
    (diagonalConormal f).val.map (homOfLE hδ').op
      (η.app (op W') ((diagonalIdeal f).val.map (homOfLE h).op s))
  erw [hn]
  change (diagonalConormal f).presheaf.map (homOfLE hδ).op (η.app (op W) s) =
    (diagonalConormal f).presheaf.map (homOfLE hδ').op
      ((diagonalConormal f).presheaf.map
        ((TopologicalSpace.Opens.map (pullback.diagonal f).base).map (homOfLE h)).op
        (η.app (op W) s))
  exact Functor.map_comp_apply (diagonalConormal f).presheaf
    ((TopologicalSpace.Opens.map (pullback.diagonal f).base).map (homOfLE h)).op
    (homOfLE hδ').op (η.app (op W) s)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem conormalDifference_formula (f : X ⟶ S)
    (U : X.Opens) (W : (pullback f f).Opens)
    (h₁ : W ≤ (pullback.fst f f) ⁻¹ᵁ U)
    (h₂ : W ≤ (pullback.snd f f) ⁻¹ᵁ U)
    (hδ : U ≤ (pullback.diagonal f) ⁻¹ᵁ W)
    (a : Γ(X, U)) (s : Γ(diagonalIdeal f, W))
    (hs : idealInclusion f W s =
      (pullback.snd f f).appLE U W h₂ a - (pullback.fst f f).appLE U W h₁ a) :
    conormalDifference f U a = conormalClass f U W hδ s := by
  have hW : W ≤ differenceOpen f U := le_inf h₁ h₂
  have hkernel : (diagonalIdeal f).val.map (homOfLE hW).op
      (kernelDifference f U a) = s := by
    apply idealInclusion_injective f W
    dsimp only [idealInclusion]
    erw [PresheafOfModules.naturality_apply]
    rw [kernelDifference_spec, hs]
    change (pullback f f).presheaf.map (homOfLE hW).op
      ((pullback.snd f f).appLE U (differenceOpen f U) inf_le_right a -
        (pullback.fst f f).appLE U (differenceOpen f U) inf_le_left a) = _
    rw [map_sub]
    congr 1
    · exact ConcreteCategory.congr_hom
        (Scheme.Hom.appLE_map _ _ (homOfLE hW).op) a
    · exact ConcreteCategory.congr_hom
        (Scheme.Hom.appLE_map _ _ (homOfLE hW).op) a
  exact (conormalClass_restrict f U (differenceOpen f U) W hW
    (diagonal_le_differenceOpen f U) hδ (kernelDifference f U a)).trans
      (congrArg (conormalClass f U W hδ) hkernel)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem conormalClass_smul (f : X ⟶ S) (U : X.Opens)
    (W : (pullback f f).Opens) (hδ : U ≤ (pullback.diagonal f) ⁻¹ᵁ W)
    (r : Γ(pullback f f, W)) (s : Γ(diagonalIdeal f, W)) :
    conormalClass f U W hδ (r • s) =
      (pullback.diagonal f).appLE W U hδ r • conormalClass f U W hδ s := by
  let η := ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction
    (pullback.diagonal f))).unit.app (diagonalIdeal f)).val
  have hn := (η.app (op W)).hom.map_smul r s
  change η.app (op W) (r • s) =
    (pullback.diagonal f).app W r •
      (show Γ(diagonalConormal f, (pullback.diagonal f) ⁻¹ᵁ W) from η.app (op W) s) at hn
  change (diagonalConormal f).val.map (homOfLE hδ).op (η.app (op W) (r • s)) = _
  rw [hn]
  exact (diagonalConormal f).val.map_smul (homOfLE hδ).op
    ((pullback.diagonal f).app W r) (η.app (op W) s)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem conormalDifference_mul (f : X ⟶ S) (U : X.Opens) (a b : Γ(X, U)) :
    conormalDifference f U (a * b) =
      a • conormalDifference f U b + b • conormalDifference f U a := by
  let W := differenceOpen f U
  let p := (pullback.snd f f).appLE U W inf_le_right
  let q := (pullback.fst f f).appLE U W inf_le_left
  have hk : kernelDifference f U (a * b) =
      p a • kernelDifference f U b + q b • kernelDifference f U a := by
    apply idealInclusion_injective f W
    simp only [map_add, map_smul]
    erw [kernelDifference_spec, kernelDifference_spec, kernelDifference_spec]
    change p (a * b) - q (a * b) = p a * (p b - q b) + q b * (p a - q a)
    simp only [map_mul]
    ring
  have hp (c : Γ(X, U)) :
      (pullback.diagonal f).appLE W U (diagonal_le_differenceOpen f U) (p c) = c := by
    have he : p ≫ (pullback.diagonal f).appLE W U
        (diagonal_le_differenceOpen f U) = 𝟙 _ := by
      dsimp only [p]
      rw [Scheme.Hom.appLE_comp_appLE]
      simp only [pullback.diagonal_snd]
      simp only [Scheme.Hom.appLE, Scheme.Hom.id_base, Scheme.Hom.id_app,
        homOfLE_refl, op_id, Category.id_comp]
      exact X.presheaf.map_id _
    exact ConcreteCategory.congr_hom he c
  have hq (c : Γ(X, U)) :
      (pullback.diagonal f).appLE W U (diagonal_le_differenceOpen f U) (q c) = c := by
    have he : q ≫ (pullback.diagonal f).appLE W U
        (diagonal_le_differenceOpen f U) = 𝟙 _ := by
      dsimp only [q]
      rw [Scheme.Hom.appLE_comp_appLE]
      simp only [pullback.diagonal_fst]
      simp only [Scheme.Hom.appLE, Scheme.Hom.id_base, Scheme.Hom.id_app,
        homOfLE_refl, op_id, Category.id_comp]
      exact X.presheaf.map_id _
    exact ConcreteCategory.congr_hom he c
  change conormalClass f U W _ (kernelDifference f U (a * b)) = _
  rw [hk, map_add, conormalClass_smul, conormalClass_smul, hp, hq]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem conormalClass_map (f : X ⟶ S) (U V : X.Opens) (h : V ≤ U)
    (W : (pullback f f).Opens) (hδ : U ≤ (pullback.diagonal f) ⁻¹ᵁ W)
    (s : Γ(diagonalIdeal f, W)) :
    (diagonalConormal f).val.map (homOfLE h).op (conormalClass f U W hδ s) =
      conormalClass f V W (h.trans hδ) s := by
  change (diagonalConormal f).presheaf.map (homOfLE h).op
    ((diagonalConormal f).presheaf.map (homOfLE hδ).op _) = _
  exact (Functor.map_comp_apply (diagonalConormal f).presheaf
    (homOfLE hδ).op (homOfLE h).op _).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem conormalDifference_map (f : X ⟶ S) {U V : X.Opensᵒᵖ}
    (i : U ⟶ V) (a : X.presheaf.obj U) :
    conormalDifference f V.unop (X.presheaf.map i a) =
      (diagonalConormal f).val.map i (conormalDifference f U.unop a) := by
  let h : V.unop ≤ U.unop := i.unop.le
  let hW : differenceOpen f V.unop ≤ differenceOpen f U.unop :=
    inf_le_inf ((TopologicalSpace.Opens.map (pullback.fst f f).base).map (homOfLE h)).le
      ((TopologicalSpace.Opens.map (pullback.snd f f).base).map (homOfLE h)).le
  have hk : (diagonalIdeal f).val.map (homOfLE hW).op (kernelDifference f U.unop a) =
      kernelDifference f V.unop (X.presheaf.map i a) := by
    apply idealInclusion_injective f (differenceOpen f V.unop)
    dsimp only [idealInclusion]
    erw [PresheafOfModules.naturality_apply]
    rw [kernelDifference_spec, kernelDifference_spec]
    change (pullback f f).presheaf.map (homOfLE hW).op
      ((pullback.snd f f).appLE U.unop (differenceOpen f U.unop) inf_le_right a -
        (pullback.fst f f).appLE U.unop (differenceOpen f U.unop) inf_le_left a) = _
    rw [map_sub]
    congr 1
    · have he : (pullback.snd f f).appLE U.unop (differenceOpen f U.unop) inf_le_right ≫
          (pullback f f).presheaf.map (homOfLE hW).op =
        X.presheaf.map i ≫
          (pullback.snd f f).appLE V.unop (differenceOpen f V.unop) inf_le_right := by
        rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
      exact ConcreteCategory.congr_hom he a
    · have he : (pullback.fst f f).appLE U.unop (differenceOpen f U.unop) inf_le_left ≫
          (pullback f f).presheaf.map (homOfLE hW).op =
        X.presheaf.map i ≫
          (pullback.fst f f).appLE V.unop (differenceOpen f V.unop) inf_le_left := by
        rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
      exact ConcreteCategory.congr_hom he a
  change conormalClass f V.unop (differenceOpen f V.unop) _
      (kernelDifference f V.unop (X.presheaf.map i a)) =
    (diagonalConormal f).val.map i
      (conormalClass f U.unop (differenceOpen f U.unop) _ (kernelDifference f U.unop a))
  have hi : i = (homOfLE h).op := Subsingleton.elim _ _
  conv_rhs => rw [hi]
  rw [conormalClass_map f U.unop V.unop h]
  exact (congrArg (conormalClass f V.unop (differenceOpen f V.unop)
    (diagonal_le_differenceOpen f V.unop)) hk).symm.trans
      (conormalClass_restrict f V.unop (differenceOpen f U.unop)
        (differenceOpen f V.unop) hW (h.trans (diagonal_le_differenceOpen f U.unop))
        (diagonal_le_differenceOpen f V.unop) (kernelDifference f U.unop a)).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem conormalDifference_app (f : X ⟶ S) (V : S.Opens) (a : Γ(S, V)) :
    conormalDifference f (f ⁻¹ᵁ V) (f.app V a) = 0 := by
  have hk : kernelDifference f (f ⁻¹ᵁ V) (f.app V a) = 0 := by
    apply idealInclusion_injective f (differenceOpen f (f ⁻¹ᵁ V))
    rw [kernelDifference_spec, map_zero]
    apply sub_eq_zero.mpr
    have he : f.app V ≫ (pullback.snd f f).appLE (f ⁻¹ᵁ V)
        (differenceOpen f (f ⁻¹ᵁ V)) inf_le_right =
      f.app V ≫ (pullback.fst f f).appLE (f ⁻¹ᵁ V)
        (differenceOpen f (f ⁻¹ᵁ V)) inf_le_left := by
      rw [f.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
      simp only [pullback.condition]
    exact ConcreteCategory.congr_hom he a
  change conormalClass f (f ⁻¹ᵁ V) _ _ (kernelDifference f (f ⁻¹ᵁ V) (f.app V a)) = 0
  rw [hk, map_zero]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The difference derivation into the diagonal conormal, with its local formula.
Source: Stacks Project, Tag 08S2. Construct the difference of the two splittings
of the square-zero diagonal extension and check the formula locally.
(blueprint: lem-sc-diagonal-conormal-derivation-core-exists). -/
theorem exists_diagonalConormalDerivation_core (f : X ⟶ S) :
    ∃ D : (diagonalConormal f).val.Derivation' f.pullbackPresheafToPresheaf,
      ∀ (U : X.Opens) (W : (pullback f f).Opens)
        (h₁ : W ≤ (pullback.fst f f) ⁻¹ᵁ U)
        (h₂ : W ≤ (pullback.snd f f) ⁻¹ᵁ U)
        (hδ : U ≤ (pullback.diagonal f) ⁻¹ᵁ W)
        (a : Γ(X, U)) (s : Γ(kernel (SheafOfModules.unitToPushforwardObjUnit
          (pullback.diagonal f).toRingCatSheafHom), W)),
        (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (pullback.diagonal f).toRingCatSheafHom)).val.app (op W) s =
            (pullback.snd f f).appLE U W h₂ a -
              (pullback.fst f f).appLE U W h₁ a →
        D.d (X := op U) a =
          (diagonalConormal f).presheaf.map (homOfLE hδ).op
            (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction
              (pullback.diagonal f))).unit.app
                (kernel (SheafOfModules.unitToPushforwardObjUnit
                  (pullback.diagonal f).toRingCatSheafHom))).val.app (op W) s) := by
  let D := f.derivationMk (fun {U} ↦ conormalDifference f U.unop)
    (fun {U} a b ↦ conormalDifference_mul f U.unop a b)
    (fun i a ↦ conormalDifference_map f i a)
    (fun V a ↦ conormalDifference_app f V a)
  refine ⟨D, ?_⟩
  intro U W h₁ h₂ hδ a s hs
  exact conormalDifference_formula f U W h₁ h₂ hδ a s hs
end
end AlgebraicGeometry

