/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PicardConstantSectionsTensor

/-! # Pointwise scalar extension of a constant module presheaf

Source: Stacks Project, Varieties, Tag 0BED, degree-zero tensor calculation;
the representing-object argument in lem-sc-picard-constant-tensor-balanced-sections.
-/

public section
universe w
open CategoryTheory Opposite
open scoped TensorProduct ChangeOfRings
namespace AlgebraicGeometry.Scheme.Modules
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section
variable {k : Type w} [Field k] {Y : Scheme.{w}}
variable (g : Y ⟶ Spec (CommRingCat.of k)) (M : ModuleCat.{w} k)

private def extensionRestriction {U V : Y.Opensᵒᵖ} (i : U ⟶ V) :
    (ModuleCat.extendScalars (scalarMap g U.unop)).obj M ⟶
      (ModuleCat.restrictScalars (Y.presheaf.map i).hom).obj
        ((ModuleCat.extendScalars (scalarMap g V.unop)).obj M) := by
  let : Module k Γ(Y, V.unop) := Module.compHom _ (scalarMap g V.unop)
  let T := (ModuleCat.restrictScalars (Y.presheaf.map i).hom).obj
    ((ModuleCat.extendScalars (scalarMap g V.unop)).obj M)
  let h : M ⟶ (ModuleCat.restrictScalars (scalarMap g U.unop)).obj T :=
    ModuleCat.ofHom (Y := (ModuleCat.restrictScalars (scalarMap g U.unop)).obj T)
      { toFun := fun s ↦ (1 : Γ(Y, V.unop)) ⊗ₜ[k, scalarMap g V.unop] s
        map_add' := by intros; rw [TensorProduct.tmul_add]
        map_smul' := by
          intro r s
          change (1 : Γ(Y, V.unop)) ⊗ₜ[k] (r • s) =
            (Y.presheaf.map i (scalarMap g U.unop r)) •
              ((1 : Γ(Y, V.unop)) ⊗ₜ[k] s)
          have hn : Y.presheaf.map i (scalarMap g U.unop r) = scalarMap g V.unop r := by
            simp only [scalarMap, RingHom.comp_apply]
            change (Y.presheaf.map (homOfLE (le_top (a := U.unop))).op ≫
              Y.presheaf.map i) _ = _
            rw [← Y.presheaf.map_comp]
            rfl
          rw [hn, TensorProduct.tmul_smul]
          rfl }
  exact ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
    (scalarMap g U.unop) h

private theorem extensionRestriction_tmul {U V : Y.Opensᵒᵖ} (i : U ⟶ V)
    (a : Γ(Y, U.unop)) (s : M) :
    extensionRestriction g M i (a ⊗ₜ[k, scalarMap g U.unop] s) =
      (Y.presheaf.map i a) ⊗ₜ[k, scalarMap g V.unop] s := by
  let : Module k Γ(Y, V.unop) := Module.compHom _ (scalarMap g V.unop)
  let T := (ModuleCat.restrictScalars (Y.presheaf.map i).hom).obj
    ((ModuleCat.extendScalars (scalarMap g V.unop)).obj M)
  let : Module k T := Module.compHom T (scalarMap g U.unop)
  let : Module k Γ(Y, U.unop) := Module.compHom _ (scalarMap g U.unop)
  unfold extensionRestriction
  erw [ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_hom_apply,
    TensorProduct.lift.tmul]
  change Y.presheaf.map i a •
    ((1 : Γ(Y, V.unop)) ⊗ₜ[k, scalarMap g V.unop] s) = _
  rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]

private def extensionPresheaf : _root_.PresheafOfModules Y.ringCatSheaf.obj where
  obj U := (ModuleCat.extendScalars (scalarMap g U.unop)).obj M
  map i := extensionRestriction g M i
  map_id U := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro s
    rw [extensionRestriction_tmul]
    simp
    rfl
  map_comp i j := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro s
    simp only [ModuleCat.comp_apply, extensionRestriction_tmul]
    change _ = extensionRestriction g M j _
    erw [extensionRestriction_tmul]
    simp

private def extensionToRestrict (H : _root_.PresheafOfModules Y.ringCatSheaf.obj)
    (f : extensionPresheaf g M ⟶ H) :
    picardConstantVector k Y M ⟶
      (PresheafOfModules.pushforward (picardConstantRingMap k Y g)).obj H where
  app U := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars
    (scalarMap g U.unop) (f.app U)
  naturality := by
    intro U V i
    ext s
    change f.app V ((1 : Γ(Y, V.unop)) ⊗ₜ[k, scalarMap g V.unop] s) =
      H.map i (f.app U ((1 : Γ(Y, U.unop)) ⊗ₜ[k, scalarMap g U.unop] s))
    rw [← PresheafOfModules.naturality_apply f i]
    change _ = f.app V (extensionRestriction g M i _)
    rw [extensionRestriction_tmul]
    simp

private def extensionFromRestrict (H : _root_.PresheafOfModules Y.ringCatSheaf.obj)
    (h : picardConstantVector k Y M ⟶
      (PresheafOfModules.pushforward (picardConstantRingMap k Y g)).obj H) :
    extensionPresheaf g M ⟶ H where
  app U := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
    (scalarMap g U.unop) (h.app U)
  naturality := by
    intro U V i
    apply ModuleCat.ExtendScalars.hom_ext
    intro s
    change ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
      (scalarMap g V.unop) (h.app V) (extensionRestriction g M i _) =
      H.map i (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
        (scalarMap g U.unop) (h.app U) _)
    rw [extensionRestriction_tmul]
    simp only [map_one]
    let : Module k Γ(Y, V.unop) := Module.compHom _ (scalarMap g V.unop)
    let : Module k (H.obj V) := Module.compHom _ (scalarMap g V.unop)
    let : Module k Γ(Y, U.unop) := Module.compHom _ (scalarMap g U.unop)
    let : Module k (H.obj U) := Module.compHom _ (scalarMap g U.unop)
    let : Module k (((PresheafOfModules.pushforward₀ (𝟭 Y.Opens)
        Y.ringCatSheaf.obj).obj H).obj U) := inferInstanceAs (Module k (H.obj U))
    let : Module k (((PresheafOfModules.pushforward₀ (𝟭 Y.Opens)
        Y.ringCatSheaf.obj).obj H).obj V) := inferInstanceAs (Module k (H.obj V))
    erw [ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_hom_apply
      («R» := k) («S» := Γ(Y, V.unop)), TensorProduct.lift.tmul,
      ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_hom_apply
      («R» := k) («S» := Γ(Y, U.unop)), TensorProduct.lift.tmul]
    change (1 : Γ(Y, V.unop)) • (show H.obj V from h.app V s) =
      H.map i ((1 : Γ(Y, U.unop)) • (show H.obj U from h.app U s))
    simp only [one_smul]
    exact PresheafOfModules.naturality_apply h i s

private def extensionHomEquiv (H : _root_.PresheafOfModules Y.ringCatSheaf.obj) :
    (extensionPresheaf g M ⟶ H) ≃
      (picardConstantVector k Y M ⟶
        (PresheafOfModules.pushforward (picardConstantRingMap k Y g)).obj H) where
  toFun := extensionToRestrict g M H
  invFun := extensionFromRestrict g M H
  left_inv f := by
    apply PresheafOfModules.hom_ext
    intro U
    exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv (scalarMap g U.unop)).left_inv _
  right_inv h := by
    apply PresheafOfModules.hom_ext
    intro U
    exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv (scalarMap g U.unop)).right_inv _

private def extensionCorepresentableBy :
    (PresheafOfModules.pushforward (picardConstantRingMap k Y g) ⋙
      coyoneda.obj (op (picardConstantVector k Y M))).CorepresentableBy
        (extensionPresheaf g M) where
  homEquiv := extensionHomEquiv g M _
  homEquiv_comp := by intros; rfl

/-- Extension of a constant module to the structure presheaf is pointwise base change.
Source: Stacks Project, Varieties, Tag 0BED, degree-zero tensor calculation;
representing-object argument of lem-sc-picard-constant-tensor-balanced-sections.
(blueprint: lem-sc-picard-constant-scalar-extension-sections).

Proof: Construct E(V) = O_Y(V) tensor_k M, with restriction sending a tensor s
 to res(a) tensor s. Identity, composition, and semilinearity follow on pure tensors.
For any structure-module presheaf H, a morphism E to H gives a morphism from the
constant M presheaf to restriction of scalars of H by evaluating at 1 tensor s.
Conversely extend such a morphism by a tensor s mapping to a times its value at s.
The scalar-extension Hom equivalence makes these assignments well-defined and inverse.
Restriction compatibility follows from the same formulas and res(1)=1. They are
natural in H. Thus E and the chosen pullback represent the same Hom functor;
uniqueness of representing objects gives a presheaf isomorphism, whose components
are these linear equivalences.
This includes the empty open and zero M; no nonzero ring or geometric assumption
is used in the scalar-extension adjunction. -/
def picardConstantScalarExtensionSections
    (k : Type w) [Field k] (Y : Scheme.{w})
    (g : Y ⟶ Spec (CommRingCat.of k)) (M : ModuleCat.{w} k) (V : Y.Opens) :
    (ModuleCat.extendScalars (scalarMap g V)).obj M ≃ₗ[Γ(Y, V)]
      ((PresheafOfModules.pullback (picardConstantRingMap k Y g)).obj
        (picardConstantVector k Y M)).obj (op V) :=
  ((PresheafOfModules.evaluation Y.ringCatSheaf.obj (op V)).mapIso
    ((extensionCorepresentableBy g M).uniqueUpToIso
      ((PresheafOfModules.pullbackPushforwardAdjunction
        (picardConstantRingMap k Y g)).corepresentableBy
          (picardConstantVector k Y M)))).toLinearEquiv

/-- The identifications `picardConstantScalarExtensionSections` commute with restriction:
restriction of the pullback corresponds to restricting the ring coefficient.
(blueprint: lem-sc-picard-constant-scalar-extension-sections). -/
theorem picardConstantScalarExtensionSections_map
    (k : Type w) [Field k] (Y : Scheme.{w})
    (g : Y ⟶ Spec (CommRingCat.of k)) (M : ModuleCat.{w} k)
    {U V : Y.Opensᵒᵖ} (i : U ⟶ V) (a : Γ(Y, U.unop)) (s : M) :
    ((PresheafOfModules.pullback (picardConstantRingMap k Y g)).obj
      (picardConstantVector k Y M)).map i
        (picardConstantScalarExtensionSections k Y g M U.unop
          (a ⊗ₜ[k, scalarMap g U.unop] s)) =
      picardConstantScalarExtensionSections k Y g M V.unop
        ((Y.presheaf.map i a) ⊗ₜ[k, scalarMap g V.unop] s) := by
  let e := (extensionCorepresentableBy g M).uniqueUpToIso
    ((PresheafOfModules.pullbackPushforwardAdjunction
      (picardConstantRingMap k Y g)).corepresentableBy (picardConstantVector k Y M))
  change ((PresheafOfModules.pullback (picardConstantRingMap k Y g)).obj
      (picardConstantVector k Y M)).map i
        (e.hom.app U (a ⊗ₜ[k, scalarMap g U.unop] s)) =
      e.hom.app V ((Y.presheaf.map i a) ⊗ₜ[k, scalarMap g V.unop] s)
  rw [← PresheafOfModules.naturality_apply e.hom i]
  change e.hom.app V (extensionRestriction g M i _) = _
  rw [extensionRestriction_tmul]

end
end AlgebraicGeometry.Scheme.Modules
