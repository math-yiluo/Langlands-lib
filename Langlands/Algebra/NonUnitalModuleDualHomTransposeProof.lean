import Langlands.Algebra.NonUnitalModuleDualHomTransposeStatements

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra.NonUnitalModuleDualHomTransposeProof

open NonUnitalModuleDual NonUnitalModuleDualHomTranspose
open NonUnitalModuleDualHomTransposeStatements

universe uA uV uW uV' uW'

section Components

variable {A : Type uA} [NonUnitalRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  {V : Type uV} [AddCommGroup V] [NonUnitalModule Aᵐᵒᵖ V]
  {W : Type uW} [AddCommGroup W] [NonUnitalModule A W]
  (hA : IsIdempotented A) (hV : IsNondegenerate Aᵐᵒᵖ V)
  (hW : IsNondegenerate A W)

local instance : NonUnitalModule Aᵐᵒᵖ (FullDual hA hW) := fullAction hA hW
local instance : NonUnitalModule Aᵐᵒᵖᵐᵒᵖ (FullDual hA.op hV) := fullAction hA.op hV
local instance : Module ℂ (R hA hV hW) := rModule hA hV hW
local instance : Module ℂ (L hA hV hW) := lModule hA hV hW

/-- Swapping the evaluation variables twice recovers the original right intertwiner. -/
theorem S_T (φ : R hA hV hW) : S hA hV hW (T hA hV hW φ) = φ := by
  apply NonUnitalModuleHom.ext
  intro v
  exact dual_ext hA hW (fun _ => rfl)

/-- The same double swap recovers the original left intertwiner. -/
theorem T_S (ψ : L hA hV hW) : T hA hV hW (S hA hV hW ψ) = ψ := by
  let _ := rightDualAction hA hV
  apply NonUnitalModuleHom.ext
  intro w
  exact dual_ext hA.op hV (fun _ => rfl)

/-- Both prescribed inverse identities hold as entire complex-linear maps. -/
theorem inverseIdentities : InverseIdentities hA hV hW := by
  constructor
  · exact LinearMap.ext (S_T hA hV hW)
  · exact LinearMap.ext (T_S hA hV hW)

/-- The equivalence uses exactly the published forward and reverse linear maps. -/
def equiv : R hA hV hW ≃ₗ[ℂ] L hA hV hW where
  toLinearMap := T hA hV hW
  invFun := S hA hV hW
  left_inv := S_T hA hV hW
  right_inv := T_S hA hV hW

/-- All six prescribed whole-map, additive-map and function pins are retained. -/
theorem prescribedEquivalence : PrescribedEquivalence hA hV hW := by
  exact ⟨equiv hA hV hW, rfl, rfl, T_toAddMonoidHom hA hV hW,
    S_toAddMonoidHom hA hV hW, rfl, rfl⟩

end Components

section Naturality

variable {A : Type uA} [NonUnitalRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  {V : Type uV} [AddCommGroup V] [NonUnitalModule Aᵐᵒᵖ V]
  {W : Type uW} [AddCommGroup W] [NonUnitalModule A W]
  {V' : Type uV'} [AddCommGroup V'] [NonUnitalModule Aᵐᵒᵖ V']
  {W' : Type uW'} [AddCommGroup W'] [NonUnitalModule A W']
  (hA : IsIdempotented A) (hV : IsNondegenerate Aᵐᵒᵖ V)
  (hW : IsNondegenerate A W) (hV' : IsNondegenerate Aᵐᵒᵖ V')
  (hW' : IsNondegenerate A W')
  (f : NonUnitalModuleHom Aᵐᵒᵖ V' V) (g : NonUnitalModuleHom A W' W)

local instance : NonUnitalModule Aᵐᵒᵖ (FullDual hA hW) := fullAction hA hW
local instance : NonUnitalModule Aᵐᵒᵖ (FullDual hA hW') := fullAction hA hW'
local instance : NonUnitalModule Aᵐᵒᵖᵐᵒᵖ (FullDual hA.op hV) := fullAction hA.op hV
local instance : NonUnitalModule Aᵐᵒᵖᵐᵒᵖ (FullDual hA.op hV') := fullAction hA.op hV'
local instance : Module ℂ (R hA hV hW) := rModule hA hV hW
local instance : Module ℂ (L hA hV hW) := lModule hA hV hW
local instance : Module ℂ (R hA hV' hW') := rModule hA hV' hW'
local instance : Module ℂ (L hA hV' hW') := lModule hA hV' hW'

/-- The original right pre/postcomposition map preserves the named complex scalars. -/
def rLinear : R hA hV hW →ₗ[ℂ] R hA hV' hW' where
  toFun := Rfg hA hV hW hV' hW' f g
  map_add' := (Rfg hA hV hW hV' hW' f g).map_add
  map_smul' c φ := by
    apply NonUnitalModuleHom.ext
    intro v
    apply dual_ext hA hW'
    intro w
    exact (congrArg (fun q : FullDual hA hW => q (g w))
      (rModule_smul_val hA hV hW c φ (f v))).trans
      (congrArg (fun q : FullDual hA hW' => q w)
        (rModule_smul_val hA hV' hW' c (Rfg hA hV hW hV' hW' f g φ) v)).symm

/-- The transported left pre/postcomposition map preserves the named complex scalars. -/
def lLinear : L hA hV hW →ₗ[ℂ] L hA hV' hW' :=
  letI := rightDualAction hA hV'
  { toFun := Lfg hA hV hW hV' hW' f g
    map_add' := (Lfg hA hV hW hV' hW' f g).map_add
    map_smul' c ψ := by
      apply NonUnitalModuleHom.ext
      intro w
      apply dual_ext hA.op hV'
      intro v
      exact (congrArg (fun q : FullDual hA.op hV => q (f v))
        (lModule_smul_val hA hV hW c ψ (g w))).trans
        (congrArg (fun q : FullDual hA.op hV' => q v)
          (lModule_smul_val hA hV' hW' c (Lfg hA hV hW hV' hW' f g ψ) w)).symm }

/-- The complete additive map has not changed when packaged as a linear map. -/
theorem rLinear_toAddMonoidHom :
    (rLinear hA hV hW hV' hW' f g).toAddMonoidHom =
      Rfg hA hV hW hV' hW' f g := rfl

/-- The complete transported additive map has not changed either. -/
theorem lLinear_toAddMonoidHom :
    (lLinear hA hV hW hV' hW' f g).toAddMonoidHom =
      Lfg hA hV hW hV' hW' f g := rfl

/-- Naturality of the forward maps as equality of entire complex-linear maps. -/
theorem equiv_natural :
    (equiv hA hV' hW').toLinearMap.comp (rLinear hA hV hW hV' hW' f g) =
      (lLinear hA hV hW hV' hW' f g).comp (equiv hA hV hW).toLinearMap := by
  apply LinearMap.ext
  intro φ
  exact DFunLike.congr_fun (T_natural hA hV hW hV' hW' f g) φ

/-- Naturality of the inverse maps as equality of entire complex-linear maps. -/
theorem equiv_symm_natural :
    (equiv hA hV' hW').symm.toLinearMap.comp (lLinear hA hV hW hV' hW' f g) =
      (rLinear hA hV hW hV' hW' f g).comp (equiv hA hV hW).symm.toLinearMap := by
  apply LinearMap.ext
  intro ψ
  exact DFunLike.congr_fun (S_natural hA hV hW hV' hW' f g) ψ

/-- All naturality witnesses are constructed, including scalar linearity and both squares. -/
theorem naturality : Naturality hA hV hW hV' hW' f g := by
  exact ⟨rLinear hA hV hW hV' hW' f g, lLinear hA hV hW hV' hW' f g,
    equiv hA hV hW, equiv hA hV' hW', rfl, rfl, rfl, rfl, rfl, rfl,
    equiv_natural hA hV hW hV' hW' f g,
    equiv_symm_natural hA hV hW hV' hW' f g⟩

end Naturality

/-- Renard I.4.2.1 with the prescribed actions, scalars, maps and independent universes. -/
theorem dualHomTranspose : DualHomTranspose.{uA, uV, uW, uV', uW'} := by
  intro A _ _ _ _ V _ _ W _ _ hA hV hW
  refine ⟨inverseIdentities hA hV hW, prescribedEquivalence hA hV hW, ?_⟩
  intro V' _ _ W' _ _ hV' hW' f g
  exact naturality hA hV hW hV' hW' f g

/-! Closed unequal-universe specializations retain the entire published proposition. -/

example : DualHomTranspose.{0, 1, 2, 3, 4} := dualHomTranspose.{0, 1, 2, 3, 4}

example : DualHomTranspose.{4, 3, 2, 1, 0} := dualHomTranspose.{4, 3, 2, 1, 0}

end Langlands.Algebra.NonUnitalModuleDualHomTransposeProof
