import Langlands.Algebra.NonUnitalModuleDual
import Langlands.Algebra.NonUnitalModuleDualMap
import Langlands.Algebra.NonUnitalModuleDualFunctor
import Langlands.Algebra.NondegenerateModuleHomScalars

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra.NonUnitalModuleDualHomTranspose

open MulOpposite NonUnitalModuleDual

universe uA uV uW uV' uW'

section RightDual

variable {A : Type uA} [NonUnitalRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  {V : Type uV} [AddCommGroup V] [NonUnitalModule Aᵐᵒᵖ V]
  (hA : IsIdempotented A) (hV : IsNondegenerate Aᵐᵒᵖ V)

local instance : NonUnitalModule Aᵐᵒᵖᵐᵒᵖ (FullDual hA.op hV) := fullAction hA.op hV

/-- The published double-op transport on the actual dual of the right module. -/
abbrev rightDualAction : NonUnitalModule A (Dual hA.op hV) :=
  fromDoubleOppositeAction (A := A) (M := Dual hA.op hV)


/-- Intrinsic nondegeneracy of this very transported action. -/
theorem rightDual_isNondegenerate :
    letI := rightDualAction hA hV
    IsNondegenerate A (Dual hA.op hV) :=
  fromDoubleOpposite_isNondegenerate (isNondegenerate hA.op hV)

theorem rightDualAction_val (a : A) (ell : Dual hA.op hV) :
    letI := rightDualAction hA hV
    (a • ell).val = ell.val.comp (NondegenerateScalars.toLinearEndHom ℂ hA.op hV (op a)) := rfl

@[simp] theorem rightDualAction_apply (a : A) (ell : Dual hA.op hV) (v : V) :
    letI := rightDualAction hA hV
    (a • ell).val v = ell.val (op a • v) := rfl

/-- Canonical scalars for the transported action are the inherited pointwise ones. -/
theorem rightDual_canonicalModule_eq :
    letI := rightDualAction hA hV
    NondegenerateScalars.complexModule hA (rightDual_isNondegenerate hA hV) =
      dualModule hA.op hV := by
  let _ := rightDualAction hA hV
  let _ := dualModule hA.op hV
  let _ := dual_isScalarTower hA.op hV
  let _ := fromDoubleOpposite_isScalarTower (A := A) (M := Dual hA.op hV)
  exact NondegenerateScalars.module_eq_of_compatible ℂ hA (rightDual_isNondegenerate hA hV)

theorem rightDual_canonical_smul_val (c : ℂ) (ell : Dual hA.op hV) :
    letI := rightDualAction hA hV
    letI := NondegenerateScalars.complexModule hA (rightDual_isNondegenerate hA hV)
    (c • ell).val = c • ell.val := by
  let _ := rightDualAction hA hV
  rw [rightDual_canonicalModule_eq]
  rfl

@[simp] theorem rightDual_canonical_smul_apply (c : ℂ) (ell : Dual hA.op hV) (v : V) :
    letI := rightDualAction hA hV
    letI := NondegenerateScalars.complexModule hA (rightDual_isNondegenerate hA hV)
    (c • ell).val v = c • ell.val v :=
  congrArg (fun q : FullDual hA.op hV => q v) (rightDual_canonical_smul_val hA hV c ell)

end RightDual

section Carriers

variable {A : Type uA} [NonUnitalRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  {V : Type uV} [AddCommGroup V] [NonUnitalModule Aᵐᵒᵖ V]
  {W : Type uW} [AddCommGroup W] [NonUnitalModule A W]

/-- Exactly the original right Hom into the actual dual of W. -/
abbrev R (hA : IsIdempotented A) (_hV : IsNondegenerate Aᵐᵒᵖ V)
    (hW : IsNondegenerate A W) :=
  letI := fullAction hA hW
  NonUnitalModuleHom Aᵐᵒᵖ V (Dual hA hW)

/-- Exactly the original left Hom into the explicitly transported actual dual of V. -/
abbrev L (hA : IsIdempotented A) (hV : IsNondegenerate Aᵐᵒᵖ V)
    (_hW : IsNondegenerate A W) :=
  letI := fullAction hA.op hV
  letI := rightDualAction hA hV
  NonUnitalModuleHom A W (Dual hA.op hV)

variable (hA : IsIdempotented A) (hV : IsNondegenerate Aᵐᵒᵖ V) (hW : IsNondegenerate A W)

local instance : NonUnitalModule Aᵐᵒᵖ (FullDual hA hW) := fullAction hA hW
local instance : NonUnitalModule Aᵐᵒᵖᵐᵒᵖ (FullDual hA.op hV) := fullAction hA.op hV

/-- The named canonical Hom scalars, with the actual target's nondegeneracy. -/
@[instance_reducible]
def rModule : Module ℂ (R hA hV hW) :=
  NondegenerateModuleHomScalars.complexHomModule hA.op (isNondegenerate hA hW)

@[instance_reducible]
def lModule : Module ℂ (L hA hV hW) :=
  letI := rightDualAction hA hV
  NondegenerateModuleHomScalars.complexHomModule hA (rightDual_isNondegenerate hA hV)

theorem rModule_eq : rModule hA hV hW =
    NondegenerateModuleHomScalars.complexHomModule hA.op (isNondegenerate hA hW) := rfl

theorem lModule_eq :
    letI := rightDualAction hA hV
    lModule hA hV hW =
    NondegenerateModuleHomScalars.complexHomModule hA (rightDual_isNondegenerate hA hV) := rfl

local instance : Module ℂ (R hA hV hW) := rModule hA hV hW
local instance : Module ℂ (L hA hV hW) := lModule hA hV hW

/-- Pointwise formula with exactly the canonical recovered target scalars. -/
theorem rModule_smul_apply (c : ℂ) (φ : R hA hV hW) (v : V) :
    letI := NondegenerateScalars.complexModule hA.op (isNondegenerate hA hW)
    (c • φ) v = c • φ v := rfl

theorem lModule_smul_apply (c : ℂ) (ψ : L hA hV hW) (w : W) :
    letI := rightDualAction hA hV
    letI := NondegenerateScalars.complexModule hA (rightDual_isNondegenerate hA hV)
    (c • ψ) w = c • ψ w := rfl

theorem rModule_smul_val (c : ℂ) (φ : R hA hV hW) (v : V) :
    ((c • φ) v).val = c • (φ v).val := canonical_smul_val hA hW c (φ v)

theorem lModule_smul_val (c : ℂ) (ψ : L hA hV hW) (w : W) :
    ((c • ψ) w).val = c • (ψ w).val := rightDual_canonical_smul_val hA hV c (ψ w)

/-- The full functional v ↦ φ(v)(w), on V with its recovered complex module. -/
def transposeFull (φ : R hA hV hW) (w : W) : FullDual hA.op hV :=
  letI := NondegenerateScalars.complexModule hA.op hV
  { toFun v := (φ v).val w
    map_add' v v' := by
      change (φ (v + v')).val w = (φ v).val w + (φ v').val w
      rw [φ.map_add]
      rfl
    map_smul' c v := by
      change (φ (c • v)).val w = c • (φ v).val w
      have h := NondegenerateScalars.map_smul ℂ hA.op hV (isNondegenerate hA hW) φ c v
      exact (congrArg (fun q : Dual hA hW => q.val w) h).trans
        (canonical_smul_apply hA hW c (φ v) w) }

theorem transposeFull_coe (φ : R hA hV hW) (w : W) :
    ⇑(transposeFull hA hV hW φ w) = fun v => (φ v).val w := rfl

@[simp] theorem transposeFull_apply (φ : R hA hV hW) (w : W) (v : V) :
    transposeFull hA hV hW φ w v = (φ v).val w := rfl

/-- An original idempotent fixing w also fixes the swapped full functional. -/
theorem transposeFull_fixed (φ : R hA hV hW) (w : W)
    (e : Idempotent A) (he : (e : A) • w = w) (v : V) :
    transposeFull hA hV hW φ w (op (e : A) • v) = transposeFull hA hV hW φ w v := by
  change (φ (op (e : A) • v)).val w = (φ v).val w
  rw [φ.map_smul]
  change (φ v).val ((e : A) • w) = (φ v).val w
  rw [he]

theorem transposeFull_mem (φ : R hA hV hW) (w : W) :
    transposeFull hA hV hW φ w ∈ nondegeneratePart hA.op.op (FullDual hA.op hV) := by
  apply (mem_dual_iff hA.op hV _).mpr
  obtain ⟨e, he⟩ := hW w
  refine ⟨⟨op (e : A), congrArg op e.property.eq⟩, ?_⟩
  exact transposeFull_fixed hA hV hW φ w e he

/-- The actual original left intertwiner, without replacing the dual subtype. -/
def transpose (φ : R hA hV hW) : L hA hV hW :=
  letI := rightDualAction hA hV
  { toFun w := ⟨transposeFull hA hV hW φ w, transposeFull_mem hA hV hW φ w⟩
    map_zero' := by
      apply dual_ext hA.op hV
      intro v
      let _ := NondegenerateScalars.complexModule hA hW
      exact (φ v).val.map_zero
    map_add' w w' := by
      apply dual_ext hA.op hV
      intro v
      let _ := NondegenerateScalars.complexModule hA hW
      exact (φ v).val.map_add w w'
    map_smul' a w := by
      apply dual_ext hA.op hV
      intro v
      change (φ v).val (a • w) = (φ (op a • v)).val w
      rw [φ.map_smul]
      rfl }

/-- Equality of the entire included functional, not only evaluations. -/
theorem transpose_val (φ : R hA hV hW) (w : W) :
    (transpose hA hV hW φ w).val = transposeFull hA hV hW φ w := rfl

@[simp] theorem transpose_apply (φ : R hA hV hW) (w : W) (v : V) :
    (transpose hA hV hW φ w).val v = (φ v).val w := rfl

theorem transpose_map_smul (φ : R hA hV hW) (a : A) (w : W) :
    letI := rightDualAction hA hV
    transpose hA hV hW φ (a • w) = a • transpose hA hV hW φ w :=
  by
    let _ := rightDualAction hA hV
    exact (transpose hA hV hW φ).map_smul a w

/-- Complex-linear packaging on the named canonical Hom modules. -/
def T : R hA hV hW →ₗ[ℂ] L hA hV hW :=
  letI := rightDualAction hA hV
  { toFun := transpose hA hV hW
    map_add' φ φ' := by
      apply NonUnitalModuleHom.ext
      intro w
      exact dual_ext hA.op hV (fun _ => rfl)
    map_smul' c φ := by
      apply NonUnitalModuleHom.ext
      intro w
      apply dual_ext hA.op hV
      intro v
      exact (congrArg (fun q : FullDual hA hW => q w) (rModule_smul_val hA hV hW c φ v)).trans
        (congrArg (fun q : FullDual hA.op hV => q v)
          (lModule_smul_val hA hV hW c (transpose hA hV hW φ) w)).symm }

/-- The full reverse functional w ↦ ψ(w)(v), on the original W. -/
def reverseFull (ψ : L hA hV hW) (v : V) : FullDual hA hW :=
  letI := rightDualAction hA hV
  letI := NondegenerateScalars.complexModule hA hW
  { toFun w := (ψ w).val v
    map_add' w w' := by
      change (ψ (w + w')).val v = (ψ w).val v + (ψ w').val v
      rw [ψ.map_add]
      rfl
    map_smul' c w := by
      change (ψ (c • w)).val v = c • (ψ w).val v
      have h := NondegenerateScalars.map_smul ℂ hA hW (rightDual_isNondegenerate hA hV) ψ c w
      exact (congrArg (fun q : Dual hA.op hV => q.val v) h).trans
        (rightDual_canonical_smul_apply hA hV c (ψ w) v) }

theorem reverseFull_coe (ψ : L hA hV hW) (v : V) :
    ⇑(reverseFull hA hV hW ψ v) = fun w => (ψ w).val v := rfl

@[simp] theorem reverseFull_apply (ψ : L hA hV hW) (v : V) (w : W) :
    reverseFull hA hV hW ψ v w = (ψ w).val v := rfl

/-- A fixing idempotent for v in the original right module fixes the reverse functional. -/
theorem reverseFull_fixed (ψ : L hA hV hW) (v : V)
    (e : Idempotent Aᵐᵒᵖ) (he : (e : Aᵐᵒᵖ) • v = v) (w : W) :
    reverseFull hA hV hW ψ v ((e : Aᵐᵒᵖ).unop • w) = reverseFull hA hV hW ψ v w := by
  let _ := rightDualAction hA hV
  change (ψ ((e : Aᵐᵒᵖ).unop • w)).val v = (ψ w).val v
  rw [ψ.map_smul]
  change (ψ w).val ((e : Aᵐᵒᵖ) • v) = (ψ w).val v
  rw [he]

theorem reverseFull_mem (ψ : L hA hV hW) (v : V) :
    reverseFull hA hV hW ψ v ∈ nondegeneratePart hA.op (FullDual hA hW) := by
  apply (mem_dual_iff hA hW _).mpr
  obtain ⟨e, he⟩ := hV v
  refine ⟨⟨(e : Aᵐᵒᵖ).unop, ?_⟩, ?_⟩
  · have h := congrArg unop e.property.eq
    simpa only [unop_mul, IsIdempotentElem] using h
  · exact reverseFull_fixed hA hV hW ψ v e he

/-- The actual original right intertwiner with the reverse swap formula. -/
def reverse (ψ : L hA hV hW) : R hA hV hW :=
  letI := rightDualAction hA hV
  { toFun v := ⟨reverseFull hA hV hW ψ v, reverseFull_mem hA hV hW ψ v⟩
    map_zero' := by
      apply dual_ext hA hW
      intro w
      let _ := NondegenerateScalars.complexModule hA.op hV
      exact (ψ w).val.map_zero
    map_add' v v' := by
      apply dual_ext hA hW
      intro w
      let _ := NondegenerateScalars.complexModule hA.op hV
      exact (ψ w).val.map_add v v'
    map_smul' a v := by
      apply dual_ext hA hW
      intro w
      change (ψ w).val (a • v) = (ψ (a.unop • w)).val v
      rw [ψ.map_smul]
      rfl }

theorem reverse_val (ψ : L hA hV hW) (v : V) :
    (reverse hA hV hW ψ v).val = reverseFull hA hV hW ψ v := rfl

@[simp] theorem reverse_apply (ψ : L hA hV hW) (v : V) (w : W) :
    (reverse hA hV hW ψ v).val w = (ψ w).val v := rfl

theorem reverse_map_smul (ψ : L hA hV hW) (a : Aᵐᵒᵖ) (v : V) :
    reverse hA hV hW ψ (a • v) = a • reverse hA hV hW ψ v :=
  (reverse hA hV hW ψ).map_smul a v

/-- Reverse complex-linear packaging on precisely the same named scalar modules. -/
def S : L hA hV hW →ₗ[ℂ] R hA hV hW :=
  letI := rightDualAction hA hV
  { toFun := reverse hA hV hW
    map_add' ψ ψ' := by
      apply NonUnitalModuleHom.ext
      intro v
      exact dual_ext hA hW (fun _ => rfl)
    map_smul' c ψ := by
      apply NonUnitalModuleHom.ext
      intro v
      apply dual_ext hA hW
      intro w
      exact (congrArg (fun q : FullDual hA.op hV => q v) (lModule_smul_val hA hV hW c ψ w)).trans
        (congrArg (fun q : FullDual hA hW => q w)
          (rModule_smul_val hA hV hW c (reverse hA hV hW ψ) v)).symm }

/-- The entire additive transpose, with the original Hom carriers. -/
def transposeAdd : R hA hV hW →+ L hA hV hW where
  toFun := transpose hA hV hW
  map_zero' := (T hA hV hW).map_zero
  map_add' := (T hA hV hW).map_add

/-- The entire additive reverse transpose, with the original Hom carriers. -/
def reverseAdd : L hA hV hW →+ R hA hV hW where
  toFun := reverse hA hV hW
  map_zero' := (S hA hV hW).map_zero
  map_add' := (S hA hV hW).map_add

theorem T_toAddMonoidHom :
    (T hA hV hW).toAddMonoidHom = transposeAdd hA hV hW := rfl

theorem S_toAddMonoidHom :
    (S hA hV hW).toAddMonoidHom = reverseAdd hA hV hW := rfl

theorem T_coe : ⇑(T hA hV hW) = transpose hA hV hW := rfl

theorem S_coe : ⇑(S hA hV hW) = reverse hA hV hW := rfl

theorem transposeAdd_coe : ⇑(transposeAdd hA hV hW) = transpose hA hV hW := rfl

theorem reverseAdd_coe : ⇑(reverseAdd hA hV hW) = reverse hA hV hW := rfl

theorem T_apply_hom (φ : R hA hV hW) : T hA hV hW φ = transpose hA hV hW φ := rfl

theorem S_apply_hom (ψ : L hA hV hW) : S hA hV hW ψ = reverse hA hV hW ψ := rfl

theorem T_val (φ : R hA hV hW) (w : W) :
    (T hA hV hW φ w).val = transposeFull hA hV hW φ w := rfl

theorem S_val (ψ : L hA hV hW) (v : V) :
    (S hA hV hW ψ v).val = reverseFull hA hV hW ψ v := rfl

@[simp] theorem T_apply (φ : R hA hV hW) (w : W) (v : V) :
    (T hA hV hW φ w).val v = (φ v).val w := rfl

@[simp] theorem S_apply (ψ : L hA hV hW) (v : V) (w : W) :
    (S hA hV hW ψ v).val w = (ψ w).val v := rfl

theorem T_map_add (φ φ' : R hA hV hW) :
    T hA hV hW (φ + φ') = T hA hV hW φ + T hA hV hW φ' :=
  (T hA hV hW).map_add φ φ'

theorem S_map_add (ψ ψ' : L hA hV hW) :
    S hA hV hW (ψ + ψ') = S hA hV hW ψ + S hA hV hW ψ' :=
  (S hA hV hW).map_add ψ ψ'

theorem T_map_smul (c : ℂ) (φ : R hA hV hW) :
    T hA hV hW (c • φ) = c • T hA hV hW φ :=
  (T hA hV hW).map_smul c φ

theorem S_map_smul (c : ℂ) (ψ : L hA hV hW) :
    S hA hV hW (c • ψ) = c • S hA hV hW ψ :=
  (S hA hV hW).map_smul c ψ

end Carriers

section Naturality

variable {A : Type uA} [NonUnitalRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  {V : Type uV} [AddCommGroup V] [NonUnitalModule Aᵐᵒᵖ V]
  {W : Type uW} [AddCommGroup W] [NonUnitalModule A W]
  {V' : Type uV'} [AddCommGroup V'] [NonUnitalModule Aᵐᵒᵖ V']
  {W' : Type uW'} [AddCommGroup W'] [NonUnitalModule A W']
  (hA : IsIdempotented A) (hV : IsNondegenerate Aᵐᵒᵖ V) (hW : IsNondegenerate A W)
  (hV' : IsNondegenerate Aᵐᵒᵖ V') (hW' : IsNondegenerate A W')
  (f : NonUnitalModuleHom Aᵐᵒᵖ V' V) (g : NonUnitalModuleHom A W' W)

local instance : NonUnitalModule Aᵐᵒᵖ (FullDual hA hW) := fullAction hA hW
local instance : NonUnitalModule Aᵐᵒᵖ (FullDual hA hW') := fullAction hA hW'
local instance : NonUnitalModule Aᵐᵒᵖᵐᵒᵖ (FullDual hA.op hV) := fullAction hA.op hV
local instance : NonUnitalModule Aᵐᵒᵖᵐᵒᵖ (FullDual hA.op hV') := fullAction hA.op hV'

/-- The specified pullback postcomposition and original right precomposition. -/
def Rfg : R hA hV hW →+ R hA hV' hW' where
  toFun φ := (pullback hA hW' hW g).comp (φ.comp f)
  map_zero' := by
    apply NonUnitalModuleHom.ext
    intro v
    exact (pullback hA hW' hW g).map_zero
  map_add' φ φ' := by
    apply NonUnitalModuleHom.ext
    intro v
    exact (pullback hA hW' hW g).map_add (φ (f v)) (φ' (f v))

/-- The specified transported pullback and original left precomposition. -/
def Lfg : L hA hV hW →+ L hA hV' hW' :=
  letI := rightDualAction hA hV
  letI := rightDualAction hA hV'
  { toFun ψ := (fromDoubleOppositeMap (pullback hA.op hV' hV f)).comp (ψ.comp g)
    map_zero' := by
      apply NonUnitalModuleHom.ext
      intro w
      exact (fromDoubleOppositeMap (pullback hA.op hV' hV f)).map_zero
    map_add' ψ ψ' := by
      apply NonUnitalModuleHom.ext
      intro w
      exact (fromDoubleOppositeMap (pullback hA.op hV' hV f)).map_add (ψ (g w)) (ψ' (g w)) }

theorem Rfg_coe :
    ⇑(Rfg hA hV hW hV' hW' f g) =
      fun φ => (pullback hA hW' hW g).comp (φ.comp f) := rfl

theorem Lfg_coe :
    letI := rightDualAction hA hV
    letI := rightDualAction hA hV'
    ⇑(Lfg hA hV hW hV' hW' f g) =
      fun ψ => (fromDoubleOppositeMap (pullback hA.op hV' hV f)).comp (ψ.comp g) := rfl

/-- Equality of the complete original intertwiner, before evaluation. -/
theorem Rfg_apply (φ : R hA hV hW) :
    Rfg hA hV hW hV' hW' f g φ =
      (pullback hA hW' hW g).comp (φ.comp f) := rfl

theorem Lfg_apply (ψ : L hA hV hW) :
    letI := rightDualAction hA hV
    letI := rightDualAction hA hV'
    Lfg hA hV hW hV' hW' f g ψ =
      (fromDoubleOppositeMap (pullback hA.op hV' hV f)).comp (ψ.comp g) := rfl

theorem Rfg_val (φ : R hA hV hW) (v : V') :
    letI := NondegenerateScalars.complexModule hA hW'
    letI := NondegenerateScalars.complexModule hA hW
    (Rfg hA hV hW hV' hW' f g φ v).val =
      (φ (f v)).val.comp (NondegenerateScalars.complexToLinearMap hA hW' hW g) := rfl

theorem Lfg_val (ψ : L hA hV hW) (w : W') :
    letI := NondegenerateScalars.complexModule hA.op hV'
    letI := NondegenerateScalars.complexModule hA.op hV
    (Lfg hA hV hW hV' hW' f g ψ w).val =
      (ψ (g w)).val.comp (NondegenerateScalars.complexToLinearMap hA.op hV' hV f) := rfl

@[simp] theorem Rfg_eval (φ : R hA hV hW) (v : V') (w : W') :
    (Rfg hA hV hW hV' hW' f g φ v).val w = (φ (f v)).val (g w) := rfl

@[simp] theorem Lfg_eval (ψ : L hA hV hW) (w : W') (v : V') :
    (Lfg hA hV hW hV' hW' f g ψ w).val v = (ψ (g w)).val (f v) := rfl

/-- The transpose square is equality of entire bundled additive maps. -/
theorem T_natural :
    (transposeAdd hA hV' hW').comp (Rfg hA hV hW hV' hW' f g) =
      (Lfg hA hV hW hV' hW' f g).comp (transposeAdd hA hV hW) := by
  let _ := rightDualAction hA hV'
  apply AddMonoidHom.ext
  intro φ
  apply NonUnitalModuleHom.ext
  intro w
  exact dual_ext hA.op hV' (fun _ => rfl)

/-- The reverse square is equality of entire bundled additive maps. -/
theorem S_natural :
    (reverseAdd hA hV' hW').comp (Lfg hA hV hW hV' hW' f g) =
      (Rfg hA hV hW hV' hW' f g).comp (reverseAdd hA hV hW) := by
  apply AddMonoidHom.ext
  intro ψ
  apply NonUnitalModuleHom.ext
  intro v
  exact dual_ext hA hW' (fun _ => rfl)

end Naturality

end Langlands.Algebra.NonUnitalModuleDualHomTranspose
