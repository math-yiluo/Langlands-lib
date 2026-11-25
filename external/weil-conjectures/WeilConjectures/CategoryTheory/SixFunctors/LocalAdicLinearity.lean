/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SixFunctors.CompletedCoefficientLocalIntegers

/-! # The local integer approximation criterion for linearity

Source: the action-defect argument for completed coefficients.
(blueprint: lem-sfb-local-adic-linearity).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w t
open CategoryTheory Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace CategoryTheory

/-- An additive sheaf map is linear when coefficients are locally integers modulo
all powers and the target is separated for local divisibility by those powers.

Source: the integer-modulo-powers criterion in
WeilConjectures/SixFunctors/ProEtale/Adic/PadicIntSheafLinear.lean.
(blueprint: lem-sfb-local-adic-linearity).

Proof: subtract the two sides. On a covering sieve write r=a+l^(n+1)b.
Naturality and additivity identify the restricted defect with l^(n+1) times
g(bx)-c(b)g(x); the integer terms cancel because c preserves integers and g
preserves integer multiples. Thus every power-image sieve of the defect covers.
The separation hypothesis makes the defect zero. -/
theorem linearity_of_localIntegers_adicSeparated
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (l : ℕ) {S R : Sheaf J RingCat.{w}} (c : S ≅ R)
    (N : SheafOfModules.{t} S) (P : SheafOfModules.{t} R)
    (g : (SheafOfModules.toSheaf _).obj N ⟶ (SheafOfModules.toSheaf _).obj P)
    (hlocal : ∀ (n : ℕ) (V : Cᵒᵖ) (r : S.obj.obj V),
      integerApproximationSieve S (l ^ (n + 1)) r ∈ J V.unop)
    (hsep : ∀ (V : Cᵒᵖ) (z : P.val.obj V),
      (∀ n : ℕ, Presheaf.imageSieve
        ((l ^ (n + 1) • 𝟙 ((SheafOfModules.toSheaf R).obj P)).hom) z ∈ J V.unop) →
        z = 0)
    (V : Cᵒᵖ) (r : S.obj.obj V) (x : N.val.obj V) :
    g.hom.app V (r • x) =
      @SMul.smul _ (P.val.obj V) inferInstance (c.hom.hom.app V r) (g.hom.app V x) := by
  let gv : N.val.obj V →+ P.val.obj V := (g.hom.app V).hom
  change gv (r • x) = (c.hom.hom.app V r) • gv x
  apply sub_eq_zero.mp
  apply hsep V
  intro n
  refine J.superset_covering ?_ (hlocal n V r)
  rintro W f ⟨a, b, hb⟩
  let gw : N.val.obj (op W) →+ P.val.obj (op W) := (g.hom.app (op W)).hom
  let nw : N.val.obj V →+ N.val.obj (op W) := (N.val.map f.op).hom.toAddMonoidHom
  let pw : P.val.obj V →+ P.val.obj (op W) := (P.val.map f.op).hom.toAddMonoidHom
  let y := nw x
  have hg (z : N.val.obj V) : pw (gv z) = gw (nw z) :=
    (NatTrans.naturality_apply g.hom f.op z).symm
  have hn : nw (r • x) = S.obj.map f.op r • y := N.val.map_smul f.op r x
  have hp : pw (c.hom.hom.app V r • gv x) =
      R.obj.map f.op (c.hom.hom.app V r) • pw (gv x) :=
    P.val.map_smul f.op (c.hom.hom.app V r) (gv x)
  refine ⟨gw (b • y) - (c.hom.hom.app (op W) b) • gw y, ?_⟩
  change l ^ (n + 1) • (gw (b • y) - (c.hom.hom.app (op W) b) • gw y) =
    pw (gv (r • x) - (c.hom.hom.app V r) • gv x)
  rw [map_sub, hg (r • x), hn, hp,
    ← NatTrans.naturality_apply c.hom.hom f.op r, hg x]
  simp only [hb]
  simp only [y, add_smul, map_add, map_intCast, map_nsmul, Int.cast_smul_eq_zsmul,
    smul_assoc]
  simp only [smul_sub, map_zsmul]
  abel

end CategoryTheory
