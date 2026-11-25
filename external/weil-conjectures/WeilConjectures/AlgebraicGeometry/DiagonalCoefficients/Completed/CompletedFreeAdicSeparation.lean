/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pur.PurTwistCoefficientRingsSupplement
public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Completed.CompletedAffineFreeLocalDual

/-! # Adic separation of sheafified free representables

Source: the separation step of the completed local generator argument.
(blueprint: lem-sfb-completed-free-adic-separation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-- The finite constant coefficient sheaf has its defining characteristic. -/
private theorem finiteCoefficient_nsmul (l : ℕ) [Fact l.Prime]
    (X : Scheme.{u}) (n : ℕ) (V : X.ProEtᵒᵖ)
    (z : (Scheme.purTwistFiniteRing X l n).obj.obj V) : l ^ (n + 1) • z = 0 := by
  let A := CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1))))
  let η := toSheafify (Scheme.ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)
  have hA : ((l ^ (n + 1) : ℕ) : A) = 0 := by
    apply ULift.ext
    change ((l ^ (n + 1) : ℕ) : ZMod (l ^ (n + 1))) = 0
    exact ZMod.natCast_self _
  have hQ : ((l ^ (n + 1) : ℕ) : (Scheme.purTwistFiniteRing X l n).obj.obj V) = 0 := by
    rw [← map_natCast (η.app V).hom, hA, map_zero]
  rw [nsmul_eq_mul, hQ, zero_mul]

/-- Vanishing in every finite coefficient projection detects locally divisible sections. -/
private theorem coefficient_adicSeparated (l : ℕ) [Fact l.Prime]
    (X : Scheme.{u}) (V : X.ProEtᵒᵖ)
    (z : (Scheme.purTwistZlCompletion X l).obj.obj V)
    (h : ∀ n : ℕ, Presheaf.imageSieve
      ((l ^ (n + 1) • 𝟙 ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
          (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l)))).hom) z ∈
            Scheme.ProEt.topology X V.unop) : z = 0 := by
  let E := sheafToPresheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1} ⋙
    (evaluation X.ProEtᵒᵖ CommRingCat.{u + 1}).obj V
  have hc := isLimitOfPreserves E (limit.isLimit (Scheme.purTwistZlTower X l))
  apply Concrete.isLimit_ext _ hc z 0
  intro n
  change (Scheme.purTwistZlProjection X l n.unop).hom.app V z =
    (Scheme.purTwistZlProjection X l n.unop).hom.app V 0
  rw [map_zero]
  apply (Scheme.purTwistFiniteRing X l n.unop).isSeparated V.unop _ (h n.unop)
  rintro W f ⟨y, hy⟩
  change l ^ (n.unop + 1) • y =
    (Scheme.purTwistZlCompletion X l).obj.map f.op z at hy
  rw [map_zero, ← NatTrans.naturality_apply
    (Scheme.purTwistZlProjection X l n.unop).hom f.op z, ← hy, map_nsmul]
  exact finiteCoefficient_nsmul l X n.unop (op W) _

/-- A local linear functional sends the given divisibility covers to coefficient covers. -/
private theorem localDual_zero (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (P : SheafOfModules.{u + 1}
      (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l)))
    (V : X.ProEtᵒᵖ) (x : P.val.obj V)
    (h : ∀ n : ℕ, Presheaf.imageSieve
      ((l ^ (n + 1) • 𝟙 ((SheafOfModules.toSheaf _).obj P)).hom) x ∈
        Scheme.ProEt.topology X V.unop)
    (W : X.ProEt) (f : W ⟶ V.unop)
    (φ : P.over W ⟶ SheafOfModules.unit
      ((Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l)).over W)) :
    φ.val.app (op (Over.mk (𝟙 W))) (P.val.map f.op x) = 0 := by
  apply coefficient_adicSeparated l X (op W)
  intro n
  refine (Scheme.ProEt.topology X).superset_covering ?_
    ((Scheme.ProEt.topology X).pullback_stable f (h n))
  rintro Z g ⟨y, hy⟩
  refine ⟨φ.val.app (op (Over.mk g)) y, ?_⟩
  change l ^ (n + 1) • φ.val.app (op (Over.mk g)) y =
    (Scheme.purTwistZlCompletion X l).obj.map g.op
      (φ.val.app (op (Over.mk (𝟙 W))) (P.val.map f.op x))
  change l ^ (n + 1) • y = P.val.map (g ≫ f).op x at hy
  rw [← map_nsmul, hy, op_comp, P.val.map_comp_apply]
  exact PresheafOfModules.naturality_apply φ.val (Over.homMk g (by simp) :
    Over.mk g ⟶ Over.mk (𝟙 W)).op _

/-- A locally infinitely ell-divisible section of the free completed-coefficient
sheaf on a pro-affine etale representable vanishes.

Source: the separation step of lem-sfb-diagonal-completed-free-generator, corrected
by restricting to the covering basis of pro-affine etale representables.
(blueprint: lem-sfb-completed-free-adic-separation).

Proof: every local linear functional into the completed ring sends the section to
a locally infinitely divisible coefficient. Its projection to Z/l^(n+1) is zero,
since this coefficient sheaf is killed by l^(n+1). Separatedness descends the local
vanishing, and the projections of the defining limit jointly detect zero. Thus all
local linear tests vanish. The local-dual detection lemma for pro-affine etale
representables now gives the result. No countable intersection of covering sieves
is used. The argument includes zero sections and empty test objects.

The earlier version for arbitrary pro-etale representables was false: gluing two
copies of a Boolean convergent-sequence spectrum along its isolated points gives
a non-quasi-separated counterexample. The change record explains the correction
and the descent preserving the parent statement. -/
theorem completedFree_adicSeparated (l : ℕ) [Fact l.Prime]
    (X : Scheme.{u}) (U : X.ProEtᵒᵖ) (hU : proAffineEtale U.unop.hom) :
    let R := Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l)
    let P := (PresheafOfModules.sheafification (𝟙 R.obj)).obj
      ((PresheafOfModules.free R.obj).obj (uliftYoneda.{u + 1}.obj U.unop))
    ∀ (V : X.ProEtᵒᵖ) (x : P.val.obj V),
      (∀ n : ℕ, Presheaf.imageSieve
        ((l ^ (n + 1) • 𝟙 ((SheafOfModules.toSheaf R).obj P)).hom) x ∈
          Scheme.ProEt.topology X V.unop) → x = 0 := by
  intro R P V x hx
  apply completedAffineFree_localDual_detect l X U hU V x
  intro W f φ
  exact localDual_zero l X P V x hx W f φ

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
