/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pur.PurTwistCoefficientRingsSupplement
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Completed.CompletedAffineFreePresheafLocalDual
public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-! # Local linear tests on an affine completed free representable

Source: the finite-support argument for local completed generators, with pro-affine etale
representables in place of arbitrary representables.
(blueprint: lem-sfb-completed-affine-free-local-dual).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-- Local linear functionals into the completed coefficient ring detect sections
of the sheafified free module on a pro-affine etale representable.

Source: the finite-support step of lem-sfb-completed-free-adic-separation, corrected
by restricting generators to inverse limits of affine etale schemes; the canonical
clopen-neighborhood localizations of Stacks 097C give the closed restrictions below.
(blueprint: lem-sfb-completed-affine-free-local-dual).

Proof: locally on an affine test object V, lift the section to a finite sum
of basis maps s_j : V to U with completed coefficients a_j. Use the given small
cofiltered presentation U = lim U_i. Each U_i is absolutely affine, hence separated
over X, and etale over X. The graph of s_j at stage i in U_i times_X V is therefore
open and closed. Its characteristic function, with values 0 and 1 in the completed
ring, defines a natural map from the representable to that ring on the slice over V.
The free-module and sheafification adjunctions extend it to a local linear test.

The tests vanish by hypothesis. Their values are the sums of a_j weighted by the
clopen equalities of stage maps. Identify completed coefficients on V with
continuous functions from its profinite connected-component space to Z_l: each
finite constant sheaf is the sheaf of locally constant functions, and limits are
computed on sections. At a component c, cofilteredness supplies one stage separating
all the finitely many distinct limit images of the basis maps at c. Its tests give
zero for the sum of a_j in each equality class at c.

There are finitely many possible equality patterns. On the closure of a pattern's
stratum every within-class equality persists: equality of limit maps is the
intersection of their clopen stage equalities. Every class coefficient sum also
remains zero, by continuity into the Hausdorff ring Z_l. Restrict the affine V to
each such closed component subset by the canonical colimit of localizations at
idempotents of its clopen neighborhoods. These restrictions are ind-Zariski, hence
weakly etale, and their finite family covers V. On each restriction, basis maps
within each pattern class agree and the corresponding coefficient sum is zero.
Thus the finite free-presheaf sum vanishes there. Sheaf separatedness gives x = 0.
Empty support and the empty test object give the zero sum and empty covering.
No countable intersection of arbitrary covering sieves is used. -/
theorem completedAffineFree_localDual_detect (l : ℕ) [Fact l.Prime]
    (X : Scheme.{u}) (U : X.ProEtᵒᵖ) (hU : proAffineEtale U.unop.hom) :
    let R := Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l)
    let P := (PresheafOfModules.sheafification (𝟙 R.obj)).obj
      ((PresheafOfModules.free R.obj).obj (uliftYoneda.{u + 1}.obj U.unop))
    ∀ (V : X.ProEtᵒᵖ) (x : P.val.obj V),
      (∀ (W : X.ProEt) (f : W ⟶ V.unop)
        (φ : P.over W ⟶ SheafOfModules.unit (R.over W)),
        φ.val.app (op (Over.mk (𝟙 W))) (P.val.map f.op x) = 0) → x = 0 := by
  dsimp
  intro V x hx
  let R := Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l)
  let F := (PresheafOfModules.free R.obj).obj
    (uliftYoneda.{u + 1}.obj U.unop)
  let P := (PresheafOfModules.sheafification (𝟙 R.obj)).obj F
  let η := (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app F
  let ηp := (PresheafOfModules.toPresheaf R.obj).map η
  have hη : Presheaf.IsLocallySurjective (Scheme.ProEt.topology X) ηp := by
    change Presheaf.IsLocallySurjective (Scheme.ProEt.topology X)
      (CategoryTheory.toSheafify (Scheme.ProEt.topology X) F.presheaf)
    infer_instance
  apply P.isSheaf.isSeparated _ _
    (Presheaf.imageSieve_mem (Scheme.ProEt.topology X) ηp x)
  intro W f hf
  change P.val.map f.op x = P.val.map f.op 0
  obtain ⟨y, hy⟩ := hf
  change (η.app (op W) y) = P.val.map f.op x at hy
  by_cases hy0 : η.app (op W) y = 0
  · rw [← hy, hy0]
    simp only [map_zero]
  · obtain ⟨φ, hφ⟩ := completedAffineFree_presheaf_localDual l X U hU W y hy0
    have hz := hx W f φ
    rw [← hy] at hz
    exact False.elim (hφ hz)

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
