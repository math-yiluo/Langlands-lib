/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower
public import WeilConjectures.RingTheory.KoszulRegularSequence
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.AlgebraicGeometry.Modules.Dual

public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
import WeilConjectures.AlgebraicGeometry.SelfTorConormalDualChartIso
import WeilConjectures.RingTheory.SelfTorConormalRegularIso

/-! # The dual exterior-to-self-Tor comparison

Source: Stacks Project, Tags 09PQ, 062I, 0BQY and 06YH.
(blueprint: lem-sc-self-tor-conormal-dual-chart). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry

/-- The dual of the conormal-to-self-Tor map is invertible on regular affine charts.

Source: Stacks Project, more-algebra.tex, lemma-H1-regular-quasi-regular (062I),
dpa.tex, lemma-divided-powers-on-tor (09PQ), and duality.tex,
lemma-regular-ideal-ext (0BQY), the augmented Koszul dg algebra;
06YH for derived tensor. (blueprint: lem-sc-self-tor-conormal-dual-chart).

Proof: For B = i_*O_Z, the derived tensor B tensor^L B is a derived B-algebra.
Its degree-minus-one cohomology is the conormal module: tensor the exact sequence
0 -> I -> A -> A/I -> 0 with A/I; the boundary identifies Tor_1 with I/I².
Products of degree-minus-one
classes are alternating by 09PQ: compute in a Tate dg algebra resolution, where
odd generators square to zero. Resolution comparison preserves products and makes
these maps independent of the resolution. Localization is flat and preserves this
construction; thus the affine maps glue as morphisms of module sheaves on Z.
The exterior universal property gives a global map
from exterior^n(i*ker(i)) to the pulled-back degree-minus-n self-Tor sheaf.
The quotient action identifies ordinary pullback of these B-modules with the same
modules on Z. Dualizing this map gives dualMap τ. These constructions commute with open
restriction and are defined on singular charts as well; no arbitrary local frame
is glued. On a regular affine chart the augmented Koszul dg algebra is a resolution.
Tensor with B: every coefficient f_j vanishes, so its differential is zero and its
nth term is the nth exterior power of B^m. By 062I the degree-one generators are
exactly a basis of I/I². Products send each increasing conormal wedge to its Koszul
wedge, so the exterior-to-Tor map is an isomorphism there. Its dual is an isomorphism
on the whole over site. Degree zero is the unit B; above m both terms vanish.
The same argument includes m=0, B=0 and empty inverse-image charts. No derived
category on Z or on a chart is required: compute tensor and homology on Y in the
supplied universe, then apply ordinary tensor pullback. -/
theorem selfTor_conormal_dual_chart
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [IsClosedImmersion i] (n : ℕ) :
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let S := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let Q := (Scheme.Modules.tensorPullback i).obj
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (-(n : ℤ))).obj
          (S.obj B ⊗ S.obj B))
    ∃ τ : Scheme.Modules.exteriorPower
      ((Scheme.Modules.tensorPullback i).obj i.ker.toModules) n ⟶ Q,
      ∀ (V : Z.Opens) (U : Y.affineOpens)
        (_hU : ∃ (m : ℕ) (f : Fin m → Γ(Y, U.1)),
          Ideal.span (Set.range f) = i.ker.ideal U ∧
            RingTheory.Sequence.IsKoszulRegular f),
        IsIso (((Scheme.Modules.restrictFunctor V.ι).map (Scheme.Modules.dualMap τ)).over
          (V.ι ⁻¹ᵁ (i ⁻¹ᵁ U.1))) := by
  obtain ⟨τ, hτ⟩ := selfTor_conormal_dual_chart_iso i n
  refine ⟨τ, ?_⟩
  intro V U hU
  obtain ⟨r, f, hf, hreg⟩ := hU
  have hc := selfTorConormalComparison_isIso (Γ(Y, U.1) : Type u)
    (i.ker.ideal U) n r f hf hreg
  obtain ⟨a, b, hab⟩ := hτ V U
  rw [hab]
  infer_instance

end AlgebraicGeometry
