/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PicardFunctor
public import WeilConjectures.AlgebraicGeometry.TensorPullback
import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction

/-!
# Persistence of zero sections under further base change

Source: Stacks Project, Limits, Tag 01ZR (3), affine part of the first proof;
Algebra, Tags 05N7 (3) and 05LI (1).
(blueprint: lem-pc-section-base-change-zero-persists).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem unit_zero_comp {X Y Z : Scheme.{u}}
    (g : Z ⟶ Y) (h : Y ⟶ X) (q : Z ⟶ X) (w : g ≫ h = q)
    (M : X.Modules) (V : X.Opens) (y : Γ(M, V))
    (a : Scheme.Modules.tensorPullback h ⊣ Scheme.Modules.pushforward h)
    (b : Scheme.Modules.tensorPullback q ⊣ Scheme.Modules.pushforward q)
    (hy : (a.unit.app M).val.app (op V) y = 0) :
    (b.unit.app M).val.app (op V) y = 0 := by
  classical
  change (a.unit.app M).app V y = 0 at hy
  change (b.unit.app M).app V y = 0
  let ag := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)
  let ac := a.comp ag
  let e := Scheme.Modules.pushforwardComp g h ≪≫ Scheme.Modules.pushforwardCongr w
  let bc := b.ofNatIsoRight e.symm
  have hz : (ac.unit.app M).app V y = 0 := by
    change (ag.unit.app ((Scheme.Modules.tensorPullback h).obj M)).app (h ⁻¹ᵁ V)
      ((a.unit.app M).app V y) = 0
    rw [hy]
    exact map_zero _
  have hu := ac.unit_leftAdjointUniq_hom_app bc M
  have hv := congrArg (fun z ↦ z.app V y) hu
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at hv
  rw [hz, map_zero] at hv
  have hbz : (bc.unit.app M).app V y = 0 := hv.symm
  have he : (e.hom.app ((Scheme.Modules.tensorPullback q).obj M)).app V
      ((bc.unit.app M).app V y) = (b.unit.app M).app V y := by
    change (e.hom.app ((Scheme.Modules.tensorPullback q).obj M)).app V
      ((e.inv.app ((Scheme.Modules.tensorPullback q).obj M)).app V
        ((b.unit.app M).app V y)) = _
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app,
      Iso.inv_hom_id_app]
    rfl
  rw [hbz, map_zero] at he
  exact he.symm

/-- Zero pullback of a section remains zero under a further base change.
Source: Stacks Project, Sheaves, Tags 0095 and 0096; Limits, Tag 01ZR (3).
(blueprint: lem-pc-section-base-change-zero-persists).

Proof: for l ≤ k the k-to-j base-change map is the composite of the k-to-l
and l-to-j base-change maps, by pullback uniqueness and functoriality of R.
Tensor pullback along this composite is canonically isomorphic to the composite
of tensor pullbacks. The unit of the composite adjunction is the first unit
followed by pushforward of the second unit. On the inverse image of U its
value on y is therefore the further pullback of the given zero section, which
is zero by linearity. The composite-pullback isomorphism transports this unit
to a unit for the k-to-j tensor pullback. Uniqueness of left adjoints compares
that adjunction to the supplied one: their units differ by an isomorphism of
the pullback object. Its section maps preserve zero. No quasi-coherence,
finiteness or affineness is used; empty opens and identity transitions obey
the same unit equation. -/
theorem section_baseChange_zero_persists
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u})
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    (j : I) (hij : i ≤ j)
    (G : (pullback f (Spec.map (R.map (homOfLE hij)))).Modules)
    (U : Xi.Opens)
    (y : Γ(G, (pullback.fst f (Spec.map (R.map (homOfLE hij)))) ⁻¹ᵁ U))
    (adjstage : ∀ (k : I) (hjk : j ≤ k),
      let g := baseChangeMap f
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
        (Over.homMk (Spec.map (R.map (homOfLE hjk)))
          (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
      Scheme.Modules.tensorPullback g ⊣ Scheme.Modules.pushforward g)
    (l : I) (hjl : j ≤ l)
    (hy : ((adjstage l hjl).unit.app G).val.app
      (op ((pullback.fst f (Spec.map (R.map (homOfLE hij)))) ⁻¹ᵁ U)) y = 0) :
    ∀ (k : I) (hjk : j ≤ k), l ≤ k →
      ((adjstage k hjk).unit.app G).val.app
        (op ((pullback.fst f (Spec.map (R.map (homOfLE hij)))) ⁻¹ᵁ U)) y = 0 := by
  intro k hjk hlk
  let Tj := Over.mk (Spec.map (R.map (homOfLE hij)))
  let Tl := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjl))))
  let Tk := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk))))
  let al : Tl ⟶ Tj := Over.homMk (Spec.map (R.map (homOfLE hjl)))
    (by dsimp [Tl, Tj]; rw [← Spec.map_comp, ← R.map_comp]; rfl)
  let ak : Tk ⟶ Tj := Over.homMk (Spec.map (R.map (homOfLE hjk)))
    (by dsimp [Tk, Tj]; rw [← Spec.map_comp, ← R.map_comp]; rfl)
  let alk : Tk ⟶ Tl := Over.homMk (Spec.map (R.map (homOfLE hlk)))
    (by dsimp [Tk, Tl]; rw [← Spec.map_comp, ← R.map_comp]; rfl)
  have w : baseChangeMap f alk ≫ baseChangeMap f al = baseChangeMap f ak := by
    rw [← baseChangeMap_comp]
    congr 1
    apply Over.OverMorphism.ext
    change Spec.map (R.map (homOfLE hlk)) ≫ Spec.map (R.map (homOfLE hjl)) =
      Spec.map (R.map (homOfLE hjk))
    rw [← Spec.map_comp, ← R.map_comp]
    rfl
  exact unit_zero_comp (baseChangeMap f alk) (baseChangeMap f al)
    (baseChangeMap f ak) w G _ y (adjstage l hjl) (adjstage k hjk) hy

end AlgebraicGeometry
