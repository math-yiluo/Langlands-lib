/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Adjunction.Limits

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- The spectrum diagram on the upper tail, with its maps to the fixed stage.
(blueprint: new-affine-chart-upper-tail-limit-data)
-/
noncomputable def upperTailSpectrumOver {I : Type u} [Preorder I]
    (R : I ⥤ CommRingCat.{u}) (i : I) :
    ({j : I // i ≤ j})ᵒᵖ ⥤ Over (Spec (R.obj i)) where
  obj j := Over.mk (Spec.map (R.map (homOfLE j.unop.property)))
  map {j k} h := Over.homMk ((R.op ⋙ Scheme.Spec).map
    (homOfLE (show k.unop.val ≤ j.unop.val from leOfHom h.unop)).op) (by
      change Spec.map (R.map _) ≫ Spec.map (R.map _) = Spec.map (R.map _)
      rw [← Spec.map_comp, ← R.map_comp]
      rfl)
  map_id j := by ext; simp
  map_comp h k := by
    ext
    change Spec.map (R.map _) = Spec.map (R.map _) ≫ Spec.map (R.map _)
    rw [← Spec.map_comp, ← R.map_comp]
    rfl

/-- The given spectrum cone restricted to the upper tail and lifted to the slice.
(blueprint: new-affine-chart-upper-tail-limit-data)
-/
noncomputable def upperTailSpectrumOverCone {I : Type u} [Preorder I]
    (R : I ⥤ CommRingCat.{u}) (c : Cone (R.op ⋙ Scheme.Spec)) (i : I) :
    Cone (upperTailSpectrumOver R i) where
  pt := Over.mk (c.π.app (op i))
  π.app j := Over.homMk (c.π.app (op j.unop.val)) (c.w _)
  π.naturality j k h := by
    ext
    change c.π.app (op k.unop.val) = c.π.app (op j.unop.val) ≫
      (R.op ⋙ Scheme.Spec).map (homOfLE (leOfHom h.unop)).op
    exact (c.w _).symm

/-- The actual diagram obtained by pulling the upper-tail spectra back to A.
(blueprint: new-affine-chart-upper-tail-limit-data)
-/
noncomputable def upperTailChartDiagram {I : Type u} [Preorder I]
    (R : I ⥤ CommRingCat.{u}) (i : I) {A : Scheme.{u}} (g : A ⟶ Spec (R.obj i)) :
    ({j : I // i ≤ j})ᵒᵖ ⥤ Scheme.{u} :=
  upperTailSpectrumOver R i ⋙ Over.pullback g ⋙ Over.forget A

/-- The actual pulled-back cone, without choosing any existential witness.
(blueprint: new-affine-chart-upper-tail-limit-data)
-/
noncomputable def upperTailChartCone {I : Type u} [Preorder I]
    (R : I ⥤ CommRingCat.{u}) (c : Cone (R.op ⋙ Scheme.Spec)) (i : I)
    {A : Scheme.{u}} (g : A ⟶ Spec (R.obj i)) : Cone (upperTailChartDiagram R i g) :=
  (Over.forget A).mapCone ((Over.pullback g).mapCone (upperTailSpectrumOverCone R c i))

/-- The explicitly constructed upper-tail base-change cone is limiting.
Source: Stacks Project, Limits Tag 01ZR, affine case; Tags 0095 and 0097.
(blueprint: new-affine-chart-upper-tail-limit-data).

Proof: The inclusion J = {j | i ≤ j} into I is final. For every k choose a
common upper bound of i and k. Any two such upper bounds admit a further common
upper bound, so each comma category is nonempty and connected. Hence the opposite
inclusion is initial, and restriction of the limiting cone c to J opposite is
limiting. Its lift upperTailSpectrumOverCone to Over(Spec(R_i)) is limiting,
because the forgetful functor reflects limits and its underlying cone is precisely
that restriction. Over.pullback g is right adjoint to Over.map g, and therefore
preserves limits. Finally J contains i and is directed, so J opposite is connected;
the forgetful functor Over(A) -> Scheme preserves these connected limits. Its image
is exactly upperTailChartCone. Neither affineness nor a choice of new data is
needed for this universal-property argument. -/
theorem upperTailChartCone_isLimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u})
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c)
    (i : I) {A : Scheme.{u}} (g : A ⟶ Spec (R.obj i)) :
    Nonempty (IsLimit (upperTailChartCone R c i g)) := by
  let J := {j : I // i ≤ j}
  let : Nonempty J := ⟨⟨i, le_rfl⟩⟩
  let : IsDirectedOrder J := ⟨by
    intro j k
    obtain ⟨l, hj, hk⟩ := exists_ge_ge j.val k.val
    exact ⟨⟨l, j.property.trans hj⟩, hj, hk⟩⟩
  let t : J ⥤ I := (Subtype.mono_coe (fun j : I ↦ i ≤ j)).functor
  let : t.Final := (Monotone.final_functor_iff _).mpr (by
    intro k
    obtain ⟨l, hi, hk⟩ := exists_ge_ge i k
    exact ⟨⟨l, hi⟩, hk⟩)
  have hrestrict : IsLimit (c.whisker t.op) :=
    (Functor.Initial.isLimitWhiskerEquiv t.op c).symm hc
  let : IsConnected Jᵒᵖ := IsCofiltered.isConnected _
  let e : (upperTailSpectrumOver R i ⋙ Over.forget (Spec (R.obj i))) ≅
      t.op ⋙ R.op ⋙ Scheme.Spec := NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
        intro j k h
        simp only [Functor.comp_map, Over.forget_map, upperTailSpectrumOver,
          Iso.refl_hom, Category.comp_id, Category.id_comp]
        congr 2)
  have hbase : IsLimit ((Over.forget (Spec (R.obj i))).mapCone
      (upperTailSpectrumOverCone R c i)) :=
    IsLimit.equivOfNatIsoOfIso e _ _ (Cone.ext (Iso.refl _)) hrestrict
  have hover : IsLimit (upperTailSpectrumOverCone R c i) :=
    isLimitOfReflects (Over.forget _) hbase
  exact ⟨isLimitOfPreserves (Over.forget A) (isLimitOfPreserves (Over.pullback g) hover)⟩

end AlgebraicGeometry
