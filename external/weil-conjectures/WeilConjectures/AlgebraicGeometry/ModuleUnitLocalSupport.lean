/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits

/-! # Local finite support for one section

Source: Stacks Project, Modules, Tags 01BB (first paragraph of the proof) and 01AH (2).
(blueprint: lem-weil-pbc-module-unit-local-support).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

private def finiteSubsetDiagram (I : Type u) : Finset I ⥤ Type u where
  obj S := S
  map f := ↾(fun i ↦ ⟨i.val, (leOfHom f) i.property⟩)

private def finiteSubsetCocone (I : Type u) : Limits.Cocone (finiteSubsetDiagram I) where
  pt := I
  ι := { app := fun _ ↦ ↾Subtype.val }

private noncomputable def finiteSubsetIsColimit (I : Type u) :
    Limits.IsColimit (finiteSubsetCocone I) := by
  classical
  refine
    { desc := fun c ↦ ↾(fun i ↦ c.ι.app {i} ⟨i, by simp⟩)
      fac := ?_
      uniq := ?_ }
  · intro c S
    ext i
    have h := congrArg (fun f ↦ f ⟨i.val, by simp⟩)
      (c.w (homOfLE (Finset.singleton_subset_iff.mpr i.property)))
    exact h.symm
  · intro c m hm
    ext i
    exact congrArg (fun f ↦ f ⟨i, by simp⟩) (hm {i})

set_option backward.isDefEq.respectTransparency false in
private theorem colimit_comparison_locally_surjective
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {K : Type u} [SmallCategory K]
    (D : K ⥤ SheafOfModules.{u} R) (c : Limits.Cocone D) (hc : Limits.IsColimit c) :
    Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf R.obj).map
        (Limits.colimit.desc (D ⋙ SheafOfModules.forget R)
          ((SheafOfModules.forget R).mapCocone c))) := by
  let U := SheafOfModules.forget R
  let L := PresheafOfModules.sheafification (𝟙 R.obj)
  let adj : L ⊣ U := PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)
  let P := Limits.colimit.cocone (D ⋙ U)
  let hP := Limits.colimit.isColimit (D ⋙ U)
  let hQ := Limits.isColimitOfPreserves L hP
  let e : (D ⋙ U) ⋙ L ≅ D := Functor.isoWhiskerLeft D (asIso adj.counit)
  let hcE := (Limits.IsColimit.precomposeHomEquiv e c).symm hc
  let θ := hQ.coconePointUniqueUpToIso hcE
  let k := adj.unit.app P.pt ≫ U.map θ.hom
  have hk (i : K) : P.ι.app i ≫ k = U.map (c.ι.app i) := by
    dsimp only [k]
    have hn := adj.unit.naturality (P.ι.app i)
    change P.ι.app i ≫ adj.unit.app P.pt =
      adj.unit.app (U.obj (D.obj i)) ≫ U.map (L.map (P.ι.app i)) at hn
    rw [← Category.assoc, hn, Category.assoc, ← U.map_comp]
    have hθ := hQ.comp_coconePointUniqueUpToIso_hom hcE i
    change L.map (P.ι.app i) ≫ θ.hom = adj.counit.app (D.obj i) ≫ c.ι.app i at hθ
    rw [hθ, U.map_comp, ← Category.assoc, adj.right_triangle_components]
    exact Category.id_comp _
  have heq : Limits.colimit.desc (D ⋙ U) (U.mapCocone c) = k := by
    apply hP.hom_ext
    intro i
    exact (hP.fac _ i).trans (hk i).symm
  rw [heq, Functor.map_comp]
  have : Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf R.obj).map (adj.unit.app P.pt)) := by
    change Presheaf.IsLocallySurjective J (CategoryTheory.toSheafify J P.pt.presheaf)
    infer_instance
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private noncomputable def unitFromTerminalSection
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} (M : SheafOfModules.{u} R)
    (Z : C) (hZ : Limits.IsTerminal Z) (s : M.val.obj (Opposite.op Z)) : unit R ⟶ M :=
  M.unitHomEquiv.symm (M.val.sectionsMk
    (fun T ↦ M.val.map (hZ.from T.unop).op s)
    (fun {T T'} f ↦ by
      rw [← PresheafOfModules.map_comp_apply]
      rw [show (hZ.from T.unop).op ≫ f = (hZ.from T'.unop).op from
        congrArg Quiver.Hom.op (hZ.hom_ext _ _)]))

set_option backward.isDefEq.respectTransparency false in
private theorem unit_hom_ext_terminal
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M : SheafOfModules.{u} R}
    (Z : C) (hZ : Limits.IsTerminal Z) (a b : unit R ⟶ M)
    (h : a.val.app (Opposite.op Z) (1 : R.obj.obj (Opposite.op Z)) =
      b.val.app (Opposite.op Z) (1 : R.obj.obj (Opposite.op Z))) : a = b := by
  apply M.unitHomEquiv.injective
  apply PresheafOfModules.sections_ext
  intro T
  have ha := (M.unitHomEquiv a).property (hZ.from T.unop).op
  have hb := (M.unitHomEquiv b).property (hZ.from T.unop).op
  exact ha.symm.trans ((congrArg (M.val.map (hZ.from T.unop).op) h).trans hb)

set_option backward.isDefEq.respectTransparency false in
private theorem unitFromTerminalSection_apply
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} (M : SheafOfModules.{u} R)
    (Z : C) (hZ : Limits.IsTerminal Z) (s : M.val.obj (Opposite.op Z)) :
    (unitFromTerminalSection M Z hZ s).val.app (Opposite.op Z)
      (1 : R.obj.obj (Opposite.op Z)) = s := by
  change (M.unitHomEquiv (M.unitHomEquiv.symm _)).val (Opposite.op Z) = s
  rw [Equiv.apply_symm_apply]
  change M.val.map (hZ.from Z).op s = s
  rw [show hZ.from Z = 𝟙 Z from hZ.hom_ext _ _, op_id]
  simp only [PresheafOfModules.map_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem exists_unit_local_colimit_lift
    (X : Scheme.{u}) (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (V U : X.Opens) (hUV : U ≤ V)
    {K : Type u} [SmallCategory K] [IsFiltered K]
    (D : K ⥤ SheafOfModules.{u} (R.over V)) (c : Limits.Cocone D) (hc : Limits.IsColimit c)
    (b : unit (R.over U) ⟶ (overMap R (homOfLE hUV)).obj c.pt) (x : U) :
    ∃ (W : X.Opens) (hWU : W ≤ U), (x : X) ∈ W ∧ ∃ (i : K)
      (a : unit (R.over W) ⟶
        (overMap R (homOfLE (hWU.trans hUV))).obj (D.obj i)),
      a ≫ (overMap R (homOfLE (hWU.trans hUV))).map (c.ι.app i) =
        (overMap R (homOfLE hWU)).map b := by
  classical
  let F := D ⋙ SheafOfModules.forget (R.over V)
  let P := Limits.colimit F
  let k : P ⟶ c.pt.val := Limits.colimit.desc F ((SheafOfModules.forget (R.over V)).mapCocone c)
  let q := (PresheafOfModules.toPresheaf (R.over V).obj).map k
  have : Presheaf.IsLocallySurjective ((Opens.grothendieckTopology X).over V) q :=
    colimit_comparison_locally_surjective (R.over V) D c hc
  let T : Over V := Over.mk (homOfLE hUV)
  let s : c.pt.val.obj (Opposite.op T) :=
    b.val.app (Opposite.op (Over.mk (𝟙 U))) (1 : R.obj.obj (Opposite.op U))
  have hcover := Presheaf.imageSieve_mem ((Opens.grothendieckTopology X).over V) q s
  rw [GrothendieckTopology.mem_over_iff, Opens.mem_grothendieckTopology] at hcover
  obtain ⟨W, f, hf, hxW⟩ := hcover x.val x.property
  have hf' := (Sieve.overEquiv_iff _ _).mp hf
  obtain ⟨t, ht⟩ := hf'
  let A : Over V := Over.mk (f ≫ homOfLE hUV)
  let E := PresheafOfModules.evaluation (R.over V).obj (Opposite.op A) ⋙ CategoryTheory.forget _
  have : Limits.PreservesColimit F E := by dsimp [E]; infer_instance
  obtain ⟨i, a₀, ha₀⟩ := Limits.Types.jointly_surjective (F ⋙ E)
    (Limits.isColimitOfPreserves E (Limits.colimit.isColimit F)) t
  let hWU : W ≤ U := leOfHom f
  let N := (overMap R (homOfLE (hWU.trans hUV))).obj (D.obj i)
  let a : unit (R.over W) ⟶ N :=
    unitFromTerminalSection N (Over.mk (𝟙 W)) Over.mkIdTerminal a₀
  refine ⟨W, hWU, hxW, i, a, ?_⟩
  apply unit_hom_ext_terminal (Over.mk (𝟙 W)) Over.mkIdTerminal
  change (c.ι.app i).val.app (Opposite.op A)
      (a.val.app (Opposite.op (Over.mk (𝟙 W))) (1 : R.obj.obj (Opposite.op W))) =
    b.val.app (Opposite.op (Over.mk (homOfLE hWU))) (1 : R.obj.obj (Opposite.op W))
  rw [unitFromTerminalSection_apply]
  have hk := Limits.colimit.ι_desc ((SheafOfModules.forget (R.over V)).mapCocone c) i
  have hk' := congrArg (fun g ↦ g.app (Opposite.op A) a₀) hk
  change k.app (Opposite.op A) ((Limits.colimit.ι F i).app (Opposite.op A) a₀) =
    (c.ι.app i).val.app (Opposite.op A) a₀ at hk'
  change (Limits.colimit.ι F i).app (Opposite.op A) a₀ = t at ha₀
  rw [ha₀] at hk'
  have hnat := PresheafOfModules.naturality_apply b.val
    (Over.homMk (homOfLE hWU) : Over.mk (homOfLE hWU) ⟶ Over.mk (𝟙 U)).op
    (1 : R.obj.obj (Opposite.op U))
  have hunit : (unit (R.over U)).val.map
      (Over.homMk (homOfLE hWU) : Over.mk (homOfLE hWU) ⟶ Over.mk (𝟙 U)).op
      (1 : R.obj.obj (Opposite.op U)) = (1 : R.obj.obj (Opposite.op W)) := by
    change R.obj.map (homOfLE hWU).op 1 = 1
    exact (R.obj.map (homOfLE hWU).op).hom.map_one
  rw [hunit] at hnat
  exact (hk'.symm.trans ht).trans hnat.symm

set_option backward.isDefEq.respectTransparency false in
/-- A single section of a restricted free module sheaf locally has finite support.

Source: Stacks Project, Modules, Tags 01BB (first paragraph of the proof) and 01AH (2).
(blueprint: lem-weil-pbc-module-unit-local-support).

Proof: The finite subsets of I, viewed as types with inclusion maps, have I as
colimit: send i through its singleton stage, and use cocone naturality for the
inclusion of that singleton into any finite subset containing i. The free
functor preserves this colimit and takes its structure maps to freeMap.
For an arbitrary filtered colimit c of module sheaves over V, form the colimit
P of the underlying presheaves. Sheafification of P is isomorphic to c.pt;
the canonical comparison P -> c.pt.val is the sheafification unit followed by
this isomorphism. It is therefore locally surjective. Apply its covering image
sieve to the section obtained by evaluating b at 1 over U, and choose a member
W containing x. The lifted section of P over W comes from some finite stage S,
since presheaf colimits are computed sectionwise and the module forgetful
functor preserves filtered colimits. Restrict this stage section to all opens
inside W and use unitHomEquiv to construct a. Cocone compatibility and the
naturality of b show that the two morphisms agree on 1 over W. Their associated
sections agree everywhere by restriction from this terminal open, so they are
equal. No stalk comparison, preservation of colimits by restriction, compactness,
or simultaneous shrinking is required. The argument also covers empty I;
then every finite stage is empty. -/
theorem exists_unit_local_support
    (X : Scheme.{u}) (V U : X.Opens) (hUV : U ≤ V) (I : Type u)
    (b : unit ((moduleRings X.toRingedSpace).over U) ⟶
      (overMap (moduleRings X.toRingedSpace) (homOfLE hUV)).obj
        (free (R := (moduleRings X.toRingedSpace).over V) I)) (x : U) :
    ∃ (W : X.Opens) (hWU : W ≤ U), (x : X) ∈ W ∧ ∃ (S : Finset I)
      (a : unit ((moduleRings X.toRingedSpace).over W) ⟶
        (overMap (moduleRings X.toRingedSpace) (homOfLE (hWU.trans hUV))).obj
          (free (R := (moduleRings X.toRingedSpace).over V) S)),
      a ≫ (overMap (moduleRings X.toRingedSpace) (homOfLE (hWU.trans hUV))).map
        (freeMap (R := (moduleRings X.toRingedSpace).over V) ((↑) : S → I)) =
      (overMap (moduleRings X.toRingedSpace) (homOfLE hWU)).map b := by
  classical
  let R := moduleRings X.toRingedSpace
  let L := freeFunctor (R := R.over V)
  let c := L.mapCocone (finiteSubsetCocone I)
  have hc : Limits.IsColimit c := Limits.isColimitOfPreserves L (finiteSubsetIsColimit I)
  obtain ⟨W, hWU, hxW, S, a, ha⟩ :=
    exists_unit_local_colimit_lift X R V U hUV
      (finiteSubsetDiagram I ⋙ L) c hc b x
  refine ⟨W, hWU, hxW, S, a, ?_⟩
  have hι : c.ι.app S = freeMap (R := R.over V) ((↑) : S → I) :=
    freeFunctor_map (↾((↑) : S → I))
  rw [hι] at ha
  exact ha

end AlgebraicGeometry.Scheme.Modules
