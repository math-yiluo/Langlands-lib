/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OpenModuleStalkFunctor
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import WeilConjectures.AlgebraicGeometry.OpenStalkUnitMapOneLift
import WeilConjectures.AlgebraicGeometry.OpenStalkRestrictionTransport
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-! # One finite-free open-site stalk map lifts on one neighbourhood

Source: Stacks Project, Modules Tag 01CP, and Sheaves Tag 00A0 (3).
(blueprint: lem-sc-open-stalk-free-map-one-lift).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme
noncomputable section

private theorem restriction_lift_stalk
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {R : A ⥤ B} {Q : B ⥤ C} {P : A ⥤ C} {S : C ⥤ D} {T : B ⥤ D} {H : A ⥤ D}
    (c : R ⋙ Q ≅ P) (d : Q ⋙ S ≅ T) (a : R ⋙ T ≅ H) (e : P ⋙ S ≅ H)
    (hc : ∀ M, S.map (c.hom.app M) ≫ e.hom.app M = d.hom.app (R.obj M) ≫ a.hom.app M)
    {F N : A} (t : H.obj F ⟶ H.obj N) (k : R.obj F ⟶ R.obj N)
    (hk : T.map k = a.hom.app F ≫ t ≫ a.inv.app N) :
    S.map (c.inv.app F ≫ Q.map k ≫ c.hom.app N) =
      e.hom.app F ≫ t ≫ e.inv.app N := by
  apply (cancel_mono (e.hom.app N)).1
  simp only [Category.assoc, e.inv_hom_id_app, Category.comp_id, Functor.map_comp]
  rw [hc N]
  have hd : S.map (Q.map k) ≫ d.hom.app (R.obj N) =
      d.hom.app (R.obj F) ≫ T.map k := d.hom.naturality k
  rw [← Category.assoc (S.map (Q.map k)), hd]
  simp only [Category.assoc]
  rw [hk]
  simp only [Category.assoc, a.inv_hom_id_app, Category.comp_id]
  rw [← Category.assoc (d.hom.app _), ← hc F]
  simp only [← Category.assoc, ← S.map_comp, c.inv_hom_id_app, S.map_id,
    Category.id_comp]


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A single finite-free stalk map lifts on one smaller open. The comparison may
be chosen with this lift; no comparison family or further-restriction assertion is made.

Source: Stacks Project, Modules Tag 01CP (`lemma-stalk-internal-hom`), the
finite-generator part of the finite-presentation proof; Sheaves Tag 00A0 (3).
(blueprint: lem-sc-open-stalk-free-map-one-lift).

Proof: Use the slice/open-subspace equivalence to regard the source and target
as module sheaves on U.toScheme. This equivalence carries the rank-m free sheaf
to the rank-m free structure module, since its sectionwise restriction preserves
the unit sheaf and finite coproducts. The open-immersion stalk-ring map is an
isomorphism, so transport t from the ambient stalk ring to the stalk ring on U.
Apply t to the m standard basis germs and choose section representatives of their
images in N. Intersect their finitely many neighbourhoods in U to obtain V.
Restrict the representatives to V and extend the assignment of basis sections
by the free sheaf universal property, obtaining k. This is also the identity-source
case of finite-free local stalk-map lifting on the ringed space U.toScheme.
The stalk of k agrees with t on each basis germ, hence on every vector by linearity.
Transport k back through the slice equivalence. Take a to be the canonical
restriction-stalk comparison, whose germ formula identifies a restricted germ
with the original germ. The equality just proved is S(k) followed by a_N equals
 a_F followed by t; composing with a_N inverse gives the displayed formula.
For m=0 take V=U and the unique zero-source map; no representatives are needed.
No finiteness or quasicoherence of N is used. -/
theorem exists_open_stalk_free_map_one_lift
    (X : Scheme.{u}) (U : X.Opens) (x : X) (hxU : x ∈ U)
    (m : ℕ) (N : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
    (t : (openModuleStalkFunctor X U ⟨x, hxU⟩).obj
      (SheafOfModules.free
        (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin m))) ⟶
      (openModuleStalkFunctor X U ⟨x, hxU⟩).obj N) :
    ∃ (V : X.Opens) (hxV : x ∈ V) (hVU : V ≤ U),
      let R := SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE hVU)
      let S := openModuleStalkFunctor X V ⟨x, hxV⟩
      let F := SheafOfModules.free
        (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin m))
      ∃ (a : R ⋙ S ≅ openModuleStalkFunctor X U ⟨x, hxU⟩)
        (k : R.obj F ⟶ R.obj N),
        S.map k = a.hom.app F ≫ t ≫ a.inv.app N := by
  classical
  let I := ULift.{u} (Fin m)
  let F := SheafOfModules.free (R := (moduleRings X.toRingedSpace).over U) I
  let L := SheafOfModules.unit ((moduleRings X.toRingedSpace).over U)
  let T := openModuleStalkFunctor X U ⟨x, hxU⟩
  let ti (i : I) : T.obj L ⟶ T.obj N := T.map (SheafOfModules.ιFree i) ≫ t
  have he := exists_openStalk_restriction_transport X U x hxU
  let e := fun (W : X.Opens) (hxW : x ∈ W) (hWU : W ≤ U) ↦
    openModuleStalkRestrictionComparison X U W hWU x hxU hxW
  choose D hxD hDU a k hk using fun i : I ↦
    exists_open_stalk_unit_map_one_lift X U x hxU N (ti i)
  let V : X.Opens := U ⊓ ⨅ i : I, D i
  have hVU : V ≤ U := inf_le_left
  have hVD (i : I) : V ≤ D i := inf_le_right.trans (iInf_le D i)
  have hxV : x ∈ V := by
    refine ⟨hxU, ?_⟩
    rw [TopologicalSpace.Opens.coe_iInf]
    exact Set.mem_iInter.mpr hxD
  let R := SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (homOfLE hVU)
  let S := openModuleStalkFunctor X V ⟨x, hxV⟩
  let E : R ⋙ S ≅ T := e V hxV hVU
  have hi (i : I) : ∃ g : R.obj L ⟶ R.obj N,
      S.map g = E.hom.app L ≫ ti i ≫ E.inv.app N := by
    obtain ⟨c, d, -, hc⟩ := he (D i) (hxD i) (hDU i) (a i) V hxV (hVD i) hVU
    let Q := SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
      (homOfLE (hVD i))
    refine ⟨c.inv.app L ≫ Q.map (k i) ≫ c.hom.app N, ?_⟩
    exact restriction_lift_stalk c d (a i) E hc (ti i) (k i) (hk i)
  choose g hg using hi
  let K : R.obj F ⟶ R.obj N := ∑ i : I, R.map (SheafOfModules.freeπ i) ≫ g i
  refine ⟨V, hxV, hVU, E, K, ?_⟩
  change S.map K = E.hom.app F ≫ t ≫ E.inv.app N
  dsimp only [K]
  rw [Functor.map_sum]
  simp only [Functor.map_comp, hg]
  have hn (i : I) :
      S.map (R.map (SheafOfModules.freeπ i)) ≫ E.hom.app L =
        E.hom.app F ≫ T.map (SheafOfModules.freeπ i) :=
    E.hom.naturality (SheafOfModules.freeπ i)
  simp only [← Category.assoc, hn]
  simp only [ti, Category.assoc]
  calc
    _ = E.hom.app F ≫ (∑ i : I,
        T.map (SheafOfModules.freeπ i ≫ SheafOfModules.ιFree i)) ≫
          t ≫ E.inv.app N := by
      simp only [Preadditive.comp_sum, Preadditive.sum_comp, Functor.map_comp,
        Category.assoc]
    _ = E.hom.app F ≫ t ≫ E.inv.app N := by
      rw [← Functor.map_sum, SheafOfModules.sum_freeπ_ιFree, T.map_id,
        Category.id_comp]


end
end AlgebraicGeometry.Scheme
