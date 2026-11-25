/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTorsion
import WeilConjectures.AlgebraicGeometry.EtaleSheafDiscreteContinuousRep
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.FiniteAbelian.Basic

/-!
# A stalk element lies in a finite-stalk subobject

Source: blueprint `theorem-cohomology-curves--2`, paragraph 4; Stacks 04JQ.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
private theorem finite_stable_submodule
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] {V : Type (u + 1)} [AddCommGroup V] [Module ℤ V]
    (ρ : Representation ℤ G V)
    (hρ : ∀ x : V, IsOpen {g : G | ρ g x = x})
    (ht : IsAddTorsion V) (x : V) :
    ∃ (W : Submodule ℤ V), x ∈ W ∧ Finite W ∧ ∀ g, W ≤ W.comap (ρ g) := by
  classical
  let : MulAction G V :=
    { smul g y := ρ g y
      one_smul y := by change ρ 1 y = y; simp
      mul_smul g h y := by change ρ (g * h) y = ρ g (ρ h y); simp }
  have hopen : IsOpen (MulAction.stabilizer G x : Set G) := hρ x
  have : Finite (G ⧸ MulAction.stabilizer G x) :=
    Subgroup.quotient_finite_of_isOpen _ hopen
  have : Finite (MulAction.orbit G x) :=
    Finite.of_equiv _ (MulAction.orbitEquivQuotientStabilizer G x).symm
  have horbit : (MulAction.orbit G x).Finite := Set.toFinite _
  let W := Submodule.span ℤ (MulAction.orbit G x)
  have hfg : W.FG := Submodule.fg_span horbit
  have : Module.Finite ℤ W := by
    have he : W.module = AddCommGroup.toIntModule W := Subsingleton.elim _ _
    rw [← he]
    exact Module.Finite.of_fg hfg
  have htor : IsAddTorsion W := ht.addSubgroup W.toAddSubgroup
  have : AddGroup.FG W := Module.Finite.iff_addGroup_fg.mp inferInstance
  refine ⟨W, Submodule.subset_span (MulAction.mem_orbit_self x),
    AddCommGroup.finite_of_fg_isAddTorsion W htor, ?_⟩
  intro g y hy
  change ρ g y ∈ W
  induction hy using Submodule.span_induction with
  | mem y hy =>
    apply Submodule.subset_span
    obtain ⟨h, rfl⟩ := hy
    exact ⟨g * h, by change (ρ (g * h)) x = ρ g (ρ h x); simp⟩
  | zero => simp
  | add y z hy hz ihy ihz => simpa using W.add_mem ihy ihz
  | smul n y hy ih => simpa using W.smul_mem n ih

-- Prove the transport with abstract functors, so rewriting does not unfold the stalk comparison.
private theorem finite_subobject_element_of_equivalence
    {C D : Type*} [Category C] [Category D] (E : C ≌ D)
    (Φ : C ⥤ AddCommGrpCat.{u + 1}) (R : D ⥤ AddCommGrpCat.{u + 1})
    (i : E.functor ⋙ R ≅ Φ) {M : C} {B : D}
    (inc : B ⟶ E.functor.obj M) [Mono inc] [Finite (R.obj B)]
    (y : R.obj B) (x : Φ.obj M) (hy : (R.map inc ≫ i.hom.app M) y = x) :
    ∃ (N : Subobject M) (_ : Finite (Φ.obj (N : C))) (z : Φ.obj (N : C)),
      Φ.map N.arrow z = x := by
  classical
  let f : E.inverse.obj B ⟶ M := E.functor.preimage (E.counitIso.hom.app B ≫ inc)
  have hf : E.functor.map f = E.counitIso.hom.app B ≫ inc := E.functor.map_preimage _
  have : Mono (E.functor.map f) := by rw [hf]; infer_instance
  have : Mono f := E.functor.mono_of_mono_map inferInstance
  let e : Φ.obj (E.inverse.obj B) ≅ R.obj B :=
    (i.app (E.inverse.obj B)).symm ≪≫ R.mapIso (E.counitIso.app B)
  have hmap : Φ.map f = e.hom ≫ R.map inc ≫ i.hom.app M := by
    calc
      Φ.map f = i.inv.app (E.inverse.obj B) ≫ (E.functor ⋙ R).map f ≫
          i.hom.app M := by
        rw [i.hom.naturality, Iso.inv_hom_id_app_assoc]
      _ = e.hom ≫ R.map inc ≫ i.hom.app M := by
        simp only [Functor.comp_map, hf, R.map_comp, e, Iso.trans_hom, Iso.symm_hom,
          Functor.mapIso_hom, Category.assoc]
        rfl
  let N := Subobject.mk f
  let eN : Φ.obj (N : C) ≅ R.obj B := Φ.mapIso (Subobject.underlyingIso f) ≪≫ e
  have hN : Finite (Φ.obj (N : C)) := Finite.of_injective eN.hom
    (ConcreteCategory.bijective_of_isIso _).1
  refine ⟨N, hN, eN.inv y, ?_⟩
  change Φ.map N.arrow ((e.inv ≫ Φ.map (Subobject.underlyingIso f).inv) y) = x
  rw [ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← Φ.map_comp, Subobject.underlyingIso_arrow, hmap]
  simpa only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply] using hy

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option linter.style.haveILetI false in
/-- Every element of the geometric stalk of a torsion sheaf over a field comes from
one finite-stalk subobject.

Source: blueprint `theorem-cohomology-curves--2`, paragraph 4, and Stacks 04JQ.
(blueprint: lem-sc-field-finite-stalk-subobject-element)

Proof: Take the separable closure inside AlgebraicClosure K and identify the sheaf
with its discrete continuous absolute Galois module using 04JQ. The stalk is torsion
by the geometric-stalk torsion criterion. The stabilizer of an element is open, so
its coset space, and hence its orbit, is finite by compactness of the Galois group.
The additive subgroup generated by the orbit is stable under the action. It is
finitely generated and torsion, hence finite. Regard it as a discrete continuous
subrepresentation, transport its injective inclusion through the inverse equivalence,
and form its subobject. The stalk comparison identifies this inclusion with the
original subgroup inclusion. Therefore its stalk is finite and the element lifts to
it. For the zero element the zero subgroup suffices; the ambient module need not be
finitely generated. No supremum or conservativity assertion is part of this lemma. -/
theorem torsion_exists_finite_stalk_subobject_element
    (K : Type u) [Field K]
    (M : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hM : M.IsTorsion) :
    let Φ := (pointSmallEtale
      (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))).sheafFiber
        (A := AddCommGrpCat.{u + 1})
    ∀ x : Φ.obj M, ∃ (N : Subobject M)
      (_ : Finite (Φ.obj (N :
        Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})))
      (y : Φ.obj (N :
        Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})),
      Φ.map N.arrow y = x := by
  dsimp only
  classical
  let Φ := (pointSmallEtale
    (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))).sheafFiber
      (A := AddCommGrpCat.{u + 1})
  let E := etaleSheafEquivDiscreteContinuousRep K (SeparableClosure K)
  let i := etaleSheafEquivDiscreteContinuousRepForgetIso
    K (SeparableClosure K) (AlgebraicClosure K)
  let U := ObjectProperty.ι (fun X : Rep.{u + 1} ℤ (Gal(SeparableClosure K/K)) ↦
    ∀ x : X.V, IsOpen {g | X.ρ g x = x})
  let R := U ⋙ Rep.RepToAction ℤ (Gal(SeparableClosure K/K)) ⋙
    Action.forget (ModuleCat.{u + 1} ℤ) (Gal(SeparableClosure K/K)) ⋙
    forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat
  let A := E.functor.obj M
  letI : Module ℤ A.obj.V := A.obj.hV2
  have ht : IsAddTorsion (R.obj A) := IsAddTorsion.of_surjective
    (f := (i.inv.app M).hom) (ConcreteCategory.bijective_of_isIso _).2
    ((isTorsion_iff_isAddTorsion_sheafFiber M).mp hM _
      (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))))
  intro x
  let a : A.obj.V := i.inv.app M x
  obtain ⟨W, ha, hfin, hW⟩ := finite_stable_submodule A.obj.ρ A.property ht a
  let B : Rep.DiscreteContinuousRep.{0, u, u + 1} ℤ (Gal(SeparableClosure K/K)) :=
    ⟨Rep.subrepresentation A.obj W hW, fun y ↦ by
      convert A.property y.val using 1
      ext g
      exact Subtype.ext_iff⟩
  let inc : B ⟶ A := ObjectProperty.homMk (Rep.subtype A.obj W hW)
  have : Mono (U.map inc) := (Rep.mono_iff_injective _).mpr Subtype.val_injective
  have : Mono inc := U.mono_of_mono_map inferInstance
  have : Finite (R.obj B) := hfin
  apply finite_subobject_element_of_equivalence E Φ R i inc ⟨a, ha⟩ x
  change (i.hom.app M) ((i.inv.app M) x) = x
  exact Iso.inv_hom_id_apply (i.app M) x

end AlgebraicGeometry.Scheme
