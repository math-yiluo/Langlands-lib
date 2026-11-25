/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Category.Preorder

import Mathlib.CategoryTheory.Limits.Constructions.Filtered
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits

/-!
# Small finite-subsum presentations of existing module-sheaf coproducts

Source: Stacks Project, Modules, Tag 01AH; Cohomology, Tag 09J7.
(blueprint: lem-weil-pbc-module-coproduct-small-subsum-diagram).
-/

@[expose] public section

universe u v
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace AlgebraicGeometry.Scheme

attribute [local instance] Abelian.hasFiniteBiproducts

/-- Nonzero summands inject into the endomorphisms of their coproduct. -/
private theorem small_coproduct_support
    {C : Type*} [Category C] [Preadditive C] [LocallySmall.{u} C]
    {I : Type v} (F : I → C) (t : Cofan F) (ht : IsColimit t) :
    Small.{u} {i // ¬ IsZero (F i)} := by
  classical
  let p (i : I) : t.pt ⟶ F i := ht.desc (Cofan.mk (F i) (Pi.single i (𝟙 (F i))))
  have hp (i j : I) :
      t.inj j ≫ p i = Pi.single (M := fun j ↦ F j ⟶ F i) i (𝟙 (F i)) j :=
    ht.fac (Cofan.mk (F i) (Pi.single i (𝟙 (F i)))) (Discrete.mk j)
  apply small_of_injective (f := fun i : {i // ¬ IsZero (F i)} ↦ p i.val ≫ t.inj i.val)
  intro i j hij
  apply Subtype.ext
  by_contra hne
  have he := congrArg (fun f ↦ t.inj i.val ≫ f ≫ p i.val) hij
  have hi : t.inj i.val ≫ p i.val = 𝟙 (F i.val) := by simp [hp]
  have hj : t.inj i.val ≫ p j.val = 0 := by simp [hp, hne]
  have hid : 𝟙 (F i.val) = 0 := by
    simpa only [← Category.assoc, hi, hj, Category.id_comp, zero_comp] using he
  exact i.property ((IsZero.iff_id_eq_zero _).mpr hid)

open Classical in
/-- A given, possibly large coproduct of module sheaves has a small directed presentation
by finite biproducts of its summands, with the original inclusions as component maps.

Source: Stacks Project, Modules, Tag 01AH; Cohomology, Tag 09J7, the finite-subsum
presentation used in the proof. The universe reduction is the smallness argument in
`lem-weil-pbc-qcqs-cohomology-finite-subsum-representatives`.
(blueprint: lem-weil-pbc-module-coproduct-small-subsum-diagram).

Proof: Let N be the subtype of indices of nonzero summands. For each summand,
the coproduct universal property supplies a projection which is the identity on
that summand and zero on all others. The resulting endomorphisms of S are distinct
on N: composing an equality with the inclusion and projection of one summand
would make its identity zero. Thus N injects into End(S), which is u-small.
This is the same argument as the proved private small-support helper in
`WeilConjectures.CategoryTheory.CompactTestsRightAdjointCoproducts`.

Discard the zero summands: extend any family of maps on N by zero, and use the
original coproduct universal property. Maps from a zero summand are unique,
which proves uniqueness. Shrink N to B : Type u and whisker the restricted cofan
by the discrete equivalence. Mathlib's finite-subcoproduct diagram on
Finset (Discrete B) is directed, nonempty, and has colimit the coproduct of this
small family. Transport that cocone along the unique coproduct isomorphism to S.
For each finite stage a, map its indices injectively to I, obtaining J. The
finite-set image equivalence and the biproduct-coproduct isomorphism identify
the stage with the biproduct over J. The equations for these isomorphisms and
the transported colimit legs give precisely the original inclusion ι j.
No cohomology, compactness or quasi-separatedness is used. For empty support,
the diagram contains only the empty finite subset and its zero coproduct. -/
theorem exists_small_finiteSubsum_diagram (X : Scheme.{u}) (I : Type v)
    (F : I → SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (S : SheafOfModules.{u} (moduleRings X.toRingedSpace)) (ι : ∀ i : I, F i ⟶ S)
    (hS : IsColimit (Cofan.mk S ι)) :
    ∃ (A : Type u) (_ : Preorder A) (_ : Nonempty A) (_ : IsDirected A (· ≤ ·))
      (D : A ⥤ SheafOfModules.{u} (moduleRings X.toRingedSpace))
      (τ : D ⟶ (Functor.const A).obj S) (_ : IsColimit (Cocone.mk S τ)),
      ∀ a : A, ∃ (J : Finset I) (e : D.obj a ≅ ⨁ (fun j : J ↦ F j)),
        ∀ j : J, biproduct.ι (fun j : J ↦ F j) j ≫ e.inv ≫ τ.app a = ι j := by
  classical
  have : LocallySmall.{u} (SheafOfModules.{u} (moduleRings X.toRingedSpace)) := by
    infer_instance
  have hsupport : Small.{u} {i // ¬ IsZero (F i)} :=
    small_coproduct_support F (Cofan.mk S ι) hS
  let N := {i // ¬ IsZero (F i)}
  let B := Shrink.{u} N
  let e : N ≃ B := equivShrink N
  let r : B → I := fun b ↦ (e.symm b).val
  let G : B → SheafOfModules.{u} (moduleRings X.toRingedSpace) := fun b ↦ F (r b)
  let U : N → SheafOfModules.{u} (moduleRings X.toRingedSpace) := fun i ↦ F i.val
  let tN : Cofan U := Cofan.mk S (fun i ↦ ι i.val)
  have htN : IsColimit tN := by
    refine Cofan.IsColimit.mk tN (fun s ↦ hS.desc (Cofan.mk s.pt
      (fun i ↦ if hi : ¬ IsZero (F i) then s.inj ⟨i, hi⟩ else 0))) ?_ ?_
    · intro s i
      obtain ⟨i, hi⟩ := i
      change (Cofan.mk S ι).ι.app (Discrete.mk i) ≫ _ = _
      rw [hS.fac]
      simp only [Cofan.mk_ι_app, dite_eq_left hi]
    · intro s m hm
      apply hS.hom_ext
      intro ⟨i⟩
      rw [hS.fac]
      by_cases hi : ¬ IsZero (F i)
      · simpa only [tN, cofan_mk_inj, Cofan.inj, Cofan.mk_ι_app, dite_eq_left hi]
          using hm ⟨i, hi⟩
      · exact (not_not.mp hi).eq_of_src _ _
  let t : Cofan G := tN.whisker (Discrete.equivalence e.symm).functor
  have ht : IsColimit t := htN.whiskerEquivalence (Discrete.equivalence e.symm)
  have : HasCoproduct G := ⟨⟨t, ht⟩⟩
  let q : (∐ G) ≅ S := IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) ht
  let D := CoproductsFromFiniteFiltered.liftToFinsetObj (Discrete.functor G)
  let c := CoproductsFromFiniteFiltered.finiteSubcoproductsCocone G
  let cS := c.extend q.hom
  have hcS : IsColimit cS :=
    IsColimit.extendIso (s := c) q.hom
      (CoproductsFromFiniteFiltered.isColimitFiniteSubproductsCocone G)
  refine ⟨Finset (Discrete B), inferInstance, inferInstance, inferInstance,
    D, cS.ι, hcS, ?_⟩
  intro a
  let f : Discrete B ↪ I := ⟨fun b ↦ r b.as, by
    intro b b' h
    apply Discrete.ext
    apply e.symm.injective
    exact Subtype.ext h⟩
  let J := a.map f
  let E : a ≃ J := Finset.equivMap f a
  let H : a → SheafOfModules.{u} (moduleRings X.toRingedSpace) := fun b ↦ G b.val.as
  let w : ∀ b : a, F (E b).val ≅ H b := fun _ ↦ Iso.refl _
  let z : D.obj a ≅ ⨁ (fun j : J ↦ F j) :=
    (biproduct.isoCoproduct H).symm ≪≫ biproduct.whiskerEquiv E w
  refine ⟨J, z, ?_⟩
  intro j
  obtain ⟨b, rfl⟩ := E.surjective j
  have hz : Sigma.ι H b ≫ z.hom = biproduct.ι (fun j : J ↦ F j) (E b) := by
    simp only [z, Iso.trans_hom, Iso.symm_hom,
      biproduct.isoCoproduct_inv, Sigma.ι_comp_desc_assoc, biproduct.whiskerEquiv_hom,
      biproduct.ι_desc, w, Iso.refl_inv]
    exact Category.id_comp _
  rw [← hz]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  change Sigma.ι H b ≫ (Sigma.desc (fun b : a ↦ Sigma.ι G b.val.as) ≫ q.hom) = _
  rw [Sigma.ι_comp_desc_assoc]
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (colimit.isColimit (Discrete.functor G)) ht (Discrete.mk b.val.as)

end AlgebraicGeometry.Scheme
