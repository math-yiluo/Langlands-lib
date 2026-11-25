/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.HomotopyCategory
import WeilConjectures.Algebra.Homology.LocalizedHomComplexBoundaries
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Homology descent of the canonical localized chain-map comparison

Source: Stacks Project, Tag 0A8X, Hom complexes; Equation 0A8Y (degree zero)
(blueprint: lem-pur-localized-hom-complex-homology-aux).
-/

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace CategoryTheory

-- Evaluated chosen products and their categorical morphisms require extra elaboration work.
set_option backward.isDefEq.respectTransparency false in
/-- The canonical cocycle equivalence descends to homology and homotopy classes.
The component formula is essential: an arbitrary equivalence of sets need not
respect boundaries.
Source: Stacks Project, Tag 0A8X (Hom complexes), Equation 0A8Y
(blueprint: lem-pur-localized-hom-complex-homology-aux).

Proof: identify every degree n section with a family of localized maps using
the sectionwise product cone of `homComplex_exists`. Under this identification,
the differential from degree -1 to degree 0 sends h to d_I h + h d_L.
The assumed component formula identifies e with the degree-zero chain-map
construction. Consequently, for cycles z and z', their images under e are
homotopic if and only if their difference is a boundary: a degree -1 section
yields a homotopy by its components, and the components of any homotopy assemble
into such a section by the same product universal property. The formula for e
also makes it additive, since all projections and the cycle inclusion are linear
and chain maps are determined by their components. The homology projection in
abelian groups is surjective, with kernel the boundaries. The quotient functor
to the homotopy category is full and identifies exactly homotopic chain maps.
Define a on a homology class represented by z to be q.map (e z). The established
boundary criterion makes this well defined and injective. Fullness of q and
surjectivity of e make it surjective. Take the equivalence associated to this
bijection; its defining formula is the asserted compatibility on representatives.
For zero complexes both quotients are singletons; with zero differential there
are no nonzero boundaries, as the same criterion requires. -/
theorem localizedHomComplex_homology_aux
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{max u v}) (U : C)
    (L I : CochainComplex (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ)
    (hzero : Functor.PreservesZeroMorphisms
      (SheafOfModules.overFunctor.{max u v}
        ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R) U))
    (e : let R₀ := (sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R
      let H := homComplex (R := R) L I
      let S := ((SheafOfModules.forget R₀ ⋙ PresheafOfModules.evaluation R₀.obj (op U) ⋙
        forget₂ (ModuleCat.{max u v} (R₀.obj.obj (op U))) AddCommGrpCat).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj H
      letI := hzero
      let res := (SheafOfModules.overFunctor.{max u v} R₀ U).mapHomologicalComplex
        (ComplexShape.up ℤ)
      S.cycles 0 ≃ (res.obj L ⟶ res.obj I)) :
    let R₀ := (sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R
    let H := homComplex (R := R) L I
    let π := Classical.choose (Classical.choose_spec
      (homComplex_exists.{u, v, max u v, max u v} (J := J) (R := R)))
    let S := ((SheafOfModules.forget R₀ ⋙ PresheafOfModules.evaluation R₀.obj (op U) ⋙
      forget₂ (ModuleCat.{max u v} (R₀.obj.obj (op U))) AddCommGrpCat).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj H
    letI := hzero
    let res : CochainComplex (SheafOfModules.{max u v} R₀) ℤ ⥤
        CochainComplex (SheafOfModules.{max u v} (R₀.over U)) ℤ :=
      (SheafOfModules.overFunctor.{max u v} R₀ U).mapHomologicalComplex (ComplexShape.up ℤ)
    let q := HomotopyCategory.quotient
      (SheafOfModules.{max u v} (R₀.over U)) (ComplexShape.up ℤ)
    (∀ (z : S.cycles 0) (p : ℤ) (W : (Over U)ᵒᵖ),
      ((e z).f p).val.app W =
        (((π L I 0 p p (add_zero p)).val.app (op U)) (S.iCycles 0 z)).app W) →
    ∃ a : S.homology 0 ≃ (q.obj (res.obj L) ⟶ q.obj (res.obj I)),
      ∀ z : S.cycles 0, a (S.homologyπ 0 z) = q.map (e z) := by
  classical
  let R₀ := (sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R
  let H := homComplex (R := R) L I
  let π := Classical.choose (Classical.choose_spec
    (homComplex_exists.{u, v, max u v, max u v} (J := J) (R := R)))
  let S : CochainComplex AddCommGrpCat.{max u v} ℤ :=
    ((SheafOfModules.forget R₀ ⋙ PresheafOfModules.evaluation R₀.obj (op U) ⋙
    forget₂ (ModuleCat.{max u v} (R₀.obj.obj (op U))) AddCommGrpCat).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj H
  let := hzero
  let res : CochainComplex (SheafOfModules.{max u v} R₀) ℤ ⥤
      CochainComplex (SheafOfModules.{max u v} (R₀.over U)) ℤ :=
    (SheafOfModules.overFunctor.{max u v} R₀ U).mapHomologicalComplex
    (ComplexShape.up ℤ)
  change S.cycles 0 ≃ (res.obj L ⟶ res.obj I) at e
  let q := HomotopyCategory.quotient
    (SheafOfModules.{max u v} (R₀.over U)) (ComplexShape.up ℤ)
  change (∀ (z : S.cycles 0) (p : ℤ) (W : (Over U)ᵒᵖ),
    ((e z).f p).val.app W =
      (((π L I 0 p p (add_zero p)).val.app (op U)) (S.iCycles 0 z)).app W) →
    ∃ a : S.homology 0 ≃ (q.obj (res.obj L) ⟶ q.obj (res.obj I)),
      ∀ z : S.cycles 0, a (S.homologyπ 0 z) = q.map (e z)
  intro he
  have hadd (z z' : S.cycles 0) : e (z + z') = e z + e z' := by
    apply HomologicalComplex.hom_ext
    intro p
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro W
    change ((e (z + z')).f p).val.app W =
      ((e z).f p).val.app W + ((e z').f p).val.app W
    let P := (π L I 0 p p (add_zero p)).val.app (op U)
    have hi : S.iCycles 0 (z + z') = S.iCycles 0 z + S.iCycles 0 z' :=
      map_add (S.iCycles 0).hom z z'
    have hp : P (S.iCycles 0 (z + z')) = P (S.iCycles 0 z) + P (S.iCycles 0 z') :=
      (congrArg P hi).trans (map_add P.hom _ _)
    exact (he (z + z') p W).trans
      ((congrArg (fun f ↦ f.app W) hp).trans
        (congrArg₂ (· + ·) (he z p W).symm (he z' p W).symm))
  let E : S.cycles 0 →+ (res.obj L ⟶ res.obj I) := AddMonoidHom.mk' e hadd
  have hker (z : S.cycles 0) : q.map (e z) = 0 ↔
      ∃ x : S.X (-1), S.toCycles (-1) 0 x = z :=
    (HomotopyCategory.quotient_map_eq_zero_iff (e z)).trans
      (localizedHomComplex_nullHomotopy_iff_boundary.{u, v}
        (C := C) J R U L I hzero z (e z) (he z))
  have hhom (z : S.cycles 0) : S.homologyπ 0 z = 0 ↔
      ∃ x : S.X (-1), S.toCycles (-1) 0 x = z := by
    let T := ShortComplex.mk (S.toCycles (-1) 0) (S.homologyπ 0)
      (S.toCycles_comp_homologyπ (-1) 0)
    have ht : T.Exact := T.exact_of_g_is_cokernel
      (S.homologyIsCokernel (-1) 0 (by simp))
    exact (T.ab_exact_iff_function_exact.mp ht) z
  have hfiber (z z' : S.cycles 0) :
      S.homologyπ 0 z = S.homologyπ 0 z' ↔ q.map (e z) = q.map (e z') := by
    rw [← sub_eq_zero, ← map_sub, hhom, ← hker]
    change q.map (E (z - z')) = 0 ↔ _
    rw [map_sub, Functor.map_sub, sub_eq_zero]
    rfl
  have hs : Function.Surjective (S.homologyπ 0) :=
    (AddCommGrpCat.epi_iff_surjective _).mp inferInstance
  let f : S.homology 0 → (q.obj (res.obj L) ⟶ q.obj (res.obj I)) :=
    fun a ↦ q.map (e (Classical.choose (hs a)))
  have hf (z : S.cycles 0) : f (S.homologyπ 0 z) = q.map (e z) :=
    (hfiber _ _).mp (Classical.choose_spec (hs _))
  have hinj : Function.Injective f := by
    intro a b hab
    obtain ⟨z, rfl⟩ := hs a
    obtain ⟨z', rfl⟩ := hs b
    exact (hfiber z z').mpr (by simpa only [hf] using hab)
  have hsurj : Function.Surjective f := by
    intro a
    obtain ⟨g, rfl⟩ := q.map_surjective a
    obtain ⟨z, rfl⟩ := e.surjective g
    exact ⟨S.homologyπ 0 z, hf z⟩
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, hf⟩

end CategoryTheory
