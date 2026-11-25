/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.Algebra.Homology.LocalizedHomComplexHomotopy
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalized
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-!
# Localized derived morphisms into a K-injective complex

Source: Stacks Project, Lemma 21.34.6, Tag 0A94
(blueprint: lem-pur-rhom-into-kinjective-local).

## Main statements

* `module_overFunctor_preservesZero`: the zero-morphism compatibility needed to restrict complexes.
* `rhom_into_kinjective_local`: the canonical localized derived-morphism bijection.
-/

@[expose] public section

universe u v w r t

open CategoryTheory Opposite

namespace CategoryTheory


/-- Restriction of module sheaves preserves zero morphisms.
Source: Stacks Project, Lemma 21.20.1, as used in Tag 0A94
(blueprint: lem-pur-rhom-into-kinjective-local).

Proof: restriction evaluates a morphism at objects of the localized site. The restriction
of a zero morphism therefore has zero at every component, and is the zero morphism. -/
theorem module_overFunctor_preservesZero
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{r}) (U : C) :
    (SheafOfModules.overFunctor.{w} R U).PreservesZeroMorphisms := by
  constructor
  intro M N
  ext W x
  rfl

/-- Degree-zero cocycles of the sections of the sheaf Hom complex are precisely localized
chain maps. The induced map on degree-zero cohomology sends a chain map to its image under
localization and is bijective.
Source: Stacks Project, Lemma 21.34.6, Tag 0A94
(blueprint: lem-pur-rhom-into-kinjective-local).

Proof: restriction to `C/U` is right adjoint to exact extension by zero in module categories
(lem-pur-site-restriction-module-adjunction-exact). Thus restriction preserves K-injective
complexes (lem-weil-pbc-right-adjoint-preserves-kinjective). The product projections of
`homComplex` identify degree-zero cocycles with chain maps; the differential in degree
minus one identifies coboundaries with null-homotopies (def-pur-hom-complex). Consequently
its zeroth cohomology is the Hom group in the localized homotopy category. The K-injective
comparison (lem-weil-pbc-kinjective-hom-derived) identifies this Hom group with morphisms in
the derived category, by the map induced by localization. This proves well-definedness and
bijectivity. The component equation below specifies the cocycle identification, so the
result concerns the canonical map, independently of choices of product or homology objects. -/
theorem rhom_into_kinjective_local
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{max u v}) (U : C)
    [HasDerivedCategory.{t} (SheafOfModules.{max u v}
      (((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R).over U))]
    (L I : CochainComplex (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ)
    [I.IsKInjective] :
    let R₀ := (sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R
    let H := homComplex (R := R) L I
    let π := Classical.choose (Classical.choose_spec
      (homComplex_exists.{u, v, max u v, max u v} (J := J) (R := R)))
    let S := ((SheafOfModules.forget R₀ ⋙ PresheafOfModules.evaluation R₀.obj (op U) ⋙
      forget₂ (ModuleCat.{max u v} (R₀.obj.obj (op U))) AddCommGrpCat).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj H
    letI := module_overFunctor_preservesZero.{u, v, max u v, max u v} R₀ U
    let res : CochainComplex (SheafOfModules.{max u v} R₀) ℤ ⥤
        CochainComplex (SheafOfModules.{max u v} (R₀.over U)) ℤ :=
      (SheafOfModules.overFunctor.{max u v} R₀ U).mapHomologicalComplex (ComplexShape.up ℤ)
    let Q := DerivedCategory.Q.{t} (C := SheafOfModules.{max u v} (R₀.over U))
    ∃ e : S.cycles 0 ≃ (res.obj L ⟶ res.obj I),
      (∀ (z : S.cycles 0) (p : ℤ) (W : (Over U)ᵒᵖ),
        ((e z).f p).val.app W =
          (((π L I 0 p p (add_zero p)).val.app (op U)) (S.iCycles 0 z)).app W) ∧
      ∃ φ : S.homology 0 → (Q.obj (res.obj L) ⟶
        Q.obj (res.obj I)),
        (∀ z : S.cycles 0, φ (S.homologyπ 0 z) = Q.map (e z)) ∧
        Function.Bijective φ := by
  classical
  let R₀ := (sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R
  let hzero := module_overFunctor_preservesZero.{u, v, max u v, max u v} R₀ U
  let := hzero
  let res := (SheafOfModules.overFunctor.{max u v} R₀ U).mapHomologicalComplex
    (ComplexShape.up ℤ)
  let q := HomotopyCategory.quotient (SheafOfModules.{max u v} (R₀.over U))
    (ComplexShape.up ℤ)
  have : CochainComplex.IsKInjective (res.obj I) :=
    isKInjective_restrict_localized R₀ U hzero I
  have h := localizedHomComplex_homotopy (C := C) J R U L I hzero
  rcases h with ⟨e, he, a, ha⟩
  let b : (q.obj (res.obj L) ⟶ q.obj (res.obj I)) ≃
      (DerivedCategory.Qh.{t}.obj (q.obj (res.obj L)) ⟶
        DerivedCategory.Qh.{t}.obj (q.obj (res.obj I))) := Equiv.ofBijective
    (DerivedCategory.Qh.{t}.map : (q.obj (res.obj L) ⟶ q.obj (res.obj I)) → _)
    (CochainComplex.IsKInjective.Qh_map_bijective (q.obj (res.obj L)) (res.obj I))
  let c : (DerivedCategory.Qh.{t}.obj (q.obj (res.obj L)) ⟶
      DerivedCategory.Qh.{t}.obj (q.obj (res.obj I))) ≃
      (DerivedCategory.Q.{t}.obj (res.obj L) ⟶ DerivedCategory.Q.{t}.obj (res.obj I)) :=
    Iso.homCongr
    ((DerivedCategory.quotientCompQhIso.{t}
      (SheafOfModules.{max u v} (R₀.over U))).app (res.obj L))
    ((DerivedCategory.quotientCompQhIso.{t}
      (SheafOfModules.{max u v} (R₀.over U))).app (res.obj I))
  refine ⟨e, he, (a.trans (b.trans c)), ?_, (a.trans (b.trans c)).bijective⟩
  intro z
  change c (b (a (_))) = _
  rw [ha]
  change (DerivedCategory.quotientCompQhIso.{t}
    (SheafOfModules.{max u v} (R₀.over U))).inv.app (res.obj L) ≫
      DerivedCategory.Qh.{t}.map (q.map (e z)) ≫
        (DerivedCategory.quotientCompQhIso.{t}
          (SheafOfModules.{max u v} (R₀.over U))).hom.app (res.obj I) = _
  rw [DerivedCategory.quotientCompQhIso_hom_naturality (e z)]
  exact Iso.inv_hom_id_app_assoc
    (DerivedCategory.quotientCompQhIso.{t} (SheafOfModules.{max u v} (R₀.over U)))
    (res.obj L) (DerivedCategory.Q.{t}.map (e z))

end CategoryTheory
