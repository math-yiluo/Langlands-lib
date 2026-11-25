/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import WeilConjectures.ConstructibleSheaf.UniversalHomeomorphism
import WeilConjectures.AlgebraicGeometry.FieldPointFactorsThroughClosedImmersion

/-!
# Field-valued points factor through immersions

Source: literature/stacks-project/schemes.tex, Definitions 01IO and 01HK,
Lemmas 01HI, 0356, and 01L7, and the discussion before Lemma 01J9
(blueprint: lem-weil-pbc-field-point-factors-through-immersion).
-/

@[expose] public section

universe u
set_option linter.style.haveILetI false
open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- An immersion induces residue-field isomorphisms and uniquely lifts field-valued
points whose image is the image of a chosen point. First factor the immersion as a
closed immersion followed by an open immersion and compare the two residue-field maps
using `lem-weil-pbc-residue-field-point-naturality` and
`lem-weil-pbc-closed-immersion-residue-field-iso`; their composite is an isomorphism.
For a field-valued point, lift uniquely through the open factor by
`lem-weil-pbc-morphism-factors-through-open-subscheme`, then through the closed factor
by `lem-weil-pbc-field-point-factors-through-closed-immersion`. Uniqueness follows from
`lem-weil-pbc-open-immersion-monomorphism` and the closed-factor uniqueness. The final
universal quantification includes the algebraically closed-field case defining geometric
points.
Source: Stacks Project, Schemes, Definitions 01IO and 01HK, Lemmas 01HI, 0356,
and 01L7, and the discussion before Lemma 01J9
(blueprint: lem-weil-pbc-field-point-factors-through-immersion). -/
theorem fieldPoint_factorsThrough_immersion
    {Z X : Scheme.{u}} (iota : Z ⟶ X) [IsImmersion iota]
    (z : Z) :
    IsIso (iota.residueFieldMap z) ∧
      ∀ (K : Type u) [Field K] (s : Spec (.of K) ⟶ X),
        s.base ((default : Spec (.of K))) = iota.base z →
          (∃! s' : Spec (.of K) ⟶ Z, s' ≫ iota = s) ∧
            ∀ s' : Spec (.of K) ⟶ Z,
              s' ≫ iota = s → s'.base ((default : Spec (.of K))) = z := by
  let c := iota.liftCoborder
  let o := iota.coborderRange.ι
  have hfac : c ≫ o = iota := iota.liftCoborder_ι
  letI : IsClosedImmersion c := inferInstance
  letI : IsOpenImmersion o := inferInstance
  letI : IsIso (c.residueFieldMap z) :=
    Scheme.Hom.isIso_residueFieldMap c z
  letI : IsIso (o.residueFieldMap (c.base z)) := inferInstance
  have hres : IsIso (iota.residueFieldMap z) := by
    rw [← hfac, Scheme.residueFieldMap_comp]
    infer_instance
  refine ⟨hres, ?_⟩
  intro K _ s hs
  have hrange : Set.range s.base ⊆ Set.range o.base := by
    intro x hx
    rcases hx with ⟨y, rfl⟩
    have hy : y = (default : Spec (.of K)) := Subsingleton.elim _ _
    subst hy
    exact ⟨c.base z, by simpa [← hfac] using hs.symm⟩
  let t : Spec (.of K) ⟶ iota.coborderRange := IsOpenImmersion.lift o s hrange
  have ht : t ≫ o = s := IsOpenImmersion.lift_fac o s hrange
  have htz : t.base (default : Spec (.of K)) = c.base z := by
    apply o.isEmbedding.injective
    have hto : o.base (t.base (default : Spec (.of K))) = s.base default := by
      simpa only [← Scheme.Hom.comp_base, Scheme.Hom.comp_apply] using
        congrArg (fun f : Spec (.of K) ⟶ X => f.base default) ht
    have hoc : o.base (c.base z) = iota.base z := by
      simpa only [← Scheme.Hom.comp_base, Scheme.Hom.comp_apply] using
        congrArg (fun f : Z ⟶ X => f.base z) hfac
    exact hto.trans (hs.trans hoc.symm)
  obtain ⟨⟨u, hu, huuniq⟩, hupt⟩ := field_point_factors_through_closed_immersion
    c t z htz
  refine ⟨⟨u, ?_, ?_⟩, ?_⟩
  · calc
      u ≫ iota = (u ≫ c) ≫ o := by simp only [Category.assoc, hfac]
      _ = t ≫ o := by rw [hu]
      _ = s := ht
  · intro v hv
    apply huuniq v
    apply (cancel_mono o).1
    calc
      (v ≫ c) ≫ o = v ≫ iota := by simp only [Category.assoc, hfac]
      _ = s := hv
      _ = t ≫ o := ht.symm
  · intro v hv
    have hvu : v = u := by
      apply huuniq v
      apply (cancel_mono o).1
      calc
        (v ≫ c) ≫ o = v ≫ iota := by simp only [Category.assoc, hfac]
        _ = s := hv
        _ = t ≫ o := ht.symm
    rw [hvu]
    exact hupt u hu

end AlgebraicGeometry
