/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Homology.GrothendieckAbelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Monomorphisms
public import Mathlib.CategoryTheory.Abelian.Monomorphisms
public import WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.DerivabilityStructureKInjectives
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Monomorphic quasi-isomorphisms in a Grothendieck abelian category

Let `C` be a Grothendieck abelian category and `c : ComplexShape ι`. Colimits of shape `J`
are exact in `C` both for `J` filtered (AB5) and for `J` discrete (AB4), so
`HomologicalComplex.isStableUnderColimitsOfShape_quasiIso` shows that quasi-isomorphisms in
`HomologicalComplex C c` are stable under filtered colimits and under coproducts; being
multiplicative, they are then also stable under transfinite composition.

Combining this with the corresponding stability properties of monomorphisms, we obtain that
the class `HomologicalComplex.monoQuasiIso C c` of monomorphisms which are
quasi-isomorphisms is stable under retracts, coproducts, transfinite composition, and (for
cochain complexes) cobase change. The packaged consequence
`CochainComplex.transfiniteCompositions_coproducts_pushouts_le` is the inequality needed to
identify the maps produced by the small object argument in `CochainComplex C ℤ`: it says
that the right hand side of `MorphismProperty.llp_rlp_of_hasSmallObjectArgument` for a
family of monomorphic quasi-isomorphisms consists of monomorphic quasi-isomorphisms.

## Main declarations

* `HomologicalComplex.monoQuasiIso`: the class of monomorphic quasi-isomorphisms, with
  instances `IsStableUnderRetracts`, `IsStableUnderCoproducts`,
  `IsStableUnderTransfiniteComposition` and (for cochain complexes)
  `IsStableUnderCobaseChange`.
* `CochainComplex.transfiniteCompositions_coproducts_pushouts_le`: retracts of transfinite
  compositions of pushouts of coproducts of monomorphic quasi-isomorphisms of cochain
  complexes are monomorphic quasi-isomorphisms.

-/

@[expose] public section

universe w v u t

open CategoryTheory Limits

namespace HomologicalComplex

variable (C : Type u) [Category.{v} C] [Abelian C] {ι : Type t} (c : ComplexShape ι)

section Colimits

variable [IsGrothendieckAbelian.{w} C]

instance isStableUnderFilteredColimits_quasiIso :
    MorphismProperty.IsStableUnderFilteredColimits.{w, w} (quasiIso C c) where
  isStableUnderColimitsOfShape _ := inferInstance

instance isStableUnderCoproducts_quasiIso :
    MorphismProperty.IsStableUnderCoproducts.{w} (quasiIso C c) where
  isStableUnderCoproductsOfShape _ := inferInstance

instance isStableUnderTransfiniteComposition_quasiIso :
    MorphismProperty.IsStableUnderTransfiniteComposition.{w} (quasiIso C c) :=
  inferInstance

end Colimits

section MonoQuasiIso

/-- The class of monomorphisms of homological complexes which are quasi-isomorphisms. -/
def monoQuasiIso : MorphismProperty (HomologicalComplex C c) :=
  MorphismProperty.monomorphisms _ ⊓ quasiIso C c

variable {C c}

@[simp]
lemma monoQuasiIso_iff {K L : HomologicalComplex C c} (f : K ⟶ L) :
    monoQuasiIso C c f ↔ Mono f ∧ QuasiIso f := Iff.rfl

variable (C c)

instance monoQuasiIso.isStableUnderRetracts : (monoQuasiIso C c).IsStableUnderRetracts :=
  inferInstanceAs (MorphismProperty.monomorphisms _ ⊓ quasiIso C c).IsStableUnderRetracts

variable [IsGrothendieckAbelian.{w} C] [Small.{w} ι] [c.HasNoLoop]

instance monoQuasiIso.isStableUnderCoproducts :
    MorphismProperty.IsStableUnderCoproducts.{w} (monoQuasiIso C c) :=
  inferInstanceAs (MorphismProperty.IsStableUnderCoproducts.{w}
    (MorphismProperty.monomorphisms _ ⊓ quasiIso C c))

instance monoQuasiIso.isStableUnderTransfiniteComposition :
    MorphismProperty.IsStableUnderTransfiniteComposition.{w} (monoQuasiIso C c) :=
  inferInstanceAs (MorphismProperty.IsStableUnderTransfiniteComposition.{w}
    (MorphismProperty.monomorphisms _ ⊓ quasiIso C c))

end MonoQuasiIso

end HomologicalComplex

namespace CochainComplex

open HomologicalComplex

variable (C : Type u) [Category.{v} C] [Abelian C]

instance monoQuasiIso.isStableUnderCobaseChange :
    (monoQuasiIso C (ComplexShape.up ℤ)).IsStableUnderCobaseChange := by
  have h : monoQuasiIso C (ComplexShape.up ℤ) =
      quasiIso C (ComplexShape.up ℤ) ⊓ MorphismProperty.monomorphisms _ :=
    inf_comm _ _
  rw [h]
  infer_instance

variable [IsGrothendieckAbelian.{w} C]

/-- Retracts of transfinite compositions of pushouts of coproducts of monomorphic
quasi-isomorphisms of cochain complexes are again monomorphic quasi-isomorphisms. This is
the inequality needed to identify the maps produced by the small object argument in
`CochainComplex C ℤ`. -/
theorem transfiniteCompositions_coproducts_pushouts_le :
    (MorphismProperty.transfiniteCompositions.{w}
        (MorphismProperty.coproducts.{w}
          (monoQuasiIso C (ComplexShape.up ℤ))).pushouts).retracts ≤
      monoQuasiIso C (ComplexShape.up ℤ) := by
  rw [MorphismProperty.retracts_le_iff, MorphismProperty.transfiniteCompositions_le_iff,
    MorphismProperty.pushouts_le_iff, MorphismProperty.coproducts_le_iff]

end CochainComplex
