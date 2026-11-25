/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.SetTheory.Cardinal.HasCardinalLT
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.GeneratingMonoQuasiIsos

/-!
# The canonical generating set of monomorphic quasi-isomorphisms

Let `C` be a Grothendieck abelian category. In this file we make the canonical choices of the
data `(G, κ)` entering the construction of the family
`CochainComplex.generatingMonoQuasiIsos G κ` of monomorphic quasi-isomorphisms: for `G` we take
the separator `CategoryTheory.separator C` provided by the Grothendieck condition, and
for `κ` we take a regular cardinal `CochainComplex.serpeCardinal C` which dominates `ℵ₀` and
the cardinalities of the subobject lattices of the finite copowers of the separator. Such a
cardinal exists by `HasCardinalLT.exists_regular_cardinal_forall`, as all these types are
`w`-small.

The resulting family `CochainComplex.serpeGeneratingSet C` is the generating set of the model
structure of Serpé on cochain complexes over a Grothendieck abelian category.

## Main definitions and results

- `CochainComplex.serpeCardinal`: the chosen cardinal, characterized by
  `CochainComplex.fact_isRegular_serpeCardinal`,
  `CochainComplex.aleph0_lt_serpeCardinal` and
  `CochainComplex.hasCardinalLT_subobject_serpeCardinal`; the definition itself should never
  be unfolded.
- `CochainComplex.serpeGeneratingSet`: the resulting small family of monomorphic
  quasi-isomorphisms.

## References

* M. Hovey, *Cotorsion pairs, model category structures, and representation theory*, Lemma 6.7
* T. Beke, *Sheafifiable homotopy model categories*, §3
-/

@[expose] public section

universe w v u

namespace CochainComplex

open CategoryTheory Limits

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

variable (C) in
/-- The family of `w`-small types which the cardinal `CochainComplex.serpeCardinal C` is
required to dominate: a copy of `ℕ`, which forces `ℵ₀ < serpeCardinal C`, and the subobject
lattices of the finite copowers of the separator of `C`. -/
private def serpeFamily : Option (ULift.{w} ℕ) → Type w
  | none => ULift.{w} ℕ
  | some n => Shrink.{w} (Subobject (∐ (fun (_ : Fin n.down) ↦ separator C)))

variable (C) in
private lemma exists_serpeCardinal :
    ∃ (κ : Cardinal.{w}), κ.IsRegular ∧ Cardinal.aleph0 < κ ∧
      ∀ (n : ℕ), HasCardinalLT (Subobject (∐ (fun (_ : Fin n) ↦ separator C))) κ := by
  obtain ⟨κ, hκ, h⟩ := HasCardinalLT.exists_regular_cardinal_forall.{w} (serpeFamily.{w} C)
  refine ⟨κ, hκ, ?_, fun n ↦ ?_⟩
  · have h₀ : HasCardinalLT (ULift.{w} ℕ) κ := h none
    rw [hasCardinalLT_iff_cardinal_mk_lt] at h₀
    simpa using h₀
  · rw [hasCardinalLT_iff_of_equiv (equivShrink.{w} _)]
    exact h (some (ULift.up n))

variable (C) in
/-- A regular cardinal `κ` with `ℵ₀ < κ` such that for every `n : ℕ`, the subobjects of the
`n`-fold copower of the separator of `C` form a type of cardinality `< κ`. -/
@[no_expose] noncomputable def serpeCardinal : Cardinal.{w} :=
  (exists_serpeCardinal.{w} C).choose

variable (C) in
/-- `serpeCardinal C` is regular. This is not a global instance: its conclusion
`Fact (Cardinal.IsRegular _)` would make instance search try every category `C`. -/
theorem fact_isRegular_serpeCardinal : Fact (serpeCardinal.{w} C).IsRegular :=
  ⟨(exists_serpeCardinal.{w} C).choose_spec.1⟩

variable (C) in
lemma aleph0_lt_serpeCardinal : Cardinal.aleph0 < serpeCardinal.{w} C :=
  (exists_serpeCardinal.{w} C).choose_spec.2.1

variable (C) in
lemma hasCardinalLT_subobject_serpeCardinal (n : ℕ) :
    HasCardinalLT (Subobject (∐ (fun (_ : Fin n) ↦ separator C))) (serpeCardinal.{w} C) :=
  (exists_serpeCardinal.{w} C).choose_spec.2.2 n

variable (C) in
/-- A small generating set of monomorphic quasi-isomorphisms in `CochainComplex C ℤ`
(Serpé; Hovey, *Cotorsion pairs…*, Lemma 6.7; Beke, *Sheafifiable homotopy model
categories*, §3). -/
noncomputable def serpeGeneratingSet : MorphismProperty (CochainComplex C ℤ) :=
  generatingMonoQuasiIsos (separator C) (serpeCardinal.{w} C)

variable (C) in
lemma serpeGeneratingSet_le :
    serpeGeneratingSet C ≤ MorphismProperty.monomorphisms (CochainComplex C ℤ) ⊓
      HomologicalComplex.quasiIso C (ComplexShape.up ℤ) := by
  dsimp only [serpeGeneratingSet]
  exact generatingMonoQuasiIsos_le _ _

variable (C) in
instance isSmall_serpeGeneratingSet : MorphismProperty.IsSmall.{w} (serpeGeneratingSet C) := by
  dsimp only [serpeGeneratingSet]
  infer_instance

end CochainComplex
