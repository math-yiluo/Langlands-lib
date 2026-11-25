/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# The section of a proper map fixing an open

Let `u : T₁ ⟶ T₂` be a proper morphism and `j₁ : X ⟶ T₁`, `j₂ : X ⟶ T₂` open immersions with
`j₁ ≫ u = j₂`. Put `V = T₁ ×_{T₂} X`, with projections `b : V ⟶ T₁` and `p : V ⟶ X`, and let
`s : X ⟶ V` be the morphism induced by `j₁` and `𝟙 X`. This file records the geometry of this
square: `p` is proper, `s` is an open immersion with closed image which is a section of `p`, and
`b` identifies `V` with the open subscheme `u⁻¹(j₂(X))` of `T₁`.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.isClopen_range_of_comp_eq_id`: an open immersion which is a
  section of a separated morphism has clopen range.
- `AlgebraicGeometry.isProper_pullback_snd_of_isProper`: the projection `p` is proper, hence
  separated.
- `AlgebraicGeometry.ProperOpenDatum`: the datum `(u, j₁, j₂)`, with its section
  `AlgebraicGeometry.ProperOpenDatum.section` and the properties of the latter.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- Blueprint `proposition-construction-independence-rf-shriek--7`: An open section is also closed.
Let `p : V ⟶ S` be separated and `s : S ⟶ V` an open immersion with `s ≫ p = 𝟙 S`. Then `s` is
proper (`s ≫ p` is, and `p` is separated), so its range is open and closed in `V`; hence
`V` is the disjoint union of the two open subschemes `s(S)` and `V \ s(S)`. -/
theorem Scheme.Hom.isClopen_range_of_comp_eq_id {V S : Scheme.{u}} (p : V ⟶ S) (s : S ⟶ V)
    [IsSeparated p] [IsOpenImmersion s] (h : s ≫ p = 𝟙 S) : IsClopen (Set.range s.base) := by
  have : IsProper (s ≫ p) := h ▸ inferInstance
  have : IsProper s := .of_comp s p
  exact Scheme.Hom.isClopen_range s

/-- Blueprint `proposition-construction-independence-rf-shriek--7`: Properness of the projection of
the comparison square. For `u : T₁ ⟶ T₂` proper and any `j₂ : X ⟶ T₂` (in the blueprint an open
immersion), the projection `p : T₁ ×_{T₂} X ⟶ X` is the base change of `u` along `j₂`, hence
proper and in particular separated. -/
theorem isProper_pullback_snd_of_isProper {T₁ T₂ X : Scheme.{u}} (u : T₁ ⟶ T₂) (j₂ : X ⟶ T₂)
    [IsProper u] : IsProper (pullback.snd u j₂) ∧ IsSeparated (pullback.snd u j₂) :=
  ⟨inferInstance, inferInstance⟩

/-- The datum of the proper-open comparison: a proper morphism `u : T₁ ⟶ T₂` and open
immersions `j₁ : X ⟶ T₁`, `j₂ : X ⟶ T₂` with `j₁ ≫ u = j₂`. -/
structure ProperOpenDatum (X : Scheme.{u}) where
  /-- The source of the proper map. -/
  T₁ : Scheme.{u}
  /-- The target of the proper map. -/
  T₂ : Scheme.{u}
  /-- The proper map. -/
  u : T₁ ⟶ T₂
  /-- The open immersion into the source. -/
  j₁ : X ⟶ T₁
  /-- The open immersion into the target. -/
  j₂ : X ⟶ T₂
  comm : j₁ ≫ u = j₂ := by cat_disch
  isProper : IsProper u := by infer_instance
  isOpenImmersion₁ : IsOpenImmersion j₁ := by infer_instance
  isOpenImmersion₂ : IsOpenImmersion j₂ := by infer_instance

namespace ProperOpenDatum

attribute [instance] isProper isOpenImmersion₁ isOpenImmersion₂
attribute [reassoc (attr := simp)] comm

variable {X : Scheme.{u}} (D : ProperOpenDatum X)

/-- The fibre product `V = T₁ ×_{T₂} X`. -/
noncomputable abbrev V : Scheme.{u} := pullback D.u D.j₂

/-- The projection `b : V ⟶ T₁`, the base change of `j₂` along `u`. -/
noncomputable abbrev b : D.V ⟶ D.T₁ := pullback.fst D.u D.j₂

/-- The projection `p : V ⟶ X`, the base change of `u` along `j₂`. -/
noncomputable abbrev p : D.V ⟶ X := pullback.snd D.u D.j₂

/-- The morphism `s : X ⟶ V` induced by `j₁` and `𝟙 X`. -/
noncomputable def «section» : X ⟶ D.V := pullback.lift D.j₁ (𝟙 X) (by simp)

@[reassoc (attr := simp)]
lemma section_b : D.section ≫ D.b = D.j₁ := by simp [«section»]

@[reassoc (attr := simp)]
lemma section_p : D.section ≫ D.p = 𝟙 X := by simp [«section»]

lemma isPullback : IsPullback D.b D.p D.u D.j₂ := IsPullback.of_hasPullback _ _

instance : IsOpenImmersion D.b := inferInstance

instance : IsProper D.p := inferInstance

instance isOpenImmersion_section : IsOpenImmersion D.section := by
  have : IsOpenImmersion (D.section ≫ D.b) := by rw [section_b]; infer_instance
  exact .of_comp D.section D.b

/-- The range of `b` is `u⁻¹(j₂(X))`. -/
lemma range_b : Set.range D.b.base = D.u.base ⁻¹' Set.range D.j₂.base :=
  Scheme.Pullback.range_fst _ _

/-- Blueprint `proposition-construction-independence-rf-shriek--7`: The section of the comparison
square and the open it fixes. The morphism `s : X ⟶ V` is an open immersion
(`isOpenImmersion_section`) with `s ≫ p = 𝟙 X` and `s ≫ b = j₁`; its range is open and closed in
`V`; through `b` it identifies `X` with the open `j₁(X)`; and `b` is an open immersion identifying
`V` with `u⁻¹(j₂(X))`. -/
theorem section_spec :
    IsOpenImmersion D.section ∧ D.section ≫ D.p = 𝟙 X ∧ D.section ≫ D.b = D.j₁ ∧
      IsClopen (Set.range D.section.base) ∧
      Set.range (D.section ≫ D.b).base = Set.range D.j₁.base ∧
      IsOpenImmersion D.b ∧ Set.range D.b.base = D.u.base ⁻¹' Set.range D.j₂.base :=
  ⟨inferInstance, D.section_p, D.section_b,
    Scheme.Hom.isClopen_range_of_comp_eq_id D.p D.section D.section_p, by rw [section_b],
    inferInstance, D.range_b⟩

lemma isClopen_range_section : IsClopen (Set.range D.section.base) :=
  Scheme.Hom.isClopen_range_of_comp_eq_id D.p D.section D.section_p

instance isClosedImmersion_section : IsClosedImmersion D.section := by
  have : IsProper (D.section ≫ D.p) := D.section_p ▸ inferInstance
  have : IsProper D.section := .of_comp D.section D.p
  exact .of_isOpenImmersion_of_universallyClosed D.section

end ProperOpenDatum

end AlgebraicGeometry
