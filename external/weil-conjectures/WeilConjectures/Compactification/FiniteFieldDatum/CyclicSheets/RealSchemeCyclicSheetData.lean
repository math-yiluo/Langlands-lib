/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Scheme data for cyclic sheets of a finite constant extension

Source: blueprint `theorem-real-constructible-sheaves-are-mixed--1`, proof paragraph 5, the copies
of the base in the finite constant extension before summation
(blueprint: def-zl-real-scheme-cyclic-sheet-data).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.FiniteFieldDatum.CyclicSheets

variable (D : FiniteFieldDatum.{u}) (m : ℕ) (hm : 1 ≤ m)

/-- The two specified field inclusions compose to the original inclusion.
Source: blueprint `theorem-real-constructible-sheaves-are-mixed--1`, proof paragraph 5
(blueprint: def-zl-real-scheme-cyclic-sheet-data).
Proof: the unique-subfield theorem specifies that the subfield inclusion composed
with `extensionEmbedding` is `algebraMap`. Contravariant Spec gives this equality. -/
theorem specInclusion_comp :
    Spec.map (CommRingCat.ofHom (D.extensionSubfield m hm).subtype) ≫
        Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm)) =
      Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1
  exact congrArg CommRingCat.ofHom
    (FiniteField.exists_unique_subfield_of_closure D.p D.a D.q D.prime
      D.exponent_pos D.cardinality_eq D.k₀ D.card_base D.k m hm).choose_spec.2.2.2.2.2.2.choose_spec

variable (X₀ : Over (Spec (.of D.k₀)))

/-- The actual constant extension, with its structure over the new finite field.
Source: blueprint `theorem-real-constructible-sheaves-are-mixed--1`, proof paragraph 5
(blueprint: def-zl-real-scheme-cyclic-sheet-data). -/
def model : Over (Spec (.of (D.extensionSubfield m hm))) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm)))).obj X₀

/-- The same constant extension viewed over the original finite field.
Source: blueprint `theorem-real-constructible-sheaves-are-mixed--1`, proof paragraph 5
(blueprint: def-zl-real-scheme-cyclic-sheet-data). -/
def originalModel : Over (Spec (.of D.k₀)) :=
  Over.mk ((model D m hm X₀).hom ≫
    Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm)))

/-- The first projection is a morphism over the original finite field.
Source: blueprint `theorem-real-constructible-sheaves-are-mixed--1`, proof paragraph 5
(blueprint: def-zl-real-scheme-cyclic-sheet-data). -/
def projection : originalModel D m hm X₀ ⟶ X₀ :=
  Over.homMk (pullback.fst X₀.hom
    (Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm)))) pullback.condition

/-- The source of the inclusion sheet, before identifying it with X.
Source: blueprint `theorem-real-constructible-sheaves-are-mixed--1`, proof paragraph 5
(blueprint: def-zl-real-scheme-cyclic-sheet-data). -/
def sheetSource : Scheme.{u} :=
  pullback (model D m hm X₀).hom
    (Spec.map (CommRingCat.ofHom (D.extensionSubfield m hm).subtype))

/-- Associativity of the two constant base changes gives the specified e.
Source: blueprint `theorem-real-constructible-sheaves-are-mixed--1`, proof paragraph 5
(blueprint: def-zl-real-scheme-cyclic-sheet-data). -/
def fiberIso [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    sheetSource D m hm X₀ ≅ (D.geometricFiber X₀).left :=
  pullbackLeftPullbackSndIso X₀.hom
      (Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm)))
      (Spec.map (CommRingCat.ofHom (D.extensionSubfield m hm).subtype)) ≪≫
    pullback.congrHom rfl (specInclusion_comp D m hm)

/-- The two components of s agree over the original finite field.
Source: blueprint `theorem-real-constructible-sheaves-are-mixed--1`, proof paragraph 5
(blueprint: def-zl-real-scheme-cyclic-sheet-data).
Proof: compose the pullback projection identity with Spec of the base inclusion,
and use `specInclusion_comp` to identify its composite with Spec of the original
inclusion. This is exactly the compatibility for the lift defining s. -/
theorem sheet_compatible :
    pullback.fst (model D m hm X₀).hom
        (Spec.map (CommRingCat.ofHom (D.extensionSubfield m hm).subtype)) ≫
        (originalModel D m hm X₀).hom =
      pullback.snd (model D m hm X₀).hom
        (Spec.map (CommRingCat.ofHom (D.extensionSubfield m hm).subtype)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)) := by
  change pullback.fst (model D m hm X₀).hom _ ≫
    ((model D m hm X₀).hom ≫ Spec.map
      (CommRingCat.ofHom (D.extensionEmbedding m hm))) = _
  rw [← Category.assoc, pullback.condition, Category.assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  rw [CommRingCat.ofHom_comp, Spec.map_comp, specInclusion_comp]

/-- The canonical map s into Y from the two projections of the sheet source.
Source: blueprint `theorem-real-constructible-sheaves-are-mixed--1`, proof paragraph 5
(blueprint: def-zl-real-scheme-cyclic-sheet-data). -/
def sheet : sheetSource D m hm X₀ ⟶
    pullback (originalModel D m hm X₀).hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _) (sheet_compatible D m hm X₀)

/-- The distinguished inclusion j₀=s∘e⁻¹ uses the chosen subfield inclusion.
Source: blueprint `theorem-real-constructible-sheaves-are-mixed--1`, proof paragraph 5
(blueprint: def-zl-real-scheme-cyclic-sheet-data). -/
def inclusion [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    (D.geometricFiber X₀).left ⟶
      pullback (originalModel D m hm X₀).hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) :=
  (fiberIso D m hm X₀).inv ≫ sheet D m hm X₀

end WeilConjectures.FiniteFieldDatum.CyclicSheets
