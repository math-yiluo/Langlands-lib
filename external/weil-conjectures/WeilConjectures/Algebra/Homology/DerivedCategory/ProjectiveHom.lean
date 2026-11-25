/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-!
# Morphisms out of bounded above complexes of projectives in the derived category

Let `P` be a bounded above cochain complex whose terms are projective. Then `P` is K-projective
(`CochainComplex.isKProjective_of_projective`), so that:

* every morphism `Q.obj P ⟶ Q.obj L` in the derived category is the image of a chain map
  (`DerivedCategory.Q_map_surjective_of_projective`);
* two chain maps `f g : P ⟶ L` have the same image in the derived category if and only if
  they are homotopic (`DerivedCategory.Q_map_eq_Q_map_iff_of_projective`).
-/

@[expose] public section

universe w v u

open CategoryTheory

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- Every morphism `Q.obj P ⟶ Q.obj L` in the derived category out of a bounded above complex
of projectives `P` is the image of a chain map `P ⟶ L`. -/
lemma Q_map_surjective_of_projective (P L : CochainComplex C ℤ) (b : ℤ) [P.IsStrictlyLE b]
    [∀ n, Projective (P.X n)] :
    Function.Surjective (Q.map : (P ⟶ L) → (Q.obj P ⟶ Q.obj L)) := by
  have := CochainComplex.isKProjective_of_projective P b
  exact CochainComplex.IsKProjective.exists_Q_map_eq P L

/-- Two chain maps out of a bounded above complex of projectives have the same image in the
derived category if and only if they are homotopic. -/
lemma Q_map_eq_Q_map_iff_of_projective {P L : CochainComplex C ℤ} (b : ℤ) [P.IsStrictlyLE b]
    [∀ n, Projective (P.X n)] (f g : P ⟶ L) :
    Q.map f = Q.map g ↔ Nonempty (Homotopy f g) := by
  have := CochainComplex.isKProjective_of_projective P b
  refine ⟨fun h ↦ ⟨HomotopyCategory.homotopyOfEq _ _
    ((CochainComplex.IsKProjective.Qh_map_bijective P _).injective ?_)⟩, fun ⟨h⟩ ↦ ?_⟩
  · rw [← cancel_mono ((quotientCompQhIso C).hom.app L), quotientCompQhIso_hom_naturality,
      quotientCompQhIso_hom_naturality, h]
  · rw [← cancel_epi ((quotientCompQhIso C).hom.app P), ← quotientCompQhIso_hom_naturality,
      ← quotientCompQhIso_hom_naturality, HomotopyCategory.eq_of_homotopy _ _ h]

end DerivedCategory
