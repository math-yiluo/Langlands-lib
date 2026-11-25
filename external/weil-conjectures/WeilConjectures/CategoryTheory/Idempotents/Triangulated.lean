/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Idempotents.Pretriangulated
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Triangulated
public import Mathlib.CategoryTheory.Idempotents.Biproducts

/-!
# The Karoubi envelope of a triangulated category is triangulated

Let `C` be a triangulated category. The Karoubi envelope `Karoubi C`, with the pretriangulated
structure of `WeilConjectures.CategoryTheory.Idempotents.Pretriangulated`, satisfies the octahedral
axiom, following Balmer and Schlichting. A composable pair `X₁ ⟶ X₂ ⟶ X₃` of `Karoubi C`, padded by
zero morphisms on the complements `Xᵢ.complement`, is isomorphic to the image of a composable pair
of `C`, so it has an octahedron; the padding is then removed one object at a time
(`CategoryTheory.Triangulated.nonempty_octahedron_of_pad₁` and its variants), using that the
distinguished triangles of `Karoubi C` are stable under retracts.

## Main statements

- `CategoryTheory.Idempotents.Karoubi.distinguished_of_retract`: retracts of distinguished
  triangles of `Karoubi C` are distinguished.
- `CategoryTheory.Idempotents.Karoubi.isTriangulated`: the octahedral axiom for `Karoubi C`.

## References

* Paul Balmer and Marco Schlichting, *Idempotent completion of triangulated categories*,
  J. Algebra 236 (2001), Theorem 1.12
-/

@[expose] public section

namespace CategoryTheory

open Category Limits Preadditive Pretriangulated Triangulated

namespace Idempotents

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

namespace Karoubi

/-- The distinguished triangles of the Karoubi envelope are stable under retracts. -/
lemma distinguished_of_retract (T T' : Triangle (Karoubi C))
    (hT' : T' ∈ distTriang (Karoubi C)) (r : Retract T T') : T ∈ distTriang (Karoubi C) := by
  obtain ⟨T₀, h₀, ⟨r'⟩⟩ := hT'
  exact ⟨T₀, h₀, ⟨r.trans r'⟩⟩

omit [HasZeroObject C] [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] in
/-- Under the decompositions `P ⊞ P.complement ≅ P.X`, a morphism `u : P ⟶ Q` of the Karoubi
envelope padded by zero on the complements is the image of `u.f`. -/
lemma biprod_fst_comp_comp_inl_decomposition_hom {P Q : Karoubi C} (u : P ⟶ Q) :
    ((biprod.fst : P ⊞ P.complement ⟶ P) ≫ u) ≫ biprod.inl ≫ Q.decomposition.hom =
      P.decomposition.hom ≫ (toKaroubi C).map u.f := by
  apply biprod.hom_ext'
  · ext
    simp [decomposition]
  · simp only [decomposition, assoc, biprod.inr_fst_assoc, zero_comp, biprod.inr_desc_assoc]
    ext
    simp only [comp_f, decompId_i_f, complement_p, toKaroubi_map_f, sub_comp,
      p_comp, zero_def]
    exact (sub_eq_zero.2 (id_comp _)).symm

end Karoubi

/-- The Karoubi envelope of a triangulated category satisfies the octahedral axiom
(Balmer–Schlichting, Theorem 1.12).

A composable pair `X₁ ⟶ X₂ ⟶ X₃` of the envelope, padded by zero maps on the complements
`Xᵢ.complement`, becomes the image of a composable pair of `C`, which has an octahedron. The
padding is removed one object at a time (`CategoryTheory.Triangulated.nonempty_octahedron_of_pad₁`,
`…pad₂`, `…pad₃`), using that the distinguished triangles of the envelope are stable under
retracts. -/
theorem Karoubi.isTriangulated [IsTriangulated C] : IsTriangulated (Karoubi C) := by
  refine IsTriangulated.mk' (fun X₁ X₂ X₃ u₁₂ u₂₃ ↦ ?_)
  obtain ⟨Z₁₂, v₁₂, w₁₂, h₁₂⟩ := Pretriangulated.distinguished_cocone_triangle u₁₂
  obtain ⟨Z₂₃, v₂₃, w₂₃, h₂₃⟩ := Pretriangulated.distinguished_cocone_triangle u₂₃
  obtain ⟨Z₁₃, v₁₃, w₁₃, h₁₃⟩ := Pretriangulated.distinguished_cocone_triangle (u₁₂ ≫ u₂₃)
  refine ⟨X₁, X₂, X₃, Z₁₂, Z₂₃, Z₁₃, u₁₂, u₂₃, Iso.refl _, Iso.refl _, Iso.refl _, by simp,
    by simp, v₁₂, w₁₂, h₁₂, v₂₃, w₂₃, h₂₃, v₁₃, w₁₃, h₁₃, ?_⟩
  refine nonempty_octahedron_of_pad₁ Karoubi.distinguished_of_retract X₁.complement ?_
  refine nonempty_octahedron_of_pad₂ Karoubi.distinguished_of_retract X₂.complement ?_
  refine nonempty_octahedron_of_pad₃ Karoubi.distinguished_of_retract X₃.complement ?_
  obtain ⟨_, _, _, hc₁₂⟩ := Pretriangulated.distinguished_cocone_triangle u₁₂.f
  obtain ⟨_, _, _, hc₂₃⟩ := Pretriangulated.distinguished_cocone_triangle u₂₃.f
  obtain ⟨_, _, _, hc₁₃⟩ := Pretriangulated.distinguished_cocone_triangle (u₁₂.f ≫ u₂₃.f)
  exact ⟨Octahedron.ofIso _ _ _ _ _ _ _ _ _ _ _ X₁.decomposition X₂.decomposition
    X₃.decomposition (by simpa using Karoubi.biprod_fst_comp_comp_inl_decomposition_hom u₁₂)
    (by simpa using Karoubi.biprod_fst_comp_comp_inl_decomposition_hom u₂₃) _ _ _ _ _ _ _ _ _
    ((someOctahedron rfl hc₁₂ hc₂₃ hc₁₃).map (toKaroubi C))⟩

end Idempotents

end CategoryTheory
