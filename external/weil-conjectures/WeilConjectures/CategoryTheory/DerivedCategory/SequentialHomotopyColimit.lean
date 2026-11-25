/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Telescope

/-!
# Homotopy colimits of sequences in triangulated categories

Let `X₀ ⟶ X₁ ⟶ ⋯` be a sequence in a pretriangulated category `T` with a coproduct
`∐ₙ Xₙ`. A *homotopy colimit* of the sequence is an object `H` with a morphism
`π : ∐ₙ Xₙ ⟶ H` fitting in a distinguished triangle

`∐ₙ Xₙ --(𝟙 - shift)--> ∐ₙ Xₙ --π--> H ⟶ (∐ₙ Xₙ)[1]`

(`CategoryTheory.Pretriangulated.IsHomotopyColimit`); it is unique up to a (non-unique)
isomorphism compatible with `π`. A triangulated functor preserving countable coproducts sends
homotopy colimits to homotopy colimits
(`CategoryTheory.Pretriangulated.IsHomotopyColimit.map`), so that the homotopy colimit of the
image of a sequence is isomorphic to the image of its homotopy colimit
(`CategoryTheory.Pretriangulated.IsHomotopyColimit.exists_iso_map`, blueprint
`lem-kun-functor-preserves-hocolim`).
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Pretriangulated

variable {T : Type*} [Category* T] [Preadditive T] [HasZeroObject T] [HasShift T ℤ]
  [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T]

/-- A morphism `π : ∐ₙ Xₙ ⟶ H` exhibits `H` as a *homotopy colimit* of the sequence `X` if it
fits in a distinguished triangle `∐ₙ Xₙ --(𝟙 - shift)--> ∐ₙ Xₙ --π--> H ⟶ (∐ₙ Xₙ)[1]`, the
coproduct being given by the colimit cofan `s`. -/
def IsHomotopyColimit (X : ℕ ⥤ T) {s : Cofan X.obj} (hs : IsColimit s) {H : T}
    (π : s.pt ⟶ H) : Prop :=
  ∃ δ : H ⟶ s.pt⟦(1 : ℤ)⟧, Triangle.mk (𝟙 _ - Cofan.telescopeShift hs) π δ ∈ distTriang T

/-- Homotopy colimits exist: complete `𝟙 - shift` to a distinguished triangle. -/
lemma exists_isHomotopyColimit (X : ℕ ⥤ T) {s : Cofan X.obj} (hs : IsColimit s) :
    ∃ (H : T) (π : s.pt ⟶ H), IsHomotopyColimit X hs π := by
  obtain ⟨H, π, δ, h⟩ := distinguished_cocone_triangle (𝟙 _ - Cofan.telescopeShift hs)
  exact ⟨H, π, δ, h⟩

namespace IsHomotopyColimit

/-- Homotopy colimits are unique up to an isomorphism compatible with the maps from the
coproduct. -/
lemma exists_iso {X : ℕ ⥤ T} {s : Cofan X.obj} {hs : IsColimit s} {H H' : T}
    {π : s.pt ⟶ H} {π' : s.pt ⟶ H'} (h : IsHomotopyColimit X hs π)
    (h' : IsHomotopyColimit X hs π') : ∃ e : H ≅ H', π ≫ e.hom = π' := by
  obtain ⟨δ, hT⟩ := h
  obtain ⟨δ', hT'⟩ := h'
  obtain ⟨e, h₁, h₂⟩ := exists_iso_of_arrow_iso _ _ hT hT' (Iso.refl _)
  let e₃ : H ≅ H' := Triangle.π₃.mapIso e
  refine ⟨e₃, ?_⟩
  have := e.hom.comm₂
  dsimp at this h₂
  rw [h₂, Category.id_comp] at this
  exact this

variable {T' : Type*} [Category* T'] [Preadditive T'] [HasZeroObject T'] [HasShift T' ℤ]
  [∀ n : ℤ, (shiftFunctor T' n).Additive] [Pretriangulated T']
  (F : T ⥤ T') [F.CommShift ℤ] [F.IsTriangulated]

/-- The image under `F` of a coproduct cofan of `X` is a coproduct cofan of `X ⋙ F` as soon as
`F` preserves coproducts indexed by `ℕ`. -/
noncomputable def isColimitMapCofan [PreservesColimitsOfShape (Discrete ℕ) F] {X : ℕ ⥤ T}
    {s : Cofan X.obj} (hs : IsColimit s) :
    IsColimit (Cofan.mk (F.obj s.pt) fun n ↦ F.map (s.inj n) : Cofan (X ⋙ F).obj) :=
  (isColimitMapCoconeCofanMkEquiv F X.obj s.inj).1
    (isColimitOfPreserves F (IsColimit.ofIsoColimit hs (Cofan.ext (Iso.refl _) (by simp))))

/-- A triangulated functor sends homotopy colimits to homotopy colimits: if `π` exhibits `H` as a
homotopy colimit of `X`, then `F π` exhibits `F H` as a homotopy colimit of `X ⋙ F`, for any
coproduct cofan structure on `F (∐ Xₙ)` with injections the `F` of those of `∐ Xₙ`. -/
lemma map {X : ℕ ⥤ T} {s : Cofan X.obj} {hs : IsColimit s} {H : T} {π : s.pt ⟶ H}
    (h : IsHomotopyColimit X hs π)
    (hs' : IsColimit (Cofan.mk (F.obj s.pt) fun n ↦ F.map (s.inj n) : Cofan (X ⋙ F).obj)) :
    IsHomotopyColimit (X ⋙ F) hs' (F.map π) := by
  obtain ⟨δ, hT⟩ := h
  have hF : F.map (𝟙 _ - Cofan.telescopeShift hs) = 𝟙 _ - Cofan.telescopeShift hs' :=
    Cofan.IsColimit.hom_ext hs' _ _ fun n ↦ by
      have h₁ := Cofan.inj_telescopeShift hs n
      have h₂ := Cofan.inj_telescopeShift hs' n
      dsimp at h₂ ⊢
      rw [Functor.map_sub, Functor.map_id, Preadditive.comp_sub, Preadditive.comp_sub,
        ← F.map_comp, h₁, h₂, F.map_comp]
  refine ⟨F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app s.pt, ?_⟩
  have e : F.mapTriangle.obj (Triangle.mk (𝟙 _ - Cofan.telescopeShift hs) π δ) =
      Triangle.mk (𝟙 _ - Cofan.telescopeShift hs') (F.map π)
        (F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app s.pt) := by
    rw [← hF]
    rfl
  rw [← e]
  exact F.map_distinguished _ hT

/-- Blueprint `lem-kun-functor-preserves-hocolim`: let `F : T ⥤ T'` be a triangulated functor
between pretriangulated categories which preserves coproducts indexed by `ℕ`. For every
sequence `X` with homotopy colimit `π : ∐ₙ Xₙ ⟶ H`, and every homotopy colimit
`π' : ∐ₙ F(Xₙ) ⟶ H'` of the image sequence `X ⋙ F`, there is an isomorphism
`H' ≅ F(H)` compatible with the canonical maps from `∐ₙ F(Xₙ) ≅ F(∐ₙ Xₙ)`: the homotopy
colimit of the `F(Xₙ)` is `F` of the homotopy colimit of the `Xₙ`.

Since homotopy colimits are only unique up to non-unique isomorphism, "the canonical morphism"
of the blueprint is formalized as the existence of an isomorphism compatible with the maps
from the coproduct. The proof is that of the blueprint: `F` maps the defining distinguished
triangle of `H` to a distinguished triangle, which, as `F` preserves the coproduct, is a
defining triangle of the homotopy colimit of `X ⋙ F`
(`CategoryTheory.Pretriangulated.IsHomotopyColimit.map`). -/
theorem exists_iso_map [PreservesColimitsOfShape (Discrete ℕ) F] {X : ℕ ⥤ T}
    {s : Cofan X.obj} {hs : IsColimit s} {H : T} {π : s.pt ⟶ H}
    (h : IsHomotopyColimit X hs π) {H' : T'} {π' : F.obj s.pt ⟶ H'}
    (h' : IsHomotopyColimit (X ⋙ F) (isColimitMapCofan F hs) π') :
    ∃ e : H' ≅ F.obj H, π' ≫ e.hom = F.map π :=
  exists_iso h' (h.map F (isColimitMapCofan F hs))

end IsHomotopyColimit

end CategoryTheory.Pretriangulated
