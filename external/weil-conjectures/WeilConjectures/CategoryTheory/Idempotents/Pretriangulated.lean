/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Idempotents.Shift
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Retract
public import WeilConjectures.Mathlib.Algebra.Ring.Idempotent

/-!
# The Karoubi envelope of a pretriangulated category

Let `C` be a pretriangulated category. Following Balmer and Schlichting, we equip the Karoubi
envelope `Karoubi C` with the shift `(K, e)⟦1⟧ = (K⟦1⟧, e⟦1⟧)` and with the distinguished
triangles the retracts (in the category of triangles) of images of distinguished triangles of
`C`. This makes `Karoubi C` a pretriangulated category, and the inclusion `C ⥤ Karoubi C` a
triangulated functor.

The key input is the lifting of idempotents along triangles
(`CategoryTheory.Pretriangulated.exists_idempotent_of_distTriang`): if `(a, b)` is a pair of
idempotents on the first two terms of a distinguished triangle compatible with its first
morphism, then it extends to an idempotent endomorphism `(a, b, c)` of the triangle. Indeed, any
extension `(a, b, x)` given by the axioms satisfies `(x² - x)² = 0`, so that `c = 3x² - 2x³`
is idempotent.

## References

* Paul Balmer and Marco Schlichting, *Idempotent completion of triangulated categories*,
  J. Algebra 236 (2001)
-/

@[expose] public section

namespace CategoryTheory

open Category Limits Preadditive ZeroObject Pretriangulated Idempotents

namespace Pretriangulated

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

/-- An endomorphism of the third term of a distinguished triangle which is killed by both
adjacent morphisms has square zero. -/
lemma comp_eq_zero_of_distTriang (T : Triangle C) (hT : T ∈ distTriang C)
    (h : T.obj₃ ⟶ T.obj₃) (h₂ : T.mor₂ ≫ h = 0) (h₃ : h ≫ T.mor₃ = 0) : h ≫ h = 0 := by
  obtain ⟨k, hk⟩ := Triangle.yoneda_exact₃ T hT h h₂
  obtain ⟨l, hl⟩ := Triangle.coyoneda_exact₃ T hT h h₃
  rw [show h ≫ h = (l ≫ T.mor₂) ≫ (T.mor₃ ≫ k) by rw [← hl, ← hk], assoc,
    reassoc_of% (comp_distTriang_mor_zero₂₃ T hT), zero_comp, comp_zero]

/-- The polynomial `3t² - 2t³` (written without numerals) applied to an endomorphism. -/
def idemPoly {X : C} (x : X ⟶ X) : X ⟶ X :=
  x ≫ x + x ≫ x + x ≫ x - x ≫ x ≫ x - x ≫ x ≫ x

omit [HasZeroObject C] [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] in
lemma comp_idemPoly {X Y : C} (f : Y ⟶ X) (x : X ⟶ X) (y : Y ⟶ Y) (h : f ≫ x = y ≫ f) :
    f ≫ idemPoly x = idemPoly y ≫ f := by
  simp only [idemPoly, comp_add, comp_sub, add_comp, sub_comp, assoc, reassoc_of% h, h]

omit [HasZeroObject C] [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] in
lemma idemPoly_of_idem {X : C} (x : X ⟶ X) (hx : x ≫ x = x) : idemPoly x = x := by
  simp only [idemPoly, hx]
  abel

omit [HasZeroObject C] [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] in
lemma idemPoly_idem {X : C} (x : X ⟶ X) (h : (x ≫ x - x) ≫ (x ≫ x - x) = 0) :
    idemPoly x ≫ idemPoly x = idemPoly x := by
  have := idem_of_sub_mul_sub_eq_zero (R := End X) (.of x)
    (End.ext (show (x ≫ x - x) ≫ (x ≫ x - x) = 0 from h))
  exact congr($(this).asHom)

/-- **Lifting of idempotents along a distinguished triangle**: a pair of idempotents on the first
two terms of a distinguished triangle, compatible with its first morphism, extends to an
idempotent endomorphism of the triangle:

```
  T.obj₁ ──T.mor₁──▶ T.obj₂ ──T.mor₂──▶ T.obj₃ ──T.mor₃──▶ T.obj₁⟦1⟧
    │                  │                  ┊                   │
    a                  b                  c                 a⟦1⟧
    ▼                  ▼                  ▼                   ▼
  T.obj₁ ──T.mor₁──▶ T.obj₂ ──T.mor₂──▶ T.obj₃ ──T.mor₃──▶ T.obj₁⟦1⟧
```

If `x` is any completion given by the axioms, then `(x² - x)² = 0`, and `c = 3x² - 2x³` is an
idempotent completion. -/
lemma exists_idempotent_of_distTriang (T : Triangle C) (hT : T ∈ distTriang C)
    (a : T.obj₁ ⟶ T.obj₁) (b : T.obj₂ ⟶ T.obj₂) (ha : a ≫ a = a) (hb : b ≫ b = b)
    (hab : T.mor₁ ≫ b = a ≫ T.mor₁) :
    ∃ (c : T.obj₃ ⟶ T.obj₃), c ≫ c = c ∧ T.mor₂ ≫ c = b ≫ T.mor₂ ∧
      T.mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ T.mor₃ := by
  obtain ⟨x, hx₂, hx₃⟩ := complete_distinguished_triangle_morphism T T hT hT a b hab
  refine ⟨idemPoly x, idemPoly_idem x ?_, ?_, ?_⟩
  · refine comp_eq_zero_of_distTriang T hT _ ?_ ?_
    · rw [comp_sub, reassoc_of% hx₂, hx₂, reassoc_of% hb, sub_self]
    · rw [sub_comp, assoc, ← hx₃, ← reassoc_of% hx₃, ← Functor.map_comp, ha, sub_self]
  · rw [comp_idemPoly _ _ _ hx₂, idemPoly_of_idem _ hb]
  · have h₃' : a⟦(1 : ℤ)⟧' ≫ a⟦(1 : ℤ)⟧' = a⟦(1 : ℤ)⟧' := by rw [← Functor.map_comp, ha]
    rw [← idemPoly_of_idem _ h₃']
    exact comp_idemPoly _ _ _ hx₃

end Pretriangulated

namespace Idempotents

variable (C : Type*) [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

instance : HasZeroObject (Karoubi C) :=
  ⟨⟨(toKaroubi C).obj 0, (toKaroubi C).map_isZero (isZero_zero C)⟩⟩

instance (n : ℤ) : (shiftFunctor (Karoubi C) n).Additive where
  map_add := by intros; ext; simp

variable {C}

namespace Karoubi

omit [Preadditive C] [HasZeroObject C] [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] in
lemma comm_of_comp_eq {X Y : C} {p : X ⟶ X} {q : Y ⟶ Y} (f : X ⟶ Y) (hq : q ≫ q = q)
    (h : f ≫ q = p ≫ f) : p ≫ (f ≫ q) ≫ q = f ≫ q := by
  rw [assoc, hq, ← assoc, ← h, assoc, hq]

section TriangleOfIdem

variable (T : Triangle C) (E : T ⟶ T) (hE : E ≫ E = E)

include hE

omit [Preadditive C] [HasZeroObject C] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] in
lemma idem_hom₁ : E.hom₁ ≫ E.hom₁ = E.hom₁ := by
  rw [← Pretriangulated.comp_hom₁, hE]

omit [Preadditive C] [HasZeroObject C] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] in
lemma idem_hom₂ : E.hom₂ ≫ E.hom₂ = E.hom₂ := by
  rw [← Pretriangulated.comp_hom₂, hE]

omit [Preadditive C] [HasZeroObject C] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] in
lemma idem_hom₃ : E.hom₃ ≫ E.hom₃ = E.hom₃ := by
  rw [← Pretriangulated.comp_hom₃, hE]

/-- The object `(T.obj₁, E.hom₁)` of the Karoubi envelope. -/
def objOfIdem₁ : Karoubi C := ⟨T.obj₁, E.hom₁, idem_hom₁ T E hE⟩

/-- The object `(T.obj₂, E.hom₂)` of the Karoubi envelope. -/
def objOfIdem₂ : Karoubi C := ⟨T.obj₂, E.hom₂, idem_hom₂ T E hE⟩

/-- The object `(T.obj₃, E.hom₃)` of the Karoubi envelope. -/
def objOfIdem₃ : Karoubi C := ⟨T.obj₃, E.hom₃, idem_hom₃ T E hE⟩

/-- The image of an idempotent endomorphism `E` of a triangle `T` of `C`: the triangle of the
Karoubi envelope with objects `(T.objᵢ, E.homᵢ)`. -/
@[simps!]
noncomputable def triangleOfIdem : Triangle (Karoubi C) :=
  Triangle.mk (X := objOfIdem₁ T E hE) (Y := objOfIdem₂ T E hE) (Z := objOfIdem₃ T E hE)
    ⟨T.mor₁ ≫ E.hom₂, comm_of_comp_eq _ (idem_hom₂ T E hE) E.comm₁⟩
    ⟨T.mor₂ ≫ E.hom₃, comm_of_comp_eq _ (idem_hom₃ T E hE) E.comm₂⟩
    ⟨T.mor₃ ≫ E.hom₁⟦(1 : ℤ)⟧', comm_of_comp_eq _
      (by rw [← Functor.map_comp, idem_hom₁ T E hE]) E.comm₃⟩

/-- The image of an idempotent endomorphism of a triangle `T` is a retract of `T`, in the
Karoubi envelope. -/
noncomputable def retractTriangleOfIdem :
    Retract (triangleOfIdem T E hE) ((toKaroubi C).mapTriangle.obj T) where
  i := Triangle.homMk (triangleOfIdem T E hE) ((toKaroubi C).mapTriangle.obj T)
    (⟨E.hom₁, by simp [objOfIdem₁, idem_hom₁ T E hE]⟩ : objOfIdem₁ T E hE ⟶ (toKaroubi C).obj _)
    (⟨E.hom₂, by simp [objOfIdem₂, idem_hom₂ T E hE]⟩ : objOfIdem₂ T E hE ⟶ (toKaroubi C).obj _)
    (⟨E.hom₃, by simp [objOfIdem₃, idem_hom₃ T E hE]⟩ : objOfIdem₃ T E hE ⟶ (toKaroubi C).obj _)
    (by
      ext
      change (T.mor₁ ≫ E.hom₂) ≫ E.hom₂ = E.hom₁ ≫ T.mor₁
      rw [assoc, idem_hom₂ T E hE, E.comm₁])
    (by
      ext
      change (T.mor₂ ≫ E.hom₃) ≫ E.hom₃ = E.hom₂ ≫ T.mor₂
      rw [assoc, idem_hom₃ T E hE, E.comm₂])
    (by
      ext
      change (T.mor₃ ≫ E.hom₁⟦(1 : ℤ)⟧') ≫ E.hom₁⟦(1 : ℤ)⟧' = E.hom₃ ≫ T.mor₃ ≫ 𝟙 _
      rw [assoc, ← Functor.map_comp, idem_hom₁ T E hE, E.comm₃, comp_id])
  r := Triangle.homMk ((toKaroubi C).mapTriangle.obj T) (triangleOfIdem T E hE)
    (⟨E.hom₁, by simp [objOfIdem₁, idem_hom₁ T E hE]⟩ : (toKaroubi C).obj _ ⟶ objOfIdem₁ T E hE)
    (⟨E.hom₂, by simp [objOfIdem₂, idem_hom₂ T E hE]⟩ : (toKaroubi C).obj _ ⟶ objOfIdem₂ T E hE)
    (⟨E.hom₃, by simp [objOfIdem₃, idem_hom₃ T E hE]⟩ : (toKaroubi C).obj _ ⟶ objOfIdem₃ T E hE)
    (by
      ext
      change T.mor₁ ≫ E.hom₂ = E.hom₁ ≫ T.mor₁ ≫ E.hom₂
      rw [E.comm₁, ← assoc, idem_hom₁ T E hE])
    (by
      ext
      change T.mor₂ ≫ E.hom₃ = E.hom₂ ≫ T.mor₂ ≫ E.hom₃
      rw [E.comm₂, ← assoc, idem_hom₂ T E hE])
    (by
      ext
      change (T.mor₃ ≫ 𝟙 _) ≫ E.hom₁⟦(1 : ℤ)⟧' = E.hom₃ ≫ T.mor₃ ≫ E.hom₁⟦(1 : ℤ)⟧'
      rw [comp_id, E.comm₃, ← assoc, idem_hom₃ T E hE])
  retract := by
    ext
    · exact idem_hom₁ T E hE
    · exact idem_hom₂ T E hE
    · exact idem_hom₃ T E hE

end TriangleOfIdem

variable (C) in
/-- The distinguished triangles of the Karoubi envelope: the retracts, in the category of
triangles, of images of distinguished triangles of `C`. -/
def distinguishedTriangles : Set (Triangle (Karoubi C)) :=
  fun T ↦ ∃ (T' : Triangle C) (_ : T' ∈ distTriang C),
    Nonempty (Retract T ((toKaroubi C).mapTriangle.obj T'))

lemma isomorphic_distinguished (T₁ : Triangle (Karoubi C)) (h₁ : T₁ ∈ distinguishedTriangles C)
    (T₂ : Triangle (Karoubi C)) (e : T₂ ≅ T₁) : T₂ ∈ distinguishedTriangles C := by
  obtain ⟨T', hT', ⟨r⟩⟩ := h₁
  exact ⟨T', hT', ⟨(Retract.ofIso e).trans r⟩⟩

lemma triangleOfIdem_distinguished (T : Triangle C) (hT : T ∈ distTriang C) (E : T ⟶ T)
    (hE : E ≫ E = E) : triangleOfIdem T E hE ∈ distinguishedTriangles C :=
  ⟨T, hT, ⟨retractTriangleOfIdem T E hE⟩⟩

lemma distinguished_cocone_triangle {X Y : Karoubi C} (f : X ⟶ Y) :
    ∃ (Z : Karoubi C) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distinguishedTriangles C := by
  obtain ⟨Z, g, h, hT⟩ := Pretriangulated.distinguished_cocone_triangle f.f
  obtain ⟨c, hc, hc₂, hc₃⟩ := Pretriangulated.exists_idempotent_of_distTriang _ hT X.p Y.p
    X.idem Y.idem (by simp)
  let E : Triangle.mk f.f g h ⟶ Triangle.mk f.f g h := Triangle.homMk _ _ X.p Y.p c (by simp)
    hc₂ hc₃
  have hE : E ≫ E = E := by ext <;> simp [E, hc]
  refine ⟨_, (triangleOfIdem _ E hE).mor₂, (triangleOfIdem _ E hE).mor₃,
    isomorphic_distinguished _ (triangleOfIdem_distinguished _ hT E hE) _ ?_⟩
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ (by simp) (by simp)
  ext
  simp [E]

lemma contractible_distinguished (X : Karoubi C) :
    contractibleTriangle X ∈ distinguishedTriangles C := by
  let E : contractibleTriangle X.X ⟶ contractibleTriangle X.X :=
    Triangle.homMk _ _ X.p X.p 0 ((id_comp _).trans (comp_id _).symm) (by simp) (by simp)
  have hE : E ≫ E = E := by ext <;> simp [E]
  refine isomorphic_distinguished _
    (triangleOfIdem_distinguished _ (Pretriangulated.contractible_distinguished X.X) E hE) _ ?_
  have h₃ : IsZero (objOfIdem₃ _ E hE) := by
    rw [IsZero.iff_id_eq_zero]
    ext
    exact (isZero_zero C).eq_of_src _ _
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) ((isZero_zero _).iso h₃) ?_ ?_ ?_
  · ext
    simp only [E, contractibleTriangle]
    simp only [zero_def, Triangle.mk_mor₁, Iso.refl_hom, comp_id, id_f, id_comp,
      triangleOfIdem_mor₁_f, Triangle.homMk_hom₁]
    exact (Category.comp_id _).symm
  · exact h₃.eq_of_tgt _ _
  · exact (isZero_zero _).eq_of_src _ _

lemma rotate_distinguished_triangle (T : Triangle (Karoubi C)) :
    T ∈ distinguishedTriangles C ↔ T.rotate ∈ distinguishedTriangles C := by
  constructor
  · rintro ⟨T', hT', ⟨r⟩⟩
    exact ⟨T'.rotate, rot_of_distTriang _ hT', ⟨(r.map (rotate _)).trans
      (Retract.ofIso (((toKaroubi C).mapTriangleRotateIso).app T'))⟩⟩
  · rintro ⟨T', hT', ⟨r⟩⟩
    exact ⟨T'.invRotate, inv_rot_of_distTriang _ hT', ⟨(Retract.ofIso
      ((rotCompInvRot (C := Karoubi C)).app T)).trans ((r.map (invRotate _)).trans
      (Retract.ofIso (((toKaroubi C).mapTriangleInvRotateIso).app T')))⟩⟩

omit [Preadditive C] [HasZeroObject C] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] in
/-- The morphism axiom passes to retracts of triangles. -/
lemma exists_hom₃_of_retract {D : Type*} [Category* D] [HasShift D ℤ]
    {T₁ T₂ U₁ U₂ : Triangle D} (r₁ : Retract T₁ U₁) (r₂ : Retract T₂ U₂)
    (hU : ∀ (a : U₁.obj₁ ⟶ U₂.obj₁) (b : U₁.obj₂ ⟶ U₂.obj₂), U₁.mor₁ ≫ b = a ≫ U₂.mor₁ →
      ∃ c : U₁.obj₃ ⟶ U₂.obj₃, U₁.mor₂ ≫ c = b ≫ U₂.mor₂ ∧ U₁.mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ U₂.mor₃)
    (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂) (comm : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) :
    ∃ c : T₁.obj₃ ⟶ T₂.obj₃, T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧
      T₁.mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ T₂.mor₃ := by
  have h₁₁ : r₁.i.hom₁ ≫ r₁.r.hom₁ = 𝟙 _ := by rw [← comp_hom₁, r₁.retract, id_hom₁]
  have h₁₂ : r₁.i.hom₂ ≫ r₁.r.hom₂ = 𝟙 _ := by rw [← comp_hom₂, r₁.retract, id_hom₂]
  have h₂₁ : r₂.i.hom₁ ≫ r₂.r.hom₁ = 𝟙 _ := by rw [← comp_hom₁, r₂.retract, id_hom₁]
  have h₂₂ : r₂.i.hom₂ ≫ r₂.r.hom₂ = 𝟙 _ := by rw [← comp_hom₂, r₂.retract, id_hom₂]
  obtain ⟨c', hc₂, hc₃⟩ := hU (r₁.r.hom₁ ≫ a ≫ r₂.i.hom₁) (r₁.r.hom₂ ≫ b ≫ r₂.i.hom₂) (by
    rw [reassoc_of% r₁.r.comm₁, reassoc_of% comm, r₂.i.comm₁, assoc, assoc])
  refine ⟨r₁.i.hom₃ ≫ c' ≫ r₂.r.hom₃, ?_, ?_⟩
  · rw [reassoc_of% r₁.i.comm₂, reassoc_of% hc₂, r₂.r.comm₂]
    simp only [reassoc_of% h₂₂, reassoc_of% h₁₂]
  · rw [assoc, assoc, ← r₂.r.comm₃, ← reassoc_of% hc₃, ← reassoc_of% r₁.i.comm₃]
    simp only [← Functor.map_comp, assoc, reassoc_of% h₁₁, h₂₁, comp_id]

/-- The morphism axiom holds for images of distinguished triangles of `C`. -/
lemma exists_hom₃_mapTriangle (T₁ T₂ : Triangle C) (h₁ : T₁ ∈ distTriang C)
    (h₂ : T₂ ∈ distTriang C)
    (a : ((toKaroubi C).mapTriangle.obj T₁).obj₁ ⟶ ((toKaroubi C).mapTriangle.obj T₂).obj₁)
    (b : ((toKaroubi C).mapTriangle.obj T₁).obj₂ ⟶ ((toKaroubi C).mapTriangle.obj T₂).obj₂)
    (comm : ((toKaroubi C).mapTriangle.obj T₁).mor₁ ≫ b =
      a ≫ ((toKaroubi C).mapTriangle.obj T₂).mor₁) :
    ∃ c : ((toKaroubi C).mapTriangle.obj T₁).obj₃ ⟶ ((toKaroubi C).mapTriangle.obj T₂).obj₃,
      ((toKaroubi C).mapTriangle.obj T₁).mor₂ ≫ c = b ≫ ((toKaroubi C).mapTriangle.obj T₂).mor₂ ∧
      ((toKaroubi C).mapTriangle.obj T₁).mor₃ ≫ a⟦(1 : ℤ)⟧' =
        c ≫ ((toKaroubi C).mapTriangle.obj T₂).mor₃ := by
  obtain ⟨c, hc₂, hc₃⟩ := Pretriangulated.complete_distinguished_triangle_morphism _ _ h₁ h₂
    a.f b.f (congrArg Karoubi.Hom.f comm)
  refine ⟨(toKaroubi C).map c, ?_, ?_⟩
  · ext; exact hc₂
  · ext
    change (T₁.mor₃ ≫ 𝟙 _) ≫ a.f⟦(1 : ℤ)⟧' = c ≫ T₂.mor₃ ≫ 𝟙 _
    rw [comp_id, comp_id, hc₃]

lemma complete_distinguished_triangle_morphism (T₁ T₂ : Triangle (Karoubi C))
    (h₁ : T₁ ∈ distinguishedTriangles C) (h₂ : T₂ ∈ distinguishedTriangles C)
    (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂) (comm : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) :
    ∃ c : T₁.obj₃ ⟶ T₂.obj₃, T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧
      T₁.mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ T₂.mor₃ := by
  obtain ⟨T₁', hT₁', ⟨r₁⟩⟩ := h₁
  obtain ⟨T₂', hT₂', ⟨r₂⟩⟩ := h₂
  exact exists_hom₃_of_retract r₁ r₂ (exists_hom₃_mapTriangle T₁' T₂' hT₁' hT₂') a b comm

end Karoubi

variable (C) in
/-- The Karoubi envelope of a pretriangulated category is pretriangulated, the distinguished
triangles being the retracts of images of distinguished triangles. -/
noncomputable instance Karoubi.pretriangulated : Pretriangulated (Karoubi C) where
  distinguishedTriangles := Karoubi.distinguishedTriangles C
  isomorphic_distinguished := Karoubi.isomorphic_distinguished
  contractible_distinguished := Karoubi.contractible_distinguished
  distinguished_cocone_triangle := Karoubi.distinguished_cocone_triangle
  rotate_distinguished_triangle := Karoubi.rotate_distinguished_triangle
  complete_distinguished_triangle_morphism := Karoubi.complete_distinguished_triangle_morphism

lemma Karoubi.mem_distTriang_iff (T : Triangle (Karoubi C)) :
    T ∈ distTriang (Karoubi C) ↔ ∃ (T' : Triangle C) (_ : T' ∈ distTriang C),
      Nonempty (Retract T ((toKaroubi C).mapTriangle.obj T')) := Iff.rfl

/-- The inclusion of a pretriangulated category into its Karoubi envelope is a triangulated functor.
-/
instance toKaroubi.isTriangulated : (toKaroubi C).IsTriangulated where
  map_distinguished T hT := ⟨T, hT, ⟨Retract.refl _⟩⟩

end Idempotents

end CategoryTheory
