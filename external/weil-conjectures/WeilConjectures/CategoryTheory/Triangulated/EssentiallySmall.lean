/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Small
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty

/-!
# Essential smallness of extensions and of bounded complexes

Let `C` be a pretriangulated category whose `Hom`-types are `w`-small. If two properties of
objects `P₁`, `P₃` are essentially `w`-small, so is the property of being an extension of an
object of `P₃` by an object of `P₁`, i.e. the middle term of a distinguished triangle
`X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧` with `P₁ X₁` and `P₃ X₃`
(`CategoryTheory.ObjectProperty.essentiallySmall_extensions`): up to isomorphism, the
triangle is determined by the class `X₃ ⟶ X₁⟦1⟧`, which ranges over a small set.

Consequently, for an essentially small property `P` of objects of an abelian category `A`, the
bounded complexes all of whose cohomology objects satisfy `P` form an essentially small property
of `D(A)` (`DerivedCategory.essentiallySmall_bounded_homologyProperty`), by induction on the
length along the truncation triangles (blueprint `lemma-hypotheses-brown-representability--5`).
-/

@[expose] public section

universe w v u

open CategoryTheory Limits Pretriangulated ZeroObject

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The extensions of objects satisfying `P₃` by objects satisfying `P₁`: the objects isomorphic
to the middle term of a distinguished triangle `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧` with `P₁ X₁` and
`P₃ X₃`. -/
def extensions (P₁ P₃ : ObjectProperty C) : ObjectProperty C :=
  fun X ↦ ∃ T ∈ distTriang C, P₁ T.obj₁ ∧ P₃ T.obj₃ ∧ Nonempty (T.obj₂ ≅ X)

/-- Extensions of objects of essentially small properties form an essentially small
property. -/
instance essentiallySmall_extensions [LocallySmall.{w} C] (P₁ P₃ : ObjectProperty C)
    [ObjectProperty.EssentiallySmall.{w} P₁] [ObjectProperty.EssentiallySmall.{w} P₃] :
    ObjectProperty.EssentiallySmall.{w} (extensions P₁ P₃) := by
  obtain ⟨Q₁, _, hQ₁⟩ := EssentiallySmall.exists_small_le' P₁
  obtain ⟨Q₃, _, hQ₃⟩ := EssentiallySmall.exists_small_le' P₃
  let ι := Σ (A : Subtype Q₁) (B : Subtype Q₃), B.1 ⟶ A.1⟦(1 : ℤ)⟧
  have h (x : ι) := distinguished_cocone_triangle₂ x.2.2
  choose Y a b hT using h
  refine ⟨ofObj Y, inferInstance, fun X ⟨T, hT', h₁, h₃, ⟨e⟩⟩ ↦ ?_⟩
  obtain ⟨A, hA, ⟨e₁⟩⟩ := hQ₁ _ h₁
  obtain ⟨B, hB, ⟨e₃⟩⟩ := hQ₃ _ h₃
  let x : ι := ⟨⟨A, hA⟩, ⟨B, hB⟩, e₃.inv ≫ T.mor₃ ≫ e₁.hom⟦(1 : ℤ)⟧'⟩
  exact ⟨Y x, ofObj_apply Y x, ⟨e.symm ≪≫ Triangle.π₂.mapIso
    (isoTriangleOfIso₁₃ T _ hT' (hT x) e₁ e₃ (by simp [x]))⟩⟩

end CategoryTheory.ObjectProperty

namespace DerivedCategory

open TStructure (t)

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  (P : ObjectProperty A) [P.IsClosedUnderIsomorphisms] [P.ContainsZero]
  [ObjectProperty.EssentiallySmall.{w} P]

/-- The objects of `D(A)` in degrees `[a, a + n - 1]` whose cohomology objects satisfy `P` form
an essentially small property, if `P` does. -/
lemma essentiallySmall_isGE_isLE_homologyProperty (n : ℕ) (a : ℤ) :
    ObjectProperty.EssentiallySmall.{w}
      (fun M : DerivedCategory A ↦ M.IsGE a ∧ M.IsLE (a + n - 1) ∧ homologyProperty P M) := by
  induction n generalizing a with
  | zero =>
    refine ObjectProperty.EssentiallySmall.of_le
      (Q := (ObjectProperty.ofObj fun _ : PUnit.{w + 1} ↦ (0 : DerivedCategory A)).isoClosure)
      fun M ⟨_, h₂, _⟩ ↦ ?_
    have : M.IsLE (a - 1) := by simpa using h₂
    exact ⟨0, ObjectProperty.ofObj_apply _ PUnit.unit, ⟨(t.isZero M (a - 1) a (by lia)).isoZero⟩⟩
  | succ n ih =>
    have := ih a
    have := ObjectProperty.essentiallySmall_extensions.{w} (C := DerivedCategory A)
      (fun M : DerivedCategory A ↦ M.IsGE a ∧ M.IsLE (a + n - 1) ∧ homologyProperty P M)
      (P.map (singleFunctor A (a + n)))
    refine ObjectProperty.EssentiallySmall.of_le.{w} (Q := ObjectProperty.extensions
      (fun M : DerivedCategory A ↦ M.IsGE a ∧ M.IsLE (a + n - 1) ∧ homologyProperty P M)
      (P.map (singleFunctor A (a + n)))) fun M ⟨h₁, h₂, hM⟩ ↦ ?_
    set b : ℤ := a + n
    have hT := t.triangleLEGE_distinguished (b - 1) b (by lia) M
    have : M.IsLE b := t.isLE_of_le M (a + ↑(n + 1) - 1) _ (by lia)
    have : ((t.truncGE b).obj M).IsLE b := inferInstanceAs (t.IsLE ((t.truncGE b).obj M) b)
    have : ((t.truncGE b).obj M).IsGE b := inferInstanceAs (t.IsGE ((t.truncGE b).obj M) b)
    have : ((t.truncLE (b - 1)).obj M).IsGE a :=
      inferInstanceAs (t.IsGE ((t.truncLE (b - 1)).obj M) a)
    have : ((t.truncLE (b - 1)).obj M).IsLE (b - 1) :=
      inferInstanceAs (t.IsLE ((t.truncLE (b - 1)).obj M) (b - 1))
    obtain ⟨Y, ⟨e⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE ((t.truncGE b).obj M) b
    have := isIso_homologyFunctor_map_truncGEπ_app M b b le_rfl
    exact ⟨_, hT, ⟨inferInstanceAs (((t.truncLE (b - 1)).obj M).IsGE a),
      t.isLE_of_le ((t.truncLE (b - 1)).obj M) (b - 1) _ (by lia),
      homologyProperty_truncLE hM (b - 1)⟩,
      ⟨Y, P.prop_of_iso (asIso ((homologyFunctor A b).map ((t.truncGEπ b).app M)) ≪≫
        (homologyFunctor A b).mapIso e ≪≫ (singleFunctorCompHomologyFunctorIso A b).app Y) (hM b),
        ⟨e.symm⟩⟩, ⟨Iso.refl _⟩⟩

/-- Blueprint `lemma-hypotheses-brown-representability--5`: for an essentially small property `P` of
objects of an abelian category `A`, the bounded objects of `D(A)` all of whose cohomology objects
satisfy `P` form an essentially small property. -/
instance essentiallySmall_bounded_homologyProperty :
    ObjectProperty.EssentiallySmall.{w} (t.bounded ⊓ homologyProperty P) := by
  have (p : ℤ × ℕ) := essentiallySmall_isGE_isLE_homologyProperty P p.2 p.1
  refine ObjectProperty.EssentiallySmall.of_le (Q := ⨆ p : ℤ × ℕ,
    fun M : DerivedCategory A ↦ M.IsGE p.1 ∧ M.IsLE (p.1 + p.2 - 1) ∧ homologyProperty P M)
    fun M ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hM⟩ ↦ ?_
  refine (ObjectProperty.prop_iSup_iff _ M).2 ?_
  exact ⟨(a, (b - a + 1).toNat), ha, t.isLE_of_le M b _ (by lia), hM⟩

end DerivedCategory
