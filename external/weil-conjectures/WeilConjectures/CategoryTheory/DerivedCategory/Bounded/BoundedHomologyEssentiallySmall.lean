/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
public import Mathlib.CategoryTheory.ObjectProperty.Small

/-! # Essential smallness from bounded homology

Source: blueprint `lemma-hypotheses-brown-representability--5`, the Postnikov induction in steps
11–13. (blueprint: lem-sfb-bounded-homology-essentially-small)
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

namespace CategoryTheory.ObjectProperty

private theorem small_extensions
    {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [LocallySmall.{w} C] (P Q : ObjectProperty C)
    [ObjectProperty.EssentiallySmall.{w} P] [ObjectProperty.EssentiallySmall.{w} Q] :
    ObjectProperty.EssentiallySmall.{w} (extensionProduct P Q) := by
  classical
  obtain ⟨P₀, _, hP⟩ := ObjectProperty.EssentiallySmall.exists_small_le' P
  obtain ⟨Q₀, _, hQ⟩ := ObjectProperty.EssentiallySmall.exists_small_le' Q
  let I := Σ Y : Subtype P₀, Σ Z : Subtype Q₀, Shrink.{w} (Z.val ⟶ Y.val⟦(1 : ℤ)⟧)
  have hex (i : I) := distinguished_cocone_triangle₂ ((equivShrink _).symm i.2.2)
  choose E f g hE using hex
  refine ⟨.ofObj E, inferInstance, ?_⟩
  intro X hX
  have hX' : extensionProduct P₀.isoClosure Q₀.isoClosure X :=
    monotone_extensionProduct_right _ hQ X
      (monotone_extensionProduct_left _ hP X hX)
  rw [extensionProduct_isoClosure_left, extensionProduct_isoClosure_right] at hX'
  obtain ⟨Y, Z, a, b, c, hT, hY, hZ⟩ := hX'
  let i : I := ⟨⟨Y, hY⟩, ⟨Z, hZ⟩, equivShrink _ c⟩
  refine ⟨E i, ⟨i⟩, ⟨?_⟩⟩
  let e := isoTriangleOfIso₁₃ (Triangle.mk a b c)
    (Triangle.mk (f i) (g i) ((equivShrink _).symm i.2.2)) hT (hE i)
    (Iso.refl _) (Iso.refl _) (by simp [i])
  exact Triangle.π₂.mapIso e

end CategoryTheory.ObjectProperty

namespace DerivedCategory

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  [LocallySmall.{w} (DerivedCategory A)]

/-- Bounded complexes whose homology belongs to an essentially small class form an
essentially small class. No stability of that class under extensions is required.

Source: blueprint `lemma-hypotheses-brown-representability--5`, steps 11–13, the ambient Postnikov
induction; Stacks Project, Tags 014A and 014B, uniqueness of cones up to isomorphism.
(blueprint: lem-sfb-bounded-homology-essentially-small)

Proof: extensions of two essentially small classes are essentially small. Choose
representatives of the two classes and one cone for every connecting morphism
between them; these arrows form a small set by local smallness. TR3 identifies all
other extensions with one of these cones. For the interval [a,a+n-1], induct on n.
At n=0 every complex is zero. The truncation triangle at b=a+n expresses a complex
in [a,a+n] as an extension of its truncation below b by H^b[-b]. The former lies in
the previous interval, and the latter is the image of the given essentially small
class under the single-term functor. Take the small union over all a and n.
-/
theorem bounded_homologyProperty_essentiallySmall
    (P : ObjectProperty A) [P.IsClosedUnderIsomorphisms]
    [ObjectProperty.EssentiallySmall.{w} P] :
    ObjectProperty.EssentiallySmall.{w} (TStructure.t.bounded ⊓ homologyProperty P) := by
  classical
  let R (a : ℤ) (n : ℕ) : ObjectProperty (DerivedCategory A) := fun X ↦
    X.IsGE a ∧ X.IsLE (a + n - 1) ∧
      ∀ q : ℤ, a ≤ q → q ≤ a + n - 1 → P ((homologyFunctor A q).obj X)
  have smallR (n : ℕ) (a : ℤ) : ObjectProperty.EssentiallySmall.{w} (R a n) := by
    induction n with
    | zero =>
      let Z : ObjectProperty (DerivedCategory A) := .ofObj (fun _ : PUnit ↦ 0)
      have : ObjectProperty.Small.{w} Z := by dsimp [Z]; infer_instance
      have : ObjectProperty.EssentiallySmall.{w} Z.isoClosure := inferInstance
      apply ObjectProperty.EssentiallySmall.of_le (Q := Z.isoClosure)
      intro X hX
      obtain ⟨hlo, hhi, _⟩ := hX
      have hz : IsZero X := TStructure.t.isZero X (a + ↑(0 : ℕ) - 1) a (by omega)
      exact ⟨0, ⟨PUnit.unit⟩, ⟨hz.iso (isZero_zero _)⟩⟩
    | succ n ih =>
      let b : ℤ := a + n
      let S := P.map (singleFunctor A b)
      have : ObjectProperty.EssentiallySmall.{w} S := inferInstance
      have : ObjectProperty.EssentiallySmall.{w} (R a n) := ih
      have := ObjectProperty.small_extensions (R a n) S
      apply ObjectProperty.EssentiallySmall.of_le (Q := .extensionProduct (R a n) S)
      intro X hX
      obtain ⟨hlo, hhi, hP⟩ := hX
      have : X.IsLE b := TStructure.t.isLE_of_le X (a + ↑(n + 1) - 1) b (by omega)
      let T := (TStructure.t.triangleLTGE b).obj X
      have hT := TStructure.t.triangleLTGE_distinguished b X
      have : T.obj₃.IsLE b :=
        inferInstanceAs (TStructure.t.IsLE ((TStructure.t.truncGE b).obj X) b)
      have : T.obj₃.IsGE b := inferInstance
      obtain ⟨Y, ⟨e⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE T.obj₃ b
      have hz₀ : IsZero ((homologyFunctor A b).obj T.obj₁) :=
        isZero_of_isLE _ (b - 1) _ (by omega)
      have hz₁ : IsZero ((homologyFunctor A (b + 1)).obj T.obj₁) :=
        isZero_of_isLE _ (b - 1) _ (by omega)
      have := isIso_homologyMap_mor₂ T hT b (b + 1) rfl hz₀ hz₁
      have hY : P Y := P.prop_of_iso
        (asIso ((homologyFunctor A b).map T.mor₂) ≪≫
          (homologyFunctor A b).mapIso e ≪≫ (singleFunctorCompHomologyFunctorIso A b).app Y)
        (hP b (by omega) (by omega))
      have hleft : R a n T.obj₁ := by
        refine ⟨?_, ?_, ?_⟩
        · exact inferInstanceAs (TStructure.t.IsGE ((TStructure.t.truncLT b).obj X) a)
        · exact TStructure.t.isLE_truncLT_obj _ _ _ (by omega)
        · intro q hqa hqb
          have := isIso_homologyMap_mor₁ T hT (q - 1) q (by omega)
            (isZero_of_isGE _ b _ (by omega)) (isZero_of_isGE _ b _ (by omega))
          exact P.prop_of_iso (asIso ((homologyFunctor A q).map T.mor₁)).symm
            (hP q hqa (by omega))
      exact ⟨T.obj₁, T.obj₃, T.mor₁, T.mor₂, T.mor₃, hT, hleft, Y, hY, ⟨e.symm⟩⟩
  have : ∀ a : ℤ, ∀ n : ℕ, ObjectProperty.EssentiallySmall.{w} (R a n) :=
    fun a n ↦ smallR n a
  apply ObjectProperty.EssentiallySmall.of_le (Q := ⨆ a : ℤ, ⨆ n : ℕ, R a n)
  intro X hX
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hP⟩ := hX
  have : X.IsLE (a + ↑(b - a + 1).toNat - 1) :=
    TStructure.t.isLE_of_le X b _ (by omega)
  simp only [ObjectProperty.prop_iSup_iff]
  exact ⟨a, (b - a + 1).toNat, ha, inferInstance, fun q _ _ ↦ hP q⟩

end DerivedCategory
