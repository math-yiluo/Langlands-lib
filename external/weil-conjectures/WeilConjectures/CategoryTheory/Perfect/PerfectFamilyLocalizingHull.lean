/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.CategoryTheory.ObjectProperty.Small

/-! # Perfect generators of a localizing hull

Source: Krause, Localization theory for triangulated categories, Theorem 7.2.1.
(blueprint: lem-sfb-perfect-family-localizing-hull)
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated ZeroObject

namespace CategoryTheory

section Factorization

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  (S B : ObjectProperty C) [S.IsClosedUnderIsomorphisms] [S.IsTriangulated]
  [B.IsClosedUnderIsomorphisms] [B.IsTriangulated] (hBS : B ≤ S)

omit [S.IsClosedUnderIsomorphisms] in
include hBS in
private theorem factorization_extension
    (T : Triangle C) (hT : T ∈ distTriang C)
    (hX : ∀ U, S U → ∀ f : U ⟶ T.obj₁,
      ∃ V, B V ∧ ∃ (g : U ⟶ V) (h : V ⟶ T.obj₁), g ≫ h = f)
    (hXs : ∀ U, S U → ∀ f : U ⟶ T.obj₁⟦(1 : ℤ)⟧,
      ∃ V, B V ∧ ∃ (g : U ⟶ V) (h : V ⟶ T.obj₁⟦(1 : ℤ)⟧), g ≫ h = f)
    (hZ : ∀ U, S U → ∀ f : U ⟶ T.obj₃,
      ∃ V, B V ∧ ∃ (g : U ⟶ V) (h : V ⟶ T.obj₃), g ≫ h = f)
    (U : C) (hU : S U) (f : U ⟶ T.obj₂) :
    ∃ V, B V ∧ ∃ (g : U ⟶ V) (h : V ⟶ T.obj₂), g ≫ h = f := by
  obtain ⟨Z, hZB, a, b, hab⟩ := hZ U hU (f ≫ T.mor₂)
  obtain ⟨D, hDS, c, d, hD⟩ := S.distinguished_cocone_triangle a hU (hBS _ hZB)
  let T₁ := Triangle.mk a c d
  have h₁ : a ≫ (b ≫ T.mor₃) = 0 := by
    rw [← Category.assoc, hab, Category.assoc, comp_distTriang_mor_zero₂₃ _ hT, comp_zero]
  obtain ⟨e, he⟩ := Triangle.yoneda_exact₂ T₁ hD (b ≫ T.mor₃) h₁
  obtain ⟨X, hXB, k, l, hkl⟩ := hXs D hDS e
  obtain ⟨V, hVB, p, q, hV⟩ := B.distinguished_cocone_triangle₁ (c ≫ k) hZB hXB
  let T₂ := Triangle.mk p (c ≫ k) q
  have h₂ : a ≫ (c ≫ k) = 0 := by
    have hac : a ≫ c = 0 := comp_distTriang_mor_zero₁₂ T₁ hD
    rw [← Category.assoc, hac, zero_comp]
  obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ T₂ hV a h₂
  have comm : (c ≫ k) ≫ l = b ≫ T.mor₃ := by
    rw [Category.assoc, hkl]
    exact he.symm
  obtain ⟨r, hr₁, hr₂⟩ := complete_distinguished_triangle_morphism₁
    T₂ T.rotate hV (rot_of_distTriang T hT) b l comm
  dsimp only [T₂, Triangle.mk, Triangle.rotate] at r hr₁ hr₂ g hg
  have hdiff : (f - g ≫ r) ≫ T.mor₂ = 0 := by
    rw [Preadditive.sub_comp, Category.assoc, ← hr₁, ← Category.assoc, ← hg, hab,
      sub_self]
  obtain ⟨a', ha'⟩ := Triangle.coyoneda_exact₂ T hT (f - g ≫ r) hdiff
  obtain ⟨X', hX'B, k', l', hkl'⟩ := hX U hU a'
  refine ⟨V ⊞ X', ?_, g ≫ biprod.inl + k' ≫ biprod.inr,
    biprod.desc r (l' ≫ T.mor₁), ?_⟩
  · exact B.prop_of_iso (biprod.isoProd V X').symm (B.prop_prod V X' hVB hX'B)
  · simp only [Preadditive.add_comp, Category.assoc, biprod.inl_desc, biprod.inr_desc]
    rw [← Category.assoc k', hkl', ← ha']
    abel

omit [S.IsClosedUnderIsomorphisms] in
include hBS in
private theorem factorization_localizing
    [HasCoproducts.{v} C] [ObjectProperty.EssentiallySmall.{v} B]
    (hperfect : ∀ (I : Type v) (X Y : I → C) (f : ∀ i, X i ⟶ Y i),
      (∀ i U, S U → Function.Surjective (fun g : U ⟶ X i ↦ g ≫ f i)) →
      ∀ U, S U → Function.Surjective
        (fun g : U ⟶ ∐ X ↦ g ≫ Limits.Sigma.map f))
    (hsmall : ∀ (U : C), S U → ∀ (I : Type v) (Y : I → C), (∀ i, B (Y i)) →
      ∀ f : U ⟶ ∐ Y, ∃ V, B V ∧ ∃ (g : U ⟶ V) (h : V ⟶ ∐ Y), g ≫ h = f) :
    let R : ObjectProperty C := fun X ↦ ∀ U, S U → ∀ f : U ⟶ X,
      ∃ V, B V ∧ ∃ (g : U ⟶ V) (h : V ⟶ X), g ≫ h = f
    R.IsClosedUnderIsomorphisms ∧ R.IsTriangulated ∧
      (∀ I : Type v, R.IsClosedUnderColimitsOfShape (Discrete I)) := by
  classical
  let R : ObjectProperty C := fun X ↦ ∀ U, S U → ∀ f : U ⟶ X,
    ∃ V, B V ∧ ∃ (g : U ⟶ V) (h : V ⟶ X), g ≫ h = f
  change R.IsClosedUnderIsomorphisms ∧ R.IsTriangulated ∧ _
  have hRiso : R.IsClosedUnderIsomorphisms := ⟨by
    intro X Y e hX U hU f
    obtain ⟨V, hVB, g, h, hgh⟩ := hX U hU (f ≫ e.inv)
    exact ⟨V, hVB, g, h ≫ e.hom, by rw [← Category.assoc, hgh]; simp⟩⟩
  have hRshift : R.IsStableUnderShift ℤ := ⟨fun n ↦ .mk (by
    intro X hX U hU f
    let E := shiftEquiv C n
    have hSU : S (E.inverse.obj U) := S.le_shift (-n) U hU
    let a : E.inverse.obj U ⟶ X :=
      E.functor.preimage (E.counitIso.hom.app U ≫ f)
    obtain ⟨V, hVB, g, h, hgh⟩ := hX _ hSU a
    refine ⟨E.functor.obj V, B.le_shift n V hVB, E.counitIso.inv.app U ≫ E.functor.map g,
      E.functor.map h, ?_⟩
    rw [Category.assoc, ← E.functor.map_comp, hgh]
    dsimp only [a]
    rw [E.functor.map_preimage, ← Category.assoc, E.counitIso.inv_hom_id_app]
    exact Category.id_comp f)⟩
  have hRzero : R.ContainsZero := ⟨⟨0, isZero_zero C, by
    intro U hU f
    exact ⟨0, B.prop_zero, 0, 0, (isZero_zero C).eq_of_tgt _ _⟩⟩⟩
  have hRclosed : R.IsTriangulatedClosed₂ := .mk' (by
    intro T hT hX hZ
    exact factorization_extension S B hBS T hT hX (R.le_shift (1 : ℤ) T.obj₁ hX) hZ)
  have hRtri : R.IsTriangulated := {}
  refine ⟨hRiso, hRtri, ?_⟩
  intro I
  constructor
  rintro X ⟨pres⟩
  have hRX (i : I) : R (pres.diag.obj ⟨i⟩) := pres.prop_diag_obj ⟨i⟩
  let X' : I → C := fun i ↦ pres.diag.obj ⟨i⟩
  suffices hsum : R (∐ X') from
    R.prop_of_iso
      ((coproductIsCoproduct X').coconePointUniqueUpToIso
        ((IsColimit.precomposeHomEquiv (Discrete.natIsoFunctor (F := pres.diag)).symm pres.cocone).2
          pres.isColimit)) hsum
  obtain ⟨B₀, _, hB₀, hB⟩ := ObjectProperty.EssentiallySmall.exists_small_le B
  let J := Shrink (Subtype B₀)
  let Z : J → C := fun j ↦ ((equivShrink (Subtype B₀)).symm j).val
  have hZ (j : J) : B (Z j) := hB₀ _ ((equivShrink (Subtype B₀)).symm j).property
  have hrep (V : C) (hV : B V) : ∃ j, Nonempty (V ≅ Z j) := by
    obtain ⟨V', hV', ⟨e⟩⟩ := hB _ hV
    refine ⟨equivShrink (Subtype B₀) ⟨V', hV'⟩, ⟨?_⟩⟩
    exact e ≪≫ eqToIso (by simp [Z])
  let K (i : I) := Σ j, Z j ⟶ X' i
  let Y (i : I) : K i → C := fun k ↦ Z k.1
  let e (i : I) : (∐ Y i) ⟶ X' i := Sigma.desc fun k ↦ k.2
  have he (i : I) (U : C) (hU : S U) :
      Function.Surjective (fun g : U ⟶ ∐ Y i ↦ g ≫ e i) := by
    intro f
    obtain ⟨V, hV, g, h, hgh⟩ := hRX i U hU f
    obtain ⟨j, ⟨iso⟩⟩ := hrep V hV
    refine ⟨g ≫ iso.hom ≫ Sigma.ι (Y i) ⟨j, iso.inv ≫ h⟩, ?_⟩
    simp only [Category.assoc, e, Sigma.ι_comp_desc]
    simpa using hgh
  let F : (Σ i, K i) → C := fun ik ↦ Y ik.1 ik.2
  let iso : (∐ fun i ↦ ∐ Y i) ≅ ∐ F := sigmaSigmaIso K Y
  intro U hU f
  obtain ⟨g, hg⟩ := hperfect I (fun i ↦ ∐ Y i) X' e he U hU f
  obtain ⟨V, hV, k, l, hkl⟩ := hsmall U hU _ F (fun ik ↦ hZ ik.2.1) (g ≫ iso.hom)
  refine ⟨V, hV, k, l ≫ iso.inv ≫ Limits.Sigma.map e, ?_⟩
  rw [← Category.assoc, ← Category.assoc, hkl, Category.assoc g iso.hom iso.inv, iso.hom_inv_id,
    Category.comp_id]
  exact hg

end Factorization

/-- A small triangulated hull of a perfect class gives perfect generators of its
localizing hull, provided maps from that class into coproducts of hull objects
factor through a hull object.

Source: Krause, *Localization theory for triangulated categories*, Theorem 7.2.1(1)-(3),
expanded using its factorization argument.
(blueprint: lem-sfb-perfect-family-localizing-hull)

Proof: let R consist of objects X such that every map U to X with U in S factors
through an object of B. This class is replete and shift closed. To check extensions,
factor a map U to the third vertex through Z in B. Complete U to Z to a triangle;
its cone is in S. Factor the resulting map from that cone to the shifted first
vertex through X in B. Take the fiber V in B of Z to X, and complete the square
to a morphism of triangles. The original map lifts through V up to a map through
the first vertex; factor that error through another B object and use their biproduct.
For coproducts, evaluate all maps from small representatives of B into each summand.
Perfectness of S lifts a map into the coproduct through the coproduct of these
covers. Flatten it with sigmaSigmaIso and use the assumed small factorization.
Thus R is localizing and contains P, so minimality gives Q contained in R.
Componentwise surjectivity on B now implies it on S for maps in Q, by factoring
through B. Perfectness of S gives surjectivity after coproducts, in particular on B.
Transport this through the fully faithful inclusion and its coproduct comparison,
and choose small representatives of B for the required indexed family.
-/
theorem perfectFamily_of_small_hull
    {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] [HasCoproducts.{v} C]
    (S B : ObjectProperty C) [S.IsTriangulated]
    [B.IsClosedUnderIsomorphisms] [B.IsTriangulated]
    [ObjectProperty.EssentiallySmall.{v} B] (hBS : B ≤ S)
    (P Q : ObjectProperty C) [Q.IsClosedUnderIsomorphisms] [Q.IsTriangulated]
    [∀ I : Type v, Q.IsClosedUnderColimitsOfShape (Discrete I)]
    (hPB : P ≤ B) (hBQ : B ≤ Q)
    (hminimal : ∀ R : ObjectProperty C, P ≤ R →
      R.IsClosedUnderIsomorphisms → R.IsTriangulated →
      (∀ I : Type v, R.IsClosedUnderColimitsOfShape (Discrete I)) → Q ≤ R)
    (hperfect : ∀ (I : Type v) (X Y : I → C) (f : ∀ i, X i ⟶ Y i),
      (∀ i U, S U → Function.Surjective (fun g : U ⟶ X i ↦ g ≫ f i)) →
      ∀ U, S U → Function.Surjective
        (fun g : U ⟶ ∐ X ↦ g ≫ Limits.Sigma.map f))
    (hsmall : ∀ (U : C), S U → ∀ (I : Type v) (Y : I → C), (∀ i, B (Y i)) →
      ∀ f : U ⟶ ∐ Y, ∃ V, B V ∧ ∃ (g : U ⟶ V) (h : V ⟶ ∐ Y), g ≫ h = f) :
    ∃ (J : Type v) (V : J → Q.FullSubcategory),
      (∀ (j : J) (n : ℤ), ∃ k, Nonempty (V k ≅ (V j)⟦n⟧)) ∧
      (∀ X, P X → ∃ j, Nonempty (X ≅ (V j).obj)) ∧
      (∀ (I : Type v) (X Y : I → Q.FullSubcategory) (f : ∀ i, X i ⟶ Y i),
        (∀ i j, Function.Surjective (fun g : V j ⟶ X i ↦ g ≫ f i)) →
        ∀ j, Function.Surjective (fun g : V j ⟶ ∐ X ↦ g ≫ Limits.Sigma.map f)) := by
  classical
  let R : ObjectProperty C := fun X ↦ ∀ U, S U → ∀ f : U ⟶ X,
    ∃ V, B V ∧ ∃ (g : U ⟶ V) (h : V ⟶ X), g ≫ h = f
  obtain ⟨hRi, hRt, hRc⟩ := factorization_localizing S B hBS hperfect hsmall
  have hPR : P ≤ R := fun X hX U _ f ↦ ⟨X, hPB X hX, f, 𝟙 X, Category.comp_id f⟩
  have hQR : Q ≤ R := hminimal R hPR hRi hRt hRc
  obtain ⟨B₀, _, hB₀, hB⟩ := ObjectProperty.EssentiallySmall.exists_small_le B
  let J := Shrink (Subtype B₀)
  let V : J → Q.FullSubcategory := fun j ↦
    ⟨((equivShrink (Subtype B₀)).symm j).val,
      hBQ _ (hB₀ _ ((equivShrink (Subtype B₀)).symm j).property)⟩
  have hV (j : J) : B (V j).obj := hB₀ _ ((equivShrink (Subtype B₀)).symm j).property
  have hrep (X : C) (hX : B X) : ∃ j, Nonempty (X ≅ (V j).obj) := by
    obtain ⟨X', hX', ⟨e⟩⟩ := hB X hX
    refine ⟨equivShrink (Subtype B₀) ⟨X', hX'⟩, ⟨?_⟩⟩
    exact e ≪≫ eqToIso (by simp [V])
  refine ⟨J, V, ?_, fun X hX ↦ hrep X (hPB X hX), ?_⟩
  · intro j n
    obtain ⟨k, ⟨e⟩⟩ := hrep ((V j).obj⟦n⟧) (B.le_shift n _ (hV j))
    exact ⟨k, ⟨Q.ι.preimageIso
      (e.symm ≪≫ ((Q.ι.commShiftIso n).app (V j)).symm)⟩⟩
  · intro I X Y f hf j t
    let X' : I → C := fun i ↦ (X i).obj
    let Y' : I → C := fun i ↦ (Y i).obj
    let f' : ∀ i, X' i ⟶ Y' i := fun i ↦ Q.ι.map (f i)
    have hsurj (i : I) (U : C) (hU : S U) :
        Function.Surjective (fun g : U ⟶ X' i ↦ g ≫ f' i) := by
      intro g
      obtain ⟨W, hW, a, b, hab⟩ := hQR _ (Y i).property U hU g
      obtain ⟨k, ⟨e⟩⟩ := hrep W hW
      obtain ⟨c, hc⟩ := hf i k (ObjectProperty.homMk (e.inv ≫ b))
      have hc' : Q.ι.map c ≫ f' i = e.inv ≫ b := congrArg (fun g ↦ Q.ι.map g) hc
      refine ⟨a ≫ e.hom ≫ Q.ι.map c, ?_⟩
      change (a ≫ e.hom ≫ Q.ι.map c) ≫ f' i = g
      rw [Category.assoc, Category.assoc, hc', e.hom_inv_id_assoc, hab]
    let cX := asIso (sigmaComparison Q.ι X)
    let cY := asIso (sigmaComparison Q.ι Y)
    obtain ⟨g, hg⟩ := hperfect I X' Y' f' hsurj (V j).obj (hBS _ (hV j))
      (Q.ι.map t ≫ cY.inv)
    have hnat : cX.hom ≫ Q.ι.map (Limits.Sigma.map f) =
        Limits.Sigma.map f' ≫ cY.hom := by
      apply Sigma.hom_ext
      intro i
      dsimp only [cX, cY, asIso_hom, X', Y', f']
      simp only [ι_comp_sigmaComparison_assoc, Limits.Sigma.ι_map_assoc,
        ← Functor.map_comp, Limits.Sigma.ι_map]
      change Q.ι.map (f i ≫ Sigma.ι Y i) =
        Q.ι.map (f i) ≫ Sigma.ι (fun i ↦ Q.ι.obj (Y i)) i ≫ sigmaComparison Q.ι Y
      rw [ι_comp_sigmaComparison, Functor.map_comp]
    refine ⟨Q.ι.preimage (g ≫ cX.hom), ?_⟩
    apply Q.ι.map_injective
    rw [Functor.map_comp, Functor.map_preimage, Category.assoc, hnat,
      ← Category.assoc]
    change (g ≫ Limits.Sigma.map f') ≫ cY.hom = Q.ι.map t
    change g ≫ Limits.Sigma.map f' = Q.ι.map t ≫ cY.inv at hg
    rw [hg, Category.assoc, cY.inv_hom_id, Category.comp_id]

end CategoryTheory
