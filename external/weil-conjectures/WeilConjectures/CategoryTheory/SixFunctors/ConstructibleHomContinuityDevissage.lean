/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartCommonStratification
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
import all WeilConjectures.CategoryTheory.HomColimitExtension
import all Mathlib.CategoryTheory.Triangulated.Pretriangulated
import all Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import all Mathlib.Algebra.Category.Grp.Colimits
import all Mathlib.CategoryTheory.Filtered.Basic
import all WeilConjectures.Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import all Mathlib.CategoryTheory.Triangulated.Yoneda
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartGeneration

/-!
# Devissage for continuity of derived Hom

Source: blueprint main-20261015, sec-six-functors-basics/
sk-lem-constructible-ext-continuity/sk-lem-constructible-ext-continuity-devissage.md
(blueprint: lemma-continuity-ext-out-constructible-complex--1).

The comparison is built from the actual cocone by the abelian-group colimit universal
property. The formal assertion imposes no boundedness condition. The final assertion uses
finite constant-model constructibility and the specified two field coefficient rings.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v t a

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace CategoryTheory

/-- The canonical additive comparison, sending a stage morphism h to h followed by the
shifted cocone map. Source: blueprint devissage statement, displayed theta formula
(blueprint: lemma-continuity-ext-out-constructible-complex--1). -/
def homContinuityComparison {T : Type t} [Category.{v} T] [Preadditive T]
    [HasShift T ℤ] {I : Type v} [SmallCategory I] (D : I ⥤ T) (c : Cocone D)
    (C : T) (q : ℤ) :
    colimit (D ⋙ shiftFunctor T q ⋙ preadditiveCoyoneda.obj (op C)) ⟶
      (preadditiveCoyoneda.obj (op C)).obj (c.pt⟦q⟧) :=
  colimit.desc _ (((shiftFunctor T q) ⋙ preadditiveCoyoneda.obj (op C)).mapCocone c)

/-- The class defined by bijectivity of the canonical comparison in every integer degree.
Source: blueprint devissage statement, definition of C
(blueprint: lemma-continuity-ext-out-constructible-complex--1). -/
def homContinuityLocus {T : Type t} [Category.{v} T] [Preadditive T]
    [HasShift T ℤ] {I : Type v} [SmallCategory I] (D : I ⥤ T) (c : Cocone D) :
    ObjectProperty T :=
  fun C ↦ ∀ q : ℤ, Function.Bijective (homContinuityComparison D c C q)

/-- Apply the comparison to the images of a diagram of complexes and its termwise
colimit under the ordinary derived localization Q. This is not a derived-category colimit.
Source: blueprint devissage statement, first paragraph and theta formula
(blueprint: lemma-continuity-ext-out-constructible-complex--1). -/
def complexHomContinuityLocus (A : Type a) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{t} A] {I : Type t} [SmallCategory I]
    (D : I ⥤ CochainComplex A ℤ) [HasColimit D] : ObjectProperty (DerivedCategory A) :=
  homContinuityLocus (D ⋙ DerivedCategory.Q)
    (DerivedCategory.Q.mapCocone (colimit.cocone D))

private theorem homContinuityLocus_iff_homColimitProperty
    {T : Type t} [Category.{v} T] [Preadditive T] [HasZeroObject T]
    [HasShift T ℤ] [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T]
    {I : Type v} [SmallCategory I] [IsFiltered I] (D : I ⥤ T) (c : Cocone D) (C : T) :
    homContinuityLocus D c C ↔ homColimitProperty D c C := by
  change (∀ q : ℤ, Function.Bijective (homContinuityComparison D c C q)) ↔ _
  simp only [homColimitProperty, homContinuityComparison, ConcreteCategory.isIso_iff_bijective]
  rfl

private theorem homContinuityLocus_iso
    {T : Type t} [Category.{v} T] [Preadditive T] [HasZeroObject T]
    [HasShift T ℤ] [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T]
    {I : Type v} [SmallCategory I] [IsFiltered I] (D : I ⥤ T) (c : Cocone D)
    {C B : T} (e : C ≅ B) (hC : homContinuityLocus D c C) :
    homContinuityLocus D c B := by
  rw [homContinuityLocus_iff_homColimitProperty] at hC ⊢
  intro n
  let eF := Functor.isoWhiskerLeft (shiftFunctor T n)
    (preadditiveCoyoneda.mapIso e.symm.op)
  exact desc_iso_transfer D c _ _ eF (hC n)

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- Hom continuity is closed under shifts, isomorphisms, extensions, and any finite
construction from a supplied collection. Source: blueprint devissage statement, formal
assertion (blueprint: lemma-continuity-ext-out-constructible-complex--1).

Proof:
1. Associativity and cocone compatibility make the postcomposition maps an additive
cocone, giving theta by def-weil-pbc-category-colimit. The shift equivalence identifies
theta for C[n] in degree q with theta for C in degree q-n. Precomposition with an
isomorphism and its inverse proves isomorphism invariance. Hom out of zero is zero.
2. For a distinguished triangle C' -> C -> C'' -> C'[1], apply Hom(-,W) to obtain
Hom(C'[1],W) -> Hom(C'',W) -> Hom(C,W) -> Hom(C',W) -> Hom(C''[-1],W).
Exactness at the three middle terms follows from lem-weil-pbc-hom-out-of-triangle-exact
and its application to the inverse rotation. TR2 makes that inverse rotation distinguished;
lem-weil-pbc-hom-into-triangle-exact gives the zero composites.
3. Set W=K_i[q] and W=K[q]. Precomposition commutes with postcomposition, including the
negative inverse-rotation arrow. Thus theta gives a commutative ladder. The first row stays
exact under the filtered abelian-group colimit by
lem-weil-pbc-filtered-colimit-abelian-groups-exact; the target row is exact directly.
4. Shift closure and the endpoint assumptions make the four outer vertical maps
isomorphisms. Apply lem-weil-pbc-five-lemma to obtain bijectivity of the middle map in
every degree.
5. Induct on the finite extension construction from G. The shift closure includes
isomorphic shifted generators, and extensionProductIter expresses finite iterated
extensions. Arbitrarily placed shifts and isomorphisms can be moved through distinguished
triangles, so this expresses all finite constructions in the statement. Cone closure also
follows by rotating a triangle and using shift and extension closure. -/
theorem constructibleHomContinuity_devissage
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    (X : Scheme.{u})
    [HasDerivedCategory.{u + 1}
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))]
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ)
    [HasColimit D] :
    (∀ (C : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
      (n : ℤ), complexHomContinuityLocus _ D C →
        complexHomContinuityLocus _ D (C⟦n⟧)) ∧
    (∀ (C B : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
      (_ : C ≅ B), complexHomContinuityLocus _ D C → complexHomContinuityLocus _ D B) ∧
    (∀ T : Pretriangulated.Triangle (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))),
      T ∈ distTriang _ → complexHomContinuityLocus _ D T.obj₁ →
        complexHomContinuityLocus _ D T.obj₃ → complexHomContinuityLocus _ D T.obj₂) ∧
    (∀ G : ObjectProperty (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))),
      G ≤ complexHomContinuityLocus _ D → ∀ n : ℕ,
        (G.shiftClosure ℤ).extensionProductIter n ≤ complexHomContinuityLocus _ D) := by
  let D' := D ⋙ DerivedCategory.Q
  let c := DerivedCategory.Q.mapCocone (colimit.cocone D)
  let P := homContinuityLocus D' c
  have hs (C) (n : ℤ) (h : P C) : P (C⟦n⟧) := by
    exact (homContinuityLocus_iff_homColimitProperty D' c _).mpr
      (homColimitProperty_shift D' c C
        ((homContinuityLocus_iff_homColimitProperty D' c C).mp h) n)
  have hi {C B} (e : C ≅ B) (h : P C) : P B := homContinuityLocus_iso D' c e h
  have he (T) (hT : T ∈ distTriang _) (h₁ : P T.obj₁) (h₃ : P T.obj₃) :
      P T.obj₂ := by
    exact (homContinuityLocus_iff_homColimitProperty D' c _).mpr
      (homColimitProperty_extensions D' c T hT
        ((homContinuityLocus_iff_homColimitProperty D' c _).mp h₁)
        ((homContinuityLocus_iff_homColimitProperty D' c _).mp h₃))
  refine ⟨hs, fun _ _ e h ↦ hi e h, he, ?_⟩
  let : P.IsClosedUnderIsomorphisms := ⟨fun e h ↦ hi e h⟩
  let : P.IsStableUnderShift ℤ :=
    { isStableUnderShiftBy := fun n ↦ ⟨fun C h ↦ hs C n h⟩ }
  let : P.IsTriangulatedClosed₂ := .mk' he
  intro G hG n
  change (G.shiftClosure ℤ).extensionProductIter n ≤ P
  exact (G.shiftClosure ℤ).extensionProductIter_le_of_isTriangulatedClosed₂
    ((ObjectProperty.shiftClosure_le_iff G P (A := ℤ)).2 hG) n

end AlgebraicGeometry.ProEtale
