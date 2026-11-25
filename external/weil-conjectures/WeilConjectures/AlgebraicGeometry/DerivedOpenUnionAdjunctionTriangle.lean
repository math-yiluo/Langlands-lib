/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
import WeilConjectures.AlgebraicGeometry.DerivedOpenUnionSESPresentation
import Mathlib.CategoryTheory.Shift.Adjunction
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

/-! # Direct-image triangle on an arbitrary open union

Source: Stacks Project, Tag 08BV, applied on the open union and pushed to X.
(blueprint: lem-sc-derived-open-union-adjunction-triangle).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits Pretriangulated
namespace AlgebraicGeometry

private theorem transport_triangle
    {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (T : Triangle C) (hT : T ∈ distTriang C) {N A B : C}
    (eN : T.obj₁ ≅ N) (eA : T.obj₂ ≅ A) (eB : T.obj₃ ≅ B)
    (b : A ⟶ B) (hb : T.mor₂ ≫ eB.hom = eA.hom ≫ b) :
    ∃ (d : N ⟶ A) (c : B ⟶ N⟦(1 : ℤ)⟧), Triangle.mk d b c ∈ distTriang C := by
  let d := eN.inv ≫ T.mor₁ ≫ eA.hom
  let c := eB.inv ≫ T.mor₃ ≫ eN.hom⟦(1 : ℤ)⟧'
  refine ⟨d, c, isomorphic_distinguished T hT _ ?_⟩
  refine (Triangle.isoMk _ _ eN eA eB ?_ hb ?_).symm
  · change T.mor₁ ≫ eA.hom = eN.hom ≫ (eN.inv ≫ T.mor₁ ≫ eA.hom)
    simp only [Iso.hom_inv_id_assoc]
  · change T.mor₃ ≫ eN.hom⟦(1 : ℤ)⟧' =
      eB.hom ≫ (eB.inv ≫ T.mor₃ ≫ eN.hom⟦(1 : ℤ)⟧')
    simp only [Iso.hom_inv_id_assoc]

/-- The inverse rotation of the direct-image Mayer--Vietoris triangle, expressed using
any right adjoints to localized derived restrictions. Its second arrow is constructed by transposing
the two canonical restrictions of the union counit. This is geometric triangle data only: neither
exactness of Hom nor scalar compatibility is asserted.

Source: Stacks Project, Tag 08BV (Lemma cohomology-lemma-exact-sequence-j-star),
with the derived open adjunction of Tag 079W.
(blueprint: lem-sc-derived-open-union-adjunction-triangle).

Proof: On W = U union V, restrict a K-injective representative I of E'[k] having
injective terms. Exact restriction preserves K-injectivity, since its extension-by-zero
left adjoint is exact. In each degree the sequence of direct images
0 -> j_W* I|W -> j_U* I|U plus j_V* I|V -> j_(U intersect V)* I|_(U intersect V) -> 0
is exact. Evaluate on an arbitrary open Z: the first two maps are restriction and the
difference of restrictions, and sheaf gluing proves exactness at the first two terms.
Surjectivity follows because an injective module sheaf is flasque, so a section on
Z intersect U intersect V lifts to Z intersect U. These complexes compute the four
right derived direct images, since their restricted representatives are K-injective.
The short-exact-complex triangle construction and inverse rotation give the triangle
in the statement. The shift comparisons identify the first vertex with the right
direct image of E'[k-1] on the overlap. Transport each vertex to the specified right
adjoint using the unique isomorphism of right adjoints compatible with its adjunction.
For the second arrow, transpose the counit for the union adjunction, restrict it to
U and V by the canonical nested comparison, and transpose back by the respective
adjunctions. This gives exactly the biproduct lift b displayed here. Naturality of
the comparison and the units identifies b with the image of the restriction-unit
arrow on W. Its compatibility with arbitrary Hom maps is proved separately by
adjunction naturality, not assumed in this theorem. Empty opens give zero terms,
repeated opens give the split sequence, and all integer shifts use the same
construction. No compactness or quasi-coherence is used. -/
theorem derived_open_union_adjunction_triangle
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ W : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W))]
    (U V : X.Opens)
    (G : ∀ W : X.Opens,
      DerivedCategory (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W)) ⥤
        schemeDerivedCategory X)
    (adj : ∀ W : X.Opens,
      (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) W).mapDerivedCategory ⊣
        G W)
    (E' : schemeDerivedCategory X) (k : ℤ) :
    let R := fun W : X.Opens ↦
      (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) W).mapDerivedCategory
    let N := (G (U ⊓ V)).obj ((R (U ⊓ V)).obj (E'⟦k - 1⟧))
    let A := (G (U ⊔ V)).obj ((R (U ⊔ V)).obj (E'⟦k⟧))
    let B := (G U).obj ((R U).obj (E'⟦k⟧)) ⊞ (G V).obj ((R V).obj (E'⟦k⟧))
    let β := ((adj (U ⊔ V)).homEquiv A ((R (U ⊔ V)).obj (E'⟦k⟧))).symm (𝟙 A)
    let b := biprod.lift
      ((adj U).homEquiv A ((R U).obj (E'⟦k⟧))
        (derivedOpenHomRestriction X.toRingedSpace (homOfLE le_sup_left) β))
      ((adj V).homEquiv A ((R V).obj (E'⟦k⟧))
        (derivedOpenHomRestriction X.toRingedSpace (homOfLE le_sup_right) β))
    ∃ (d : N ⟶ A) (c : B ⟶ N⟦(1 : ℤ)⟧),
      Triangle.mk d b c ∈ distTriang (schemeDerivedCategory X) := by
  classical
  -- Reuse the sheaf abelian structures throughout the restriction comparisons.
  let _ : Abelian (SheafOfModules.{u} (moduleRings X.toRingedSpace)) := inferInstance
  let _ (W : X.Opens) :
      Abelian (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W)) := inferInstance
  dsimp only
  let R := fun W : X.Opens ↦
    (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) W).mapDerivedCategory
  let H := R (U ⊓ V) ⋙ G (U ⊓ V)
  let := (adj (U ⊓ V)).rightAdjointCommShift ℤ
  have hs := derived_open_union_ses_presentation X U V G adj (E'⟦k⟧)
  dsimp only at hs
  obtain ⟨S, eA, eB, eC, hS, hf⟩ := hs
  let T := (DerivedCategory.triangleOfSES hS).invRotate
  let eN : T.obj₁ ≅ H.obj (E'⟦k - 1⟧) :=
    (shiftFunctor (schemeDerivedCategory X) (-1 : ℤ)).mapIso eC ≪≫
      (H.commShiftIso (-1 : ℤ)).symm.app (E'⟦k⟧) ≪≫
      H.mapIso ((shiftFunctorAdd' (schemeDerivedCategory X) k (-1) (k - 1)
        (by omega)).symm.app E')
  exact transport_triangle T
    (inv_rot_of_distTriang _ (DerivedCategory.triangleOfSES_distinguished hS))
    eN eA eB _ hf

end AlgebraicGeometry
