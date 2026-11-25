/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-! # Homology of a termwise finite biproduct

Source: Stacks Project, Homology, Tag 0130. The termwise inclusions and projections
are chain maps and satisfy the finite biproduct identities. Their homology maps
satisfy the same identities because homology is additive.
(blueprint: new-finite-cover-termwise-biproduct-homology)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v uJ

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
  {I : Type} {J : Type uJ} {c : ComplexShape J} (A : I → HomologicalComplex C c)
  (hB : ∀ j, HasBiproduct (fun i ↦ (A i).X j))

/-- The complex whose terms and differentials are biproducts of those of `A`.
Source: Stacks Project, Tag 0130.
(blueprint: new-finite-cover-termwise-biproduct-homology) -/
def termwiseBiproduct : HomologicalComplex C c where
  X j := by letI := hB j; exact ⨁ (fun i ↦ (A i).X j)
  d j k := by letI := hB j; letI := hB k; exact biproduct.map (fun i ↦ (A i).d j k)
  shape j k h := by
    let := hB j
    let := hB k
    apply biproduct.hom_ext
    intro i
    simp [(A i).shape j k h]
  d_comp_d' j k l _ _ := by
    let := hB j
    let := hB k
    let := hB l
    apply biproduct.hom_ext
    intro i
    simp only [Category.assoc, biproduct.map_π, biproduct.map_π_assoc,
      (A i).d_comp_d, comp_zero, zero_comp]

/-- The projection from the termwise biproduct to one complex.
Source: Stacks Project, Tag 0130.
(blueprint: new-finite-cover-termwise-biproduct-homology) -/
def termwiseBiproductπ (i : I) : termwiseBiproduct A hB ⟶ A i where
  f j := by letI := hB j; exact biproduct.π (fun i ↦ (A i).X j) i
  comm' j k _ := by
    let := hB j
    let := hB k
    exact (biproduct.map_π (fun i ↦ (A i).d j k) i).symm

/-- The inclusion of one complex in the termwise biproduct.
Source: Stacks Project, Tag 0130.
(blueprint: new-finite-cover-termwise-biproduct-homology) -/
def termwiseBiproductι (i : I) : A i ⟶ termwiseBiproduct A hB where
  f j := by letI := hB j; exact biproduct.ι (fun i ↦ (A i).X j) i
  comm' j k _ := by
    let := hB j
    let := hB k
    exact biproduct.ι_map (fun i ↦ (A i).d j k) i

/-- The homology inclusions and projections form a bicone.
Source: Stacks Project, Tag 0130. Apply the homology functor to the termwise
inclusion-projection identity, separately on and off the diagonal.
(blueprint: new-finite-cover-termwise-biproduct-homology) -/
def termwiseBiproductHomologyBicone (q : J) : Bicone (fun i ↦ (A i).homology q) where
  pt := (termwiseBiproduct A hB).homology q
  π i := homologyMap (termwiseBiproductπ A hB i) q
  ι i := homologyMap (termwiseBiproductι A hB i) q
  ι_π i i' := by
    classical
    rw [← homologyMap_comp]
    by_cases h : i = i'
    · subst i'
      have he : termwiseBiproductι A hB i ≫ termwiseBiproductπ A hB i = 𝟙 _ := by
        ext j
        let := hB j
        simp [termwiseBiproductι, termwiseBiproductπ]
      simp [he]
    · have he : termwiseBiproductι A hB i ≫ termwiseBiproductπ A hB i' = 0 := by
        ext j
        let := hB j
        simp [termwiseBiproductι, termwiseBiproductπ, h]
      simp [he, h]

/-- The preceding bicone is a biproduct when its index type is finite.
Source: Stacks Project, Tag 0130. Apply additive homology to the sum of termwise
projection-inclusion composites, which equals the identity in every degree.
(blueprint: new-finite-cover-termwise-biproduct-homology) -/
def termwiseBiproductHomologyIsBilimit [Fintype I] (q : J) :
    (termwiseBiproductHomologyBicone A hB q).IsBilimit := by
  apply isBilimitOfTotal
  change ∑ i, homologyMap (termwiseBiproductπ A hB i) q ≫
    homologyMap (termwiseBiproductι A hB i) q = 𝟙 _
  simp only [← homologyMap_comp]
  change ∑ i, (homologyFunctor C c q).map
    (termwiseBiproductπ A hB i ≫ termwiseBiproductι A hB i) = 𝟙 _
  rw [← Functor.map_sum]
  have he : ∑ i, termwiseBiproductπ A hB i ≫ termwiseBiproductι A hB i = 𝟙 _ := by
    ext j
    let := hB j
    change (Hom.fAddMonoidHom j)
      (∑ i, termwiseBiproductπ A hB i ≫ termwiseBiproductι A hB i) = 𝟙 _
    rw [map_sum]
    change ∑ i, biproduct.π (fun i ↦ (A i).X j) i ≫
      biproduct.ι (fun i ↦ (A i).X j) i = 𝟙 _
    exact biproduct.total
  rw [he, CategoryTheory.Functor.map_id]

/-- The canonical finite-biproduct comparison for homology.
Source: Stacks Project, Tag 0130. The homology bicone is a bilimit, hence is
canonically isomorphic to the chosen biproduct.
(blueprint: new-finite-cover-termwise-biproduct-homology) -/
def termwiseBiproductHomologyIso [Fintype I] (q : J)
    [HasBiproduct (fun i ↦ (A i).homology q)] :
    (termwiseBiproduct A hB).homology q ≅ ⨁ (fun i ↦ (A i).homology q) :=
  biproduct.uniqueUpToIso _ (termwiseBiproductHomologyIsBilimit A hB q)

/-- The canonical comparison preserves every projection.
Source: Stacks Project, Tag 0130. Its defining map is the biproduct lift of the
homology projections.
(blueprint: new-finite-cover-termwise-biproduct-homology) -/
@[reassoc]
theorem termwiseBiproductHomologyIso_hom_π [Fintype I] (q : J)
    [HasBiproduct (fun i ↦ (A i).homology q)] (i : I) :
    (termwiseBiproductHomologyIso A hB q).hom ≫
      biproduct.π (fun i ↦ (A i).homology q) i =
      homologyMap (termwiseBiproductπ A hB i) q := by
  exact biproduct.lift_π _ _

/-- Inverse projection formula for the finite-biproduct homology comparison.
Source: Stacks Project, Tag 0130. Cancel the comparison isomorphism in the
projection formula.
(blueprint: new-finite-cover-termwise-biproduct-homology) -/
@[reassoc]
theorem termwiseBiproductHomologyIso_inv_homologyMap_π [Fintype I] (q : J)
    [HasBiproduct (fun i ↦ (A i).homology q)] (i : I) :
    (termwiseBiproductHomologyIso A hB q).inv ≫
      homologyMap (termwiseBiproductπ A hB i) q =
      biproduct.π (fun i ↦ (A i).homology q) i := by
  rw [← termwiseBiproductHomologyIso_hom_π, Iso.inv_hom_id_assoc]

end HomologicalComplex
