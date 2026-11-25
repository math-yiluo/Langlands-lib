/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products

/-! # Termwise products of K-injective complexes

The degreewise product hypotheses suffice for both K-injectivity and the derived-category
product universal property.
-/

@[expose] public section

universe t u v w

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- The termwise product of a family of K-injective complexes is K-injective and, with the
images of its projections, is a product in the derived category.
Source: Stacks Project, Tag 0BK6, Lemma 13.31.5
(auxiliary; not a blueprint node).

The degreewise product assumption is expressed as existence of the limits of the discrete
family after evaluation in each integer degree. Mathlib's `coneOfHasLimitEval` constructs
exactly the termwise product complex, with its induced differentials and projections.
K-injectivity is Mathlib's `IsKInjective` convention, and the chosen localization universe
is that of `HasDerivedCategory`.

Proof (Tag 0BK6):
1. `HomotopyCategory.isLimitFanQuotient` gives a product fan in the homotopy category.
   Its degreewise preservation hypothesis follows from the assumed degreewise limits.
   The lemma assembles chain maps and homotopies using those products.
2. K-injective complexes are the right orthogonal of acyclic complexes in the homotopy
   category. Right orthogonals are closed under limits, so the product is K-injective.
3. For any derived-category fan, essential surjectivity of `DerivedCategory.Qh` gives a
   representative of its point in the homotopy category. `IsKInjective.Qh_map_bijective`
   lifts each leg uniquely, and the homotopy product supplies a lift. The same bijection
   for the product, together with injectivity for each factor, proves uniqueness.
   Finally `DerivedCategory.quotientCompQhIso` identifies the resulting fan with the
   actual image of the termwise product cone under `DerivedCategory.Q`.
-/
theorem termwise_product_isKInjective_and_isLimit
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {T : Type t} (I : T → CochainComplex C ℤ) [∀ s : T, (I s).IsKInjective]
    [∀ n : ℤ, HasLimit (Discrete.functor I ⋙ HomologicalComplex.eval C (ComplexShape.up ℤ) n)] :
    IsKInjective (HomologicalComplex.coneOfHasLimitEval (Discrete.functor I)).pt ∧
      Nonempty (IsLimit (DerivedCategory.Q.mapCone
        (HomologicalComplex.coneOfHasLimitEval (Discrete.functor I)))) := by
  classical
  let P : Fan I := HomologicalComplex.coneOfHasLimitEval (Discrete.functor I)
  let hP : IsLimit P := HomologicalComplex.isLimitConeOfHasLimitEval _
  let q := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  let F := DerivedCategory.Qh (C := C)
  let hK := HomotopyCategory.isLimitFanQuotient C (ComplexShape.up ℤ) hP
  have hI : P.pt.IsKInjective := by
    rw [isKInjective_iff_rightOrthogonal]
    exact ObjectProperty.prop_of_isLimit _ hK fun j ↦
      (isKInjective_iff_rightOrthogonal _).1 inferInstance
  refine ⟨hI, ?_⟩
  have hD : IsLimit (Fan.mk (F.obj (q.obj P.pt))
      fun j ↦ F.map (q.map (P.proj j))) := by
    let L (s : Fan fun j ↦ F.obj (q.obj (I j))) := F.objPreimage s.pt
    let e (s : Fan fun j ↦ F.obj (q.obj (I j))) : F.obj (L s) ≅ s.pt :=
      F.objObjPreimageIso s.pt
    let a (s : Fan fun j ↦ F.obj (q.obj (I j))) (j : T) : L s ⟶ q.obj (I j) :=
      ((IsKInjective.Qh_map_bijective (L s) (I j)).surjective
        ((e s).hom ≫ s.proj j)).choose
    have ha (s : Fan fun j ↦ F.obj (q.obj (I j))) (j : T) :
        F.map (a s j) = (e s).hom ≫ s.proj j :=
      ((IsKInjective.Qh_map_bijective (L s) (I j)).surjective
        ((e s).hom ≫ s.proj j)).choose_spec
    have hfac (s : Fan fun j ↦ F.obj (q.obj (I j))) (j : T) :
        Fan.IsLimit.lift hK (a s) ≫ q.map (P.proj j) = a s j :=
      Fan.IsLimit.fac hK (a s) j
    refine Fan.IsLimit.mk _
      (fun s ↦ (e s).inv ≫ F.map (Fan.IsLimit.lift hK (a s))) ?_ ?_
    · intro s j
      change ((e s).inv ≫ F.map _) ≫ F.map (q.map (P.proj j)) = s.proj j
      rw [Category.assoc, ← F.map_comp, hfac, ha]
      simp
    · intro s m hm
      obtain ⟨m', hm'⟩ := (IsKInjective.Qh_map_bijective (L s) P.pt).surjective
        ((e s).hom ≫ m)
      have heq : m' = Fan.IsLimit.lift hK (a s) := by
        apply Fan.IsLimit.hom_ext hK
        intro j
        apply (IsKInjective.Qh_map_bijective (L s) (I j)).injective
        change F.map (m' ≫ q.map (P.proj j)) =
          F.map (Fan.IsLimit.lift hK (a s) ≫ q.map (P.proj j))
        rw [F.map_comp, hm', Category.assoc,
          show m ≫ F.map (q.map (P.proj j)) = s.proj j from hm j, hfac, ha]
      rw [← heq, hm']
      simp
  have hQ : IsLimit (Fan.mk (DerivedCategory.Q.obj P.pt)
      fun j ↦ DerivedCategory.Q.map (P.proj j)) := by
    refine Fan.IsLimit.ofIsos hD
      (fun j ↦ ((DerivedCategory.quotientCompQhIso C).app (I j)).symm)
      ((DerivedCategory.quotientCompQhIso C).app P.pt).symm fun j ↦ ?_
    rw [Iso.symm_hom, Iso.symm_hom, Iso.inv_comp_eq,
      ← Category.assoc, Iso.eq_comp_inv]
    exact (DerivedCategory.quotientCompQhIso C).hom.naturality (P.proj j)
  exact ⟨(isLimitMapConeFanMkEquiv DerivedCategory.Q I P.proj).symm hQ⟩

end CochainComplex
