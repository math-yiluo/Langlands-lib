/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.Orthogonal
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

/-!
# Products in the homotopy category and in the derived category

Let `V` be a preadditive category with products of shape `J`. The quotient functor
`HomologicalComplex V c ⥤ HomotopyCategory V c` preserves these products
(`HomotopyCategory.isLimitFanQuotient`): homotopies between morphisms into a product of
complexes are assembled degreewise (`HomotopyCategory.homotopyOfFan`). Hence the homotopy
category has products of shape `J`.

The right orthogonal of any property of objects of a preadditive category is closed under
limits, so the K-injective complexes are closed under products in the homotopy category. As
they form a full subcategory equivalent to the derived category, an abelian category with
products of shape `J` and K-injective resolutions has a derived category with products of shape
`J` (`DerivedCategory.hasLimitsOfShape_discrete`). This applies to every Grothendieck abelian
category, for instance to sheaves on the pro-étale site, which are needed to form the Milnor
triangles of `CategoryTheory.Pretriangulated.IsHomotopyLimit`.
-/

@[expose] public section

open CategoryTheory Limits

namespace HomotopyCategory

variable {V : Type*} [Category V] [Preadditive V] {ι : Type*} {c : ComplexShape ι}
  {J : Type*}

/-- A homotopy between two morphisms into a product of complexes (computed degreewise),
assembled degreewise from homotopies between their components. -/
noncomputable def homotopyOfFan {K : J → HomologicalComplex V c}
    [∀ q, PreservesLimit (Discrete.functor K) (HomologicalComplex.eval V c q)]
    {P : Fan K} (hP : IsLimit P)
    {Y : HomologicalComplex V c} {f g : Y ⟶ P.pt}
    (H : ∀ j, Homotopy (f ≫ P.proj j) (g ≫ P.proj j)) : Homotopy f g :=
  let hPq (q : ι) : IsLimit (Fan.mk (P.pt.X q) fun j ↦ (P.proj j).f q :
      Fan fun j ↦ (K j).X q) :=
    isLimitFanMkObjOfIsLimit (HomologicalComplex.eval V c q) K P.proj hP
  have key (q : ι) {A : V} (x : ∀ j, A ⟶ (K j).X q) (j : J) :
      Fan.IsLimit.lift (hPq q) x ≫ (P.proj j).f q = x j := Fan.IsLimit.fac (hPq q) x j
  { hom p q := Fan.IsLimit.lift (hPq q) fun j ↦ (H j).hom p q
    zero p q hpq := Fan.IsLimit.hom_ext (hPq q) _ _ fun j ↦ by
      change _ ≫ (P.proj j).f q = _ ≫ (P.proj j).f q
      rw [key, (H j).zero p q hpq, Limits.zero_comp]
    comm p := Fan.IsLimit.hom_ext (hPq p) _ _ fun j ↦ by
      change _ ≫ (P.proj j).f p = _ ≫ (P.proj j).f p
      rw [Preadditive.add_comp, Preadditive.add_comp, ← dNext_comp_right,
        ← prevD_comp_right]
      simp only [key]
      have := (H j).comm p
      simp only [HomologicalComplex.comp_f] at this
      exact this }

variable (V c) in
/-- The quotient functor to the homotopy category preserves products which are computed
degreewise: the image of such a product fan of complexes is a product fan. Morphisms into the
product are lifted through the full quotient functor, and their uniqueness up to homotopy
follows from `homotopyOfFan`. -/
noncomputable def isLimitFanQuotient {K : J → HomologicalComplex V c}
    [∀ q, PreservesLimit (Discrete.functor K) (HomologicalComplex.eval V c q)] {P : Fan K}
    (hP : IsLimit P) :
    IsLimit (Fan.mk ((quotient V c).obj P.pt) fun j ↦ (quotient V c).map (P.proj j)) :=
  Fan.IsLimit.mk _
    (fun s ↦ (quotient V c).map
      (Fan.IsLimit.lift hP fun j ↦ (quotient V c).preimage (X := s.pt.as) (s.proj j)))
    (fun s j ↦ by
      change (quotient V c).map _ ≫ (quotient V c).map (P.proj j) = _
      rw [← Functor.map_comp, Fan.IsLimit.fac]
      exact Functor.map_preimage _ _)
    (fun s m hm ↦ by
      obtain ⟨m', rfl⟩ : ∃ m', (quotient V c).map (X := s.pt.as) m' = m :=
        ⟨_, Functor.map_preimage _ _⟩
      refine eq_of_homotopy _ _ (homotopyOfFan hP fun j ↦ homotopyOfEq _ _ ?_)
      rw [Functor.map_comp, Fan.IsLimit.fac]
      exact (hm j).trans ((quotient V c).map_preimage (X := s.pt.as) (Y := K j) (s.proj j)).symm)

instance [HasLimitsOfShape (Discrete J) V] :
    HasLimitsOfShape (Discrete J) (HomotopyCategory V c) where
  has_limit F := by
    have : HasLimit (Discrete.functor (F.obj ∘ Discrete.mk)) :=
      ⟨⟨⟨_, isLimitFanQuotient V c (productIsProduct fun j ↦ (F.obj ⟨j⟩).as)⟩⟩⟩
    exact hasLimit_of_iso Discrete.natIsoFunctor.symm

end HomotopyCategory

namespace DerivedCategory

variable (C : Type*) [Category C] [Abelian C] [HasDerivedCategory C]
  [Abelian.HasKInjectiveResolutions C] (J : Type*) [HasLimitsOfShape (Discrete J) C]

/-- If `C` has products of shape `J` and K-injective resolutions, then so does its derived
category: the K-injective complexes are closed under products in the homotopy category, and
they form a full subcategory equivalent to `D(C)`. -/
instance hasLimitsOfShape_discrete : HasLimitsOfShape (Discrete J) (DerivedCategory C) :=
  Adjunction.hasLimitsOfShape_of_equivalence
    (HomotopyCategory.KInjectives.equivalence C).inverse

end DerivedCategory
