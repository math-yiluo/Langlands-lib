/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.Algebra.Homology.CountableTensorStructures
public import WeilConjectures.Algebra.Homology.BifunctorMappingConeNaturality

/-!
# Additive total tensor and mapping cones before localization

Source: Stacks Project, derived.tex, Tag 0G6E,
`remark-double-complex-as-tensor-product-of`, first exactness assertion;
`WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone`, second-variable
cone comparison, and `WeilConjectures.Algebra.Homology.BifunctorMappingConeNaturality`
(auxiliary; not a blueprint node).

The total tensor below is the binary signed direct-sum tensor from
`def-sfb-preserves-kflat-quasi-iso`. The cone is Mathlib's `mappingCone`: its
coordinates are ordered as `X[n+1]` then `Y[n]`, rather than `Y[n]` then `X[n+1]`.
Under the swap of these two coordinates it has exactly the matrix in the node.
The map `mappingCone.inr` is the node's inclusion of `Y`.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CochainComplex

/-- Total tensor with an arbitrary complex commutes with cones naturally and preserves
cone inclusions; localization sends the same chain isomorphisms to derived isomorphisms.
Source: Stacks Project, derived.tex, Tag 0G6E, first exactness assertion, with the
chain comparison and naturality in the two upstream modules cited above
(auxiliary; not a blueprint node).

Proof:
1. In total degree n, distribute P^p tensor (Y^q direct-sum X^(q+1)) by
   additivity (`lem-sfb-left-resolution-additive-finite-coproducts`), then use
   the countable coproduct universal property and reindex (p,q) to (p,q+1).
   This identifies the source graded object with B^n direct-sum A^(n+1),
   where A = Tot(P tensor X), B = Tot(P tensor Y).
2. On the Y family take the identity, and on the shifted X family multiply
   by (-1)^p. The inverse has the same signs, whose squares are one. This is
   the existing `mapBifunctorMappingCone₂Iso P u (curriedTensor C)`.
3. Check the differential on both families. On Y both maps have components
   d_P tensor 1 and (-1)^p times 1 tensor d_Y. On X the three coefficients
   after the comparison are (-1)^p, (-1)^(p+1), -1; on the target-cone side
   they are (-1)^p, -(-1)^p, -1. They agree. Coproduct uniqueness gives the
   chain identity and hence the chain isomorphism.
4. For f : P to P' and a square (a,b) from u to u', the cone map is diagonal
   (b,a[1]) in the node's coordinate order. Both naturality composites on Y
   are f^p tensor b^q, and on X are (-1)^p times f^p tensor a^(q+1).
   Thus coproduct uniqueness gives simultaneous naturality; the square for
   the tensor maps is `mapBifunctorMap_comm`.
5. The inclusion lands in the Y family, where the comparison is identity,
   giving the inclusion equation. Apply `DerivedCategory.Q.mapIso` to the
   same chain isomorphism to obtain the derived one with the stated hom.
   This only applies localization to an existing isomorphism: no descent of
   tensor with P, K-flatness, boundedness, or exactness of countable sums
   is used. -/
theorem exists_totalTensorConeComparison (C : Type u) [Category.{v} C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [HasCountableCoproducts C]
    [TensorPreservesCountableCoproducts C] [HasDerivedCategory.{w} C] :
    ∃ φ : ∀ (P X Y : CochainComplex C ℤ) (u : X ⟶ Y),
      HomologicalComplex.tensorObj P (mappingCone u) ≅
        mappingCone (HomologicalComplex.tensorHom (𝟙 P) u),
    (∀ (P P' X Y X' Y' : CochainComplex C ℤ)
        (f : P ⟶ P') (u : X ⟶ Y) (u' : X' ⟶ Y')
        (a : X ⟶ X') (b : Y ⟶ Y') (h : u ≫ b = a ≫ u'),
      HomologicalComplex.tensorHom f (mappingCone.map u u' a b h) ≫
          (φ P' X' Y' u').hom =
        (φ P X Y u).hom ≫
          mappingCone.map (HomologicalComplex.tensorHom (𝟙 P) u)
            (HomologicalComplex.tensorHom (𝟙 P') u')
            (HomologicalComplex.tensorHom f a) (HomologicalComplex.tensorHom f b)
            (mapBifunctorMap_comm (curriedTensor C) f u u' a b h)) ∧
    (∀ (P X Y : CochainComplex C ℤ) (u : X ⟶ Y),
      HomologicalComplex.tensorHom (𝟙 P) (mappingCone.inr u) ≫ (φ P X Y u).hom =
        mappingCone.inr (HomologicalComplex.tensorHom (𝟙 P) u)) ∧
    (∀ (P X Y : CochainComplex C ℤ) (u : X ⟶ Y),
      ∃ e : (DerivedCategory.Q (C := C)).obj
            (HomologicalComplex.tensorObj P (mappingCone u)) ≅
          (DerivedCategory.Q (C := C)).obj
            (mappingCone (HomologicalComplex.tensorHom (𝟙 P) u)),
        e.hom = (DerivedCategory.Q (C := C)).map (φ P X Y u).hom) := by
  refine ⟨fun P _ _ u ↦ mapBifunctorMappingCone₂Iso P u (curriedTensor C), ?_, ?_, ?_⟩
  · intro P P' X Y X' Y' f u u' a b h
    exact mapBifunctorMappingCone₂Iso_hom_naturality (curriedTensor C) f u u' a b h
  · intro P X Y u
    exact mapBifunctorMap_inr_mapBifunctorMappingCone₂Iso_hom P u (curriedTensor C)
  · intro P X Y u
    exact ⟨(DerivedCategory.Q (C := C)).mapIso
      (mapBifunctorMappingCone₂Iso P u (curriedTensor C)), rfl⟩

end CochainComplex
