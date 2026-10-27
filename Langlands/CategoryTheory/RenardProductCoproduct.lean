import Langlands.CategoryTheory.RenardProductCoproductStatements

/-!
# Renard A.VI.2(7): proof that binary products and direct sums are naturally isomorphic

Proof of `Langlands.Renard.ProductCoproductNaturalIsoStatement` from
`Langlands.CategoryTheory.RenardProductCoproductStatements`, for an arbitrary abelian
category `C : Type u` with `[Category.{v} C]`.

The canonical comparison is `c(X, Y) = coprod.desc (prod.inl X Y) (prod.inr X Y)` and its
inverse is `d(X, Y) = prod.fst ≫ coprod.inl + prod.snd ≫ coprod.inr`. Every identity is
checked on the actual chosen coproduct and product by their extensionality principles
(`coprod.hom_ext`, `prod.hom_ext`); no biproduct is used.
-/

namespace Langlands.Renard

open CategoryTheory CategoryTheory.Limits

universe u v

section

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Matrix entry: the summand `X` maps to the factor `X` by the identity. -/
@[reassoc]
theorem coprodProdComparison_inl_fst (X Y : C) :
    coprod.inl ≫ coprod.desc (prod.inl X Y) (prod.inr X Y) ≫ prod.fst = 𝟙 X := by
  simp

/-- Matrix entry: the summand `X` maps to the factor `Y` by zero. -/
@[reassoc]
theorem coprodProdComparison_inl_snd (X Y : C) :
    coprod.inl ≫ coprod.desc (prod.inl X Y) (prod.inr X Y) ≫ prod.snd = 0 := by
  simp

/-- Matrix entry: the summand `Y` maps to the factor `X` by zero. -/
@[reassoc]
theorem coprodProdComparison_inr_fst (X Y : C) :
    coprod.inr ≫ coprod.desc (prod.inl X Y) (prod.inr X Y) ≫ prod.fst = 0 := by
  simp

/-- Matrix entry: the summand `Y` maps to the factor `Y` by the identity. -/
@[reassoc]
theorem coprodProdComparison_inr_snd (X Y : C) :
    coprod.inr ≫ coprod.desc (prod.inl X Y) (prod.inr X Y) ≫ prod.snd = 𝟙 Y := by
  simp

/-- The canonical comparison seen from the product side. -/
theorem coprodProdComparison_eq_prod_lift (X Y : C) :
    coprod.desc (prod.inl X Y) (prod.inr X Y) =
      prod.lift (coprod.fst X Y) (coprod.snd X Y) := by
  apply coprod.hom_ext <;> apply prod.hom_ext <;> simp

/-- First inverse law: `c(X, Y) ≫ d(X, Y) = 𝟙 (X ⨿ Y)`. -/
theorem coprodProdComparison_comp_inv (X Y : C) :
    coprod.desc (prod.inl X Y) (prod.inr X Y) ≫
        (prod.fst ≫ coprod.inl + prod.snd ≫ coprod.inr : X ⨯ Y ⟶ X ⨿ Y) =
      𝟙 (X ⨿ Y) := by
  apply coprod.hom_ext <;> simp [Preadditive.comp_add]

/-- Second inverse law: `d(X, Y) ≫ c(X, Y) = 𝟙 (X ⨯ Y)`. -/
theorem coprodProdComparison_inv_comp (X Y : C) :
    (prod.fst ≫ coprod.inl + prod.snd ≫ coprod.inr : X ⨯ Y ⟶ X ⨿ Y) ≫
        coprod.desc (prod.inl X Y) (prod.inr X Y) =
      𝟙 (X ⨯ Y) := by
  apply prod.hom_ext <;> simp [Preadditive.add_comp]

/-- The canonical comparison is an isomorphism, with inverse `d(X, Y)`. -/
theorem isIso_coprodProdComparison (X Y : C) :
    IsIso (coprod.desc (prod.inl X Y) (prod.inr X Y)) :=
  ⟨⟨_, coprodProdComparison_comp_inv X Y, coprodProdComparison_inv_comp X Y⟩⟩

/-- Joint naturality of the canonical comparison in both variables. -/
@[reassoc]
theorem coprodProdComparison_naturality {X Y X' Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') :
    coprod.map f g ≫ coprod.desc (prod.inl X' Y') (prod.inr X' Y') =
      coprod.desc (prod.inl X Y) (prod.inr X Y) ≫ prod.map f g := by
  apply coprod.hom_ext <;> apply prod.hom_ext <;> simp

/-- The canonical comparison as an isomorphism `X ⨿ Y ≅ X ⨯ Y`, with hom `c(X, Y)` and
inv `d(X, Y)`. -/
@[simps]
noncomputable def coprodProdComparisonIsoOf (X Y : C) : X ⨿ Y ≅ X ⨯ Y where
  hom := coprod.desc (prod.inl X Y) (prod.inr X Y)
  inv := prod.fst ≫ coprod.inl + prod.snd ≫ coprod.inr
  hom_inv_id := coprodProdComparison_comp_inv X Y
  inv_hom_id := coprodProdComparison_inv_comp X Y

/-- The natural isomorphism of curried bifunctors `coprod.functor ≅ prod.functor` whose
component at `X, Y` is the canonical comparison `coprod.desc (prod.inl X Y) (prod.inr X Y)`. -/
noncomputable def coprodProdNatIso : coprod.functor (C := C) ≅ prod.functor :=
  NatIso.ofComponents
    (fun X => NatIso.ofComponents (fun Y => coprodProdComparisonIsoOf X Y)
      (fun g => coprodProdComparison_naturality (𝟙 X) g))
    (fun f => by
      ext Y
      exact coprodProdComparison_naturality f (𝟙 Y))

@[simp]
theorem coprodProdNatIso_hom_app_app (X Y : C) :
    (coprodProdNatIso.hom.app X).app Y = coprod.desc (prod.inl X Y) (prod.inr X Y) :=
  rfl

end

variable (C : Type u) [Category.{v} C] [Abelian C]

theorem coprodProdComparisonIso : CoprodProdComparisonIsoStatement C := fun X Y =>
  ⟨isIso_coprodProdComparison X Y, coprodProdComparison_comp_inv X Y,
    coprodProdComparison_inv_comp X Y⟩

theorem coprodProdComparisonMatrix : CoprodProdComparisonMatrixStatement C := fun X Y =>
  ⟨coprodProdComparison_eq_prod_lift X Y, coprodProdComparison_inl_fst X Y,
    coprodProdComparison_inl_snd X Y, coprodProdComparison_inr_fst X Y,
    coprodProdComparison_inr_snd X Y⟩

theorem coprodProdComparisonNaturality : CoprodProdComparisonNaturalityStatement C :=
  fun _ _ _ _ f g => coprodProdComparison_naturality f g

theorem coprodProdNatIsoExists : CoprodProdNatIsoStatement C :=
  ⟨coprodProdNatIso, coprodProdNatIso_hom_app_app⟩

/-- Renard A.VI.2(7): the combined statement. -/
theorem productCoproductNaturalIso : ProductCoproductNaturalIsoStatement C :=
  ⟨coprodProdComparisonIso C, coprodProdComparisonMatrix C,
    coprodProdComparisonNaturality C, coprodProdNatIsoExists C⟩

end Langlands.Renard
