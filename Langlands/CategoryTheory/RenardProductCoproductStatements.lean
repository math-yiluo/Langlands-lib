import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Renard A.VI.2(7): binary products and direct sums

Statements of Renard 2026, Appendix A.VI.2(7), printed page 262 / PDF page 268:
in an abelian category the actual binary product `X ⨯ Y` and the actual direct sum
(coproduct) `X ⨿ Y` are naturally isomorphic, through the canonical comparison
`coprod.desc (prod.inl X Y) (prod.inr X Y) : X ⨿ Y ⟶ X ⨯ Y`.
-/

namespace Langlands.Renard

open CategoryTheory CategoryTheory.Limits

universe u v

/-- The canonical comparison `X ⨿ Y ⟶ X ⨯ Y` is an isomorphism, with inverse
`prod.fst ≫ coprod.inl + prod.snd ≫ coprod.inr`. -/
def CoprodProdComparisonIsoStatement
    (C : Type u) [Category.{v} C] [Abelian C] : Prop :=
  ∀ X Y : C,
    IsIso (coprod.desc (prod.inl X Y) (prod.inr X Y)) ∧
    coprod.desc (prod.inl X Y) (prod.inr X Y) ≫
        (prod.fst ≫ coprod.inl + prod.snd ≫ coprod.inr : X ⨯ Y ⟶ X ⨿ Y) =
      𝟙 (X ⨿ Y) ∧
    (prod.fst ≫ coprod.inl + prod.snd ≫ coprod.inr : X ⨯ Y ⟶ X ⨿ Y) ≫
        coprod.desc (prod.inl X Y) (prod.inr X Y) =
      𝟙 (X ⨯ Y)

/-- The canonical comparison equals `prod.lift (coprod.fst X Y) (coprod.snd X Y)`;
its matrix entries are the identity on the diagonal and zero off the diagonal. -/
def CoprodProdComparisonMatrixStatement
    (C : Type u) [Category.{v} C] [Abelian C] : Prop :=
  ∀ X Y : C,
    coprod.desc (prod.inl X Y) (prod.inr X Y) =
        prod.lift (coprod.fst X Y) (coprod.snd X Y) ∧
    coprod.inl ≫ coprod.desc (prod.inl X Y) (prod.inr X Y) ≫ prod.fst = 𝟙 X ∧
    coprod.inl ≫ coprod.desc (prod.inl X Y) (prod.inr X Y) ≫ prod.snd = 0 ∧
    coprod.inr ≫ coprod.desc (prod.inl X Y) (prod.inr X Y) ≫ prod.fst = 0 ∧
    coprod.inr ≫ coprod.desc (prod.inl X Y) (prod.inr X Y) ≫ prod.snd = 𝟙 Y

/-- The canonical comparison is natural in both variables jointly. -/
def CoprodProdComparisonNaturalityStatement
    (C : Type u) [Category.{v} C] [Abelian C] : Prop :=
  ∀ (X Y X' Y' : C) (f : X ⟶ X') (g : Y ⟶ Y'),
    coprod.map f g ≫ coprod.desc (prod.inl X' Y') (prod.inr X' Y') =
      coprod.desc (prod.inl X Y) (prod.inr X Y) ≫ prod.map f g

/-- A natural isomorphism between the actual curried coproduct and product
bifunctors whose component at `X, Y` is the canonical comparison. -/
def CoprodProdNatIsoStatement
    (C : Type u) [Category.{v} C] [Abelian C] : Prop :=
  ∃ e : coprod.functor (C := C) ≅ prod.functor,
    ∀ X Y : C, (e.hom.app X).app Y = coprod.desc (prod.inl X Y) (prod.inr X Y)

/-- The combined statement family of Renard A.VI.2(7). -/
def ProductCoproductNaturalIsoStatement
    (C : Type u) [Category.{v} C] [Abelian C] : Prop :=
  CoprodProdComparisonIsoStatement C ∧
    CoprodProdComparisonMatrixStatement C ∧
    CoprodProdComparisonNaturalityStatement C ∧
    CoprodProdNatIsoStatement C

end Langlands.Renard
