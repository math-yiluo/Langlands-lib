/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryFan
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts

/-!
# Splitting off one factor of a product indexed by `Option`

A product indexed by `Option ι` is the binary product of the `none` factor with the product of
the remaining factors. Dually, a coproduct indexed by `Option ι` is the binary coproduct of the
`none` summand with the coproduct of the remaining summands.

## Main declarations

* `CategoryTheory.Limits.binaryFanOptionPi`: the binary fan on `F none` and `∏ᶜ fun i ↦ F (some i)`
  with vertex `∏ᶜ F` is a limit cone.
* `CategoryTheory.Limits.piOptionIso`: the resulting isomorphism
  `∏ᶜ F ≅ F none ⨯ ∏ᶜ fun i ↦ F (some i)`.
* `CategoryTheory.Limits.sigmaOptionIso`: the isomorphism
  `∐ F ≅ F none ⨿ ∐ fun i ↦ F (some i)`.
-/

@[expose] public section

namespace CategoryTheory.Limits

variable {C ι : Type*} [Category* C] (F : Option ι → C)
  [HasProduct F] [HasProduct fun i ↦ F (some i)]

/-- The binary fan with vertex `∏ᶜ F` on the factor `F none` and the product
`∏ᶜ fun i ↦ F (some i)` of the remaining factors is a limit cone. -/
noncomputable def binaryFanOptionPi :
    IsLimit (BinaryFan.mk (Pi.π F none) (Pi.lift fun i ↦ Pi.π F (some i)) :
      BinaryFan (F none) (∏ᶜ fun i ↦ F (some i))) :=
  BinaryFan.isLimitMk
    (fun s ↦ Pi.lift fun j ↦ match j with
      | none => s.fst
      | some i => s.snd ≫ Pi.π (fun i ↦ F (some i)) i)
    (fun s ↦ by simp)
    (fun s ↦ by ext i; simp)
    (fun s m h₁ h₂ ↦ by
      refine Pi.hom_ext _ _ fun j ↦ ?_
      match j with
      | none => simpa using h₁
      | some i => rw [← h₂]; simp)

variable [HasBinaryProduct (F none) (∏ᶜ fun i ↦ F (some i))]

/-- A product indexed by `Option ι` is the binary product of the `none` factor with the product
over `ι` of the remaining factors. -/
noncomputable def piOptionIso : (∏ᶜ F) ≅ F none ⨯ (∏ᶜ fun i ↦ F (some i)) :=
  (binaryFanOptionPi F).conePointUniqueUpToIso
    (limit.isLimit (pair (F none) (∏ᶜ fun i ↦ F (some i))))

@[reassoc (attr := simp)]
lemma piOptionIso_hom_comp_fst : (piOptionIso F).hom ≫ prod.fst = Pi.π F none :=
  (binaryFanOptionPi F).conePointUniqueUpToIso_hom_comp
    (limit.isLimit (pair (F none) (∏ᶜ fun i ↦ F (some i)))) ⟨WalkingPair.left⟩

@[reassoc (attr := simp)]
lemma piOptionIso_hom_comp_snd :
    (piOptionIso F).hom ≫ prod.snd = Pi.lift fun i ↦ Pi.π F (some i) :=
  (binaryFanOptionPi F).conePointUniqueUpToIso_hom_comp
    (limit.isLimit (pair (F none) (∏ᶜ fun i ↦ F (some i)))) ⟨WalkingPair.right⟩

@[reassoc (attr := simp)]
lemma piOptionIso_inv_comp_π_none : (piOptionIso F).inv ≫ Pi.π F none = prod.fst :=
  (binaryFanOptionPi F).conePointUniqueUpToIso_inv_comp
    (limit.isLimit (pair (F none) (∏ᶜ fun i ↦ F (some i)))) ⟨WalkingPair.left⟩

@[reassoc (attr := simp)]
lemma piOptionIso_inv_comp_π_some (i : ι) :
    (piOptionIso F).inv ≫ Pi.π F (some i) = prod.snd ≫ Pi.π (fun i ↦ F (some i)) i := by
  have h : (piOptionIso F).inv ≫ (Pi.lift fun i ↦ Pi.π F (some i)) = prod.snd := by
    rw [Iso.inv_comp_eq, piOptionIso_hom_comp_snd]
  rw [← h]
  simp

section Sigma

variable {C ι : Type*} [Category* C] (F : Option ι → C)
  [HasCoproduct F] [HasCoproduct fun i ↦ F (some i)]

/-- The binary cofan with vertex `∐ F` on the summand `F none` and the coproduct
`∐ fun i ↦ F (some i)` of the remaining summands is a colimit cocone. -/
noncomputable def binaryCofanOptionSigma :
    IsColimit (BinaryCofan.mk (Sigma.ι F none) (Sigma.desc fun i ↦ Sigma.ι F (some i)) :
      BinaryCofan (F none) (∐ fun i ↦ F (some i))) :=
  BinaryCofan.isColimitMk
    (fun s ↦ Sigma.desc fun j ↦ match j with
      | none => s.inl
      | some i => Sigma.ι (fun i ↦ F (some i)) i ≫ s.inr)
    (fun s ↦ by simp)
    (fun s ↦ by ext i; simp)
    (fun s m h₁ h₂ ↦ by
      refine Sigma.hom_ext _ _ fun j ↦ ?_
      match j with
      | none => simpa using h₁
      | some i => rw [← h₂]; simp)

variable [HasBinaryCoproduct (F none) (∐ fun i ↦ F (some i))]

/-- A coproduct indexed by `Option ι` is the binary coproduct of the `none` summand with the
coproduct over `ι` of the remaining summands:
```
∐ F ≅ F none ⨿ ∐ (F ∘ some)
```
Under this isomorphism `Sigma.ι F none` corresponds to `coprod.inl`, and `Sigma.ι F (some i)` to
`Sigma.ι (F ∘ some) i ≫ coprod.inr`. -/
noncomputable def sigmaOptionIso : (∐ F) ≅ F none ⨿ (∐ fun i ↦ F (some i)) :=
  (binaryCofanOptionSigma F).coconePointUniqueUpToIso
    (colimit.isColimit (pair (F none) (∐ fun i ↦ F (some i))))

@[reassoc (attr := simp)]
lemma ι_none_comp_sigmaOptionIso_hom : Sigma.ι F none ≫ (sigmaOptionIso F).hom = coprod.inl :=
  (binaryCofanOptionSigma F).comp_coconePointUniqueUpToIso_hom
    (colimit.isColimit (pair (F none) (∐ fun i ↦ F (some i)))) ⟨WalkingPair.left⟩

@[reassoc (attr := simp)]
lemma ι_some_comp_sigmaOptionIso_hom (i : ι) :
    Sigma.ι F (some i) ≫ (sigmaOptionIso F).hom =
      Sigma.ι (fun i ↦ F (some i)) i ≫ coprod.inr := by
  have h : (Sigma.desc fun i ↦ Sigma.ι F (some i)) ≫ (sigmaOptionIso F).hom = coprod.inr :=
    (binaryCofanOptionSigma F).comp_coconePointUniqueUpToIso_hom
      (colimit.isColimit (pair (F none) (∐ fun i ↦ F (some i)))) ⟨WalkingPair.right⟩
  rw [← h]
  simp

end Sigma

end CategoryTheory.Limits
