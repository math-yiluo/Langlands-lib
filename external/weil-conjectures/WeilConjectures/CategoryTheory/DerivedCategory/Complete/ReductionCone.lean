/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone

/-!
# Reduction modulo a scalar as a mapping cone, for a `DerivedCategory.TensorStructure`

The results of `WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone` are
restated here for a `DerivedCategory.TensorStructure` `T` equal to
`DerivedCategory.tensorStructure A R`, the monoidal structure of `D(A)` being `T.monoidalCategory`.
This is the form in which the derived completion diagrams of
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs` use the derived tensor product:
they are stated with `T = DerivedCategory.sheafTensorStructure J R`. The equation `T = …` is
substituted away in the proofs, so that no definitional unfolding of the monoidal structure of a
concrete derived category is needed (see the implementation notes of
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs`).

## Main definitions

- `DerivedCategory.TensorStructure.reductionIso`: for a short exact sequence
  `0 ⟶ 𝟙 ⟶ 𝟙 ⟶ M ⟶ 0` whose first map is `r`, the isomorphism `Q X ⊗ᴸ M ≅ Q (cone(r : X ⟶ X))`.
-/

@[expose] public section

universe v u

open CategoryTheory Category Limits MonoidalCategory

namespace DerivedCategory.TensorStructure

open CochainComplex

variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
  [HasDerivedCategory.{v} A]
  [MonoidalCategory A] [MonoidalClosed A] [MonoidalPreadditive A] [BraidedCategory A]
  [Abelian.HasFunctorialFlatResolution A]
  {R : Type*} [CommRing R] [Linear R A] [MonoidalLinear R A]
  (T : TensorStructure.{v} A R) (hT : T = tensorStructure.{v} A R)

local instance : HasColimitsOfSize.{0, 0} A := hasColimitsOfSizeShrink A

section Reduction

variable {r : R} {M : A} {p : 𝟙_ A ⟶ M} (w : (r • 𝟙 (𝟙_ A)) ≫ p = 0)
  (hS : (ShortComplex.mk (r • 𝟙 (𝟙_ A)) p w).ShortExact)

/-- The isomorphism `Q X ⊗ᴸ M ≅ Q (cone(r : X ⟶ X))` for a short exact sequence
`0 ⟶ 𝟙 ⟶ 𝟙 ⟶ M ⟶ 0` whose first map is `r`, the tensor product being `T.monoidalCategory`. -/
noncomputable def reductionIso (X : CochainComplex A ℤ) :
    letI := T.monoidalCategory
    Q.obj X ⊗ (singleFunctor A 0).obj M ≅ Q.obj (mappingCone (r • 𝟙 X)) := by
  subst hT
  exact DerivedCategory.reductionIso w hS X

lemma reductionIso_hom_naturality {X Y : CochainComplex A ℤ} (f : X ⟶ Y) :
    letI := T.monoidalCategory
    (Q.map f ▷ _) ≫ (reductionIso T hT w hS Y).hom =
      (reductionIso T hT w hS X).hom ≫
        Q.map (mappingCone.map (r • 𝟙 X) (r • 𝟙 Y) f f (by simp)) := by
  subst hT
  exact DerivedCategory.reductionIso_hom_naturality w hS f

/-- Under `reductionIso`, the reduction `X ⟶ X ⊗ᴸ M` is the inclusion `X ⟶ cone(r)`. -/
lemma reduction_reductionIso_hom (X : CochainComplex A ℤ) :
    letI := T.monoidalCategory
    (ρ_ (Q.obj X)).inv ≫ Q.obj X ◁ (T.ε ≫ (singleFunctor A 0).map p) ≫
        (reductionIso T hT w hS X).hom =
      Q.map (mappingCone.inr (r • 𝟙 X)) := by
  subst hT
  exact DerivedCategory.reduction_reductionIso_hom w hS X

end Reduction

section ChangeOfScalar

variable {r₁ r₂ s : R} (hr : r₂ * s = r₁)
  {M₁ M₂ : A} {p₁ : 𝟙_ A ⟶ M₁} {p₂ : 𝟙_ A ⟶ M₂} (w₁ : (r₁ • 𝟙 (𝟙_ A)) ≫ p₁ = 0)
  (w₂ : (r₂ • 𝟙 (𝟙_ A)) ≫ p₂ = 0)
  (hS₁ : (ShortComplex.mk (r₁ • 𝟙 (𝟙_ A)) p₁ w₁).ShortExact)
  (hS₂ : (ShortComplex.mk (r₂ • 𝟙 (𝟙_ A)) p₂ w₂).ShortExact)
  (q : M₁ ⟶ M₂) (hq : p₁ ≫ q = p₂)

include hr hq in
/-- `reductionIso` is compatible with a change of the scalar `r₁ = r₂ s`. -/
lemma whiskerLeft_reductionIso_hom (X : CochainComplex A ℤ) :
    letI := T.monoidalCategory
    (Q.obj X ◁ (singleFunctor A 0).map q) ≫ (reductionIso T hT w₂ hS₂ X).hom =
      (reductionIso T hT w₁ hS₁ X).hom ≫ Q.map (mappingCone.map (r₁ • 𝟙 X) (r₂ • 𝟙 X) (s • 𝟙 X)
        (𝟙 X) (smul_comp_smul_eq hr X).symm) := by
  subst hT
  exact DerivedCategory.whiskerLeft_reductionIso_hom hr w₁ w₂ hS₁ hS₂ q hq X

end ChangeOfScalar

end DerivedCategory.TensorStructure
