/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact

/-! # The cone of a scalar on a fiber complex

Let `τ` be a natural endomorphism of the identity of cochain complexes which is given termwise by
a natural endomorphism `s` of the identity of the abelian category, and let
`0 ⟶ A ⟶ X ⟶ X ⟶ 0` be a short exact sequence whose second map is `τ`, with `τ` vanishing on
`A⟦1⟧`. On the fiber model `P = mappingCone ε` of `X`, the strict map from the cone of `τ` to
`A⟦1⟧` with zero shifted component is homotopic, after composition with `ε⟦1⟧`, to minus the
cone boundary of `τ` followed by the comparison `P ⟶ X`. Consequently this strict map is a
quasi-isomorphism.

Source: Stacks Tags 014I, 014K and 06YP; the octahedral comparison of the principal cone with
the short exact sequence of a surjective scalar.
(blueprint: lem-sf-regular-quotient-trace-on-injective-terms). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe v u
open CategoryTheory CategoryTheory.Limits

namespace CochainComplex.mappingCone

open HomComplex

variable {𝒞 : Type u} [Category.{v} 𝒞] [Abelian 𝒞]
  (τ : 𝟭 (CochainComplex 𝒞 ℤ) ⟶ 𝟭 (CochainComplex 𝒞 ℤ))
  {A X : CochainComplex 𝒞 ℤ} (ε : A ⟶ X)

/-- If the scalar vanishes on `A⟦1⟧`, it is killed by the cone boundary of `ε : A ⟶ X`.
Source: Stacks Tag 014I; naturality of the scalar
(auxiliary; not a blueprint node). -/
theorem scalar_triangle_mor₃_zero (hA : τ.app (A⟦(1 : ℤ)⟧) = 0) :
    τ.app (mappingCone ε) ≫ (triangle ε).mor₃ = 0 := by
  have h : (triangle ε).mor₃ ≫ τ.app (A⟦(1 : ℤ)⟧) =
      τ.app (mappingCone ε) ≫ (triangle ε).mor₃ := τ.naturality (triangle ε).mor₃
  rw [← h, hA, comp_zero]

/-- The strict scalar-cone augmentation of the fiber model, followed by `ε⟦1⟧`, is homotopic to
minus the scalar-cone boundary followed by the shifted comparison to `X`. The homotopy has
components the negated shifted second projection of `mappingCone ε`.
Source: Stacks Tags 014I and 014K; explicit homotopies between maps out of a mapping cone
(blueprint: lem-sf-regular-quotient-trace-on-injective-terms). -/
def scalarConeHomotopy (s : 𝟭 𝒞 ⟶ 𝟭 𝒞)
    (hτ : ∀ (K : CochainComplex 𝒞 ℤ) (n : ℤ), (τ.app K).f n = s.app (K.X n))
    (hε : ε ≫ τ.app X = 0) (hA : τ.app (A⟦(1 : ℤ)⟧) = 0) :
    Homotopy (desc (τ.app (mappingCone ε)) 0 (triangle ε).mor₃
        (by simp [scalar_triangle_mor₃_zero τ ε hA]) ≫ ε⟦(1 : ℤ)⟧')
      (-((triangle (τ.app (mappingCone ε))).mor₃ ≫
        (descShortComplex (ShortComplex.mk ε (τ.app X) hε))⟦(1 : ℤ)⟧')) :=
  descHomotopy _ _ _ 0 (-((snd ε).rightShift 1 (-1) (by omega))) (by
    ext p q hpq
    obtain rfl : p = q + 1 := by omega
    have hs : (τ.app (mappingCone ε)).f (q + 1) ≫ (snd ε).v (q + 1) (q + 1) (add_zero _) =
        (snd ε).v (q + 1) (q + 1) (add_zero _) ≫ (τ.app X).f (q + 1) := by
      rw [hτ, hτ]
      exact (s.naturality _).symm
    have hd : (descShortComplex (ShortComplex.mk ε (τ.app X) hε)).f (q + 1) =
        (snd ε).v (q + 1) (q + 1) (add_zero _) ≫ (τ.app X).f (q + 1) := by
      simp [descShortComplex, desc_f _ _ _ _ (q + 1) (q + 2) (by omega)]
    simp [Cochain.comp_v _ _ (add_zero (-1)) (q + 1) q q hpq (add_zero q),
      Cochain.comp_v _ _ (zero_add (-1)) (q + 1) (q + 1) q (add_zero _) hpq,
      Cochain.rightShift_v _ 1 (-1) _ (q + 1) q hpq (q + 1) (add_zero _), hd, hs]) (by
    rw [δ_neg, Cochain.δ_rightShift _ 1 (-1) 0 (by omega) 1 (by omega), δ_snd]
    ext p
    have hm : (triangle ε).mor₃.f p = -(fst ε).1.v p (p + 1) rfl := by
      simp [triangle, Cochain.rightShift_v _ 1 0 _ p p (add_zero p) (p + 1) rfl]
    simp [Cochain.rightShift_v _ 1 0 _ p p (add_zero p) (p + 1) rfl, hm])

open DerivedCategory Pretriangulated in
/-- For a short exact sequence `0 ⟶ A ⟶ X ⟶ X ⟶ 0` with second map the scalar, the strict
scalar-cone augmentation `Cone(τ_P) ⟶ A⟦1⟧` of the fiber model `P = mappingCone ε` is a
quasi-isomorphism.
Source: Stacks Tags 014I, 014K and 05SS; a morphism from the scalar-cone triangle to the
rotated short-exact-sequence triangle which is invertible on the first two objects
(blueprint: lem-sf-regular-quotient-trace-on-injective-terms).

Proof: the comparison `p : P ⟶ X` is a quasi-isomorphism and commutes with the scalar. The
connecting morphism of the short exact sequence is the cone boundary of `ε` precomposed with
the inverse of `p`, and the third square commutes by the homotopy `scalarConeHomotopy`. -/
theorem isIso_Q_map_scalarConeDesc [HasDerivedCategory 𝒞] (s : 𝟭 𝒞 ⟶ 𝟭 𝒞)
    (hτ : ∀ (K : CochainComplex 𝒞 ℤ) (n : ℤ), (τ.app K).f n = s.app (K.X n))
    (hε : ε ≫ τ.app X = 0) (hA : τ.app (A⟦(1 : ℤ)⟧) = 0)
    (hS : (ShortComplex.mk ε (τ.app X) hε).ShortExact) :
    IsIso (Q.map (desc (τ.app (mappingCone ε)) 0 (triangle ε).mor₃
        (by simp [scalar_triangle_mor₃_zero τ ε hA]))) := by
  let P := mappingCone ε
  let tP := τ.app P
  let p := descShortComplex (ShortComplex.mk ε (τ.app X) hε)
  let d := desc (τ.app (mappingCone ε)) 0 (triangle ε).mor₃
    (by simp [scalar_triangle_mor₃_zero τ ε hA])
  have : QuasiIso p := quasiIso_descShortComplex hS
  have hh := Q_map_eq_of_homotopy _
    (scalarConeHomotopy (τ := τ) (ε := ε) (s := s) (hτ := hτ) (hε := hε) (hA := hA))
  let φ : Q.mapTriangle.obj (triangle tP) ⟶ (triangleOfSES hS).rotate :=
    { hom₁ := Q.map p
      hom₂ := Q.map p
      hom₃ := Q.map d ≫ (Q.commShiftIso (1 : ℤ)).hom.app A
      comm₁ := by
        change Q.map tP ≫ Q.map p = Q.map p ≫ Q.map (τ.app X)
        rw [← Q.map_comp, ← Q.map_comp]
        exact congrArg Q.map (τ.naturality p).symm
      comm₂ := by
        change Q.map (inr tP) ≫ Q.map d ≫ (Q.commShiftIso (1 : ℤ)).hom.app A =
          Q.map p ≫ triangleOfSESδ hS
        rw [descShortComplex_triangleOfSESδ, ← Q.map_comp_assoc, inr_desc]
      comm₃ := by
        change (Q.map (triangle tP).mor₃ ≫ (Q.commShiftIso (1 : ℤ)).hom.app P) ≫
            (Q.map p)⟦(1 : ℤ)⟧' =
          (Q.map d ≫ (Q.commShiftIso (1 : ℤ)).hom.app A) ≫ (-((Q.map ε)⟦(1 : ℤ)⟧'))
        rw [Category.assoc, Category.assoc, Preadditive.comp_neg,
          ← Functor.commShiftIso_hom_naturality, ← Functor.commShiftIso_hom_naturality,
          ← Q.map_comp_assoc, Preadditive.comp_neg, ← Q.map_comp_assoc]
        erw [hh]
        rw [Q.map_neg, Preadditive.neg_comp, neg_neg]
        rfl }
  have h₃ := isIso₃_of_isIso₁₂ φ (mappingCone_triangle_distinguished tP)
    (rot_of_distTriang _ (triangleOfSES_distinguished hS)) (by dsimp [φ]; infer_instance)
    (by dsimp [φ]; infer_instance)
  have : IsIso (Q.map d ≫ (Q.commShiftIso (1 : ℤ)).hom.app A) := h₃
  exact IsIso.of_isIso_comp_right (Q.map d) ((Q.commShiftIso (1 : ℤ)).hom.app A)

end CochainComplex.mappingCone
