/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.AlgebraicGeometry.RelativeProj.Affine

/-!
# Quasi-coherent graded algebras, described on affine opens

Mathlib does not (yet) have quasi-coherent sheaves of graded `𝒪_X`-algebras. We model a
quasi-coherent graded `𝒪_X`-algebra `𝒜 = ⨁ₙ 𝒜ₙ` on a scheme `X` by its values on the affine
opens of `X`:

- for every affine open `U` an `ℕ`-graded commutative `Γ(X, U)`-algebra
  `A.grading U : ℕ → Submodule Γ(X, U) (A.obj U)` (playing the role of `Γ(U, 𝒜)`),
- for every inclusion `U ≤ V` of affine opens a restriction map `A.res : A(V) → A(U)`, which
  is a graded ring homomorphism, functorial in `U ≤ V`,
- **quasi-coherence**: for every inclusion `U ≤ V` of affine opens and every `n`, the
  restriction map `A(V)ₙ → A(U)ₙ` is `Γ(X, V) → Γ(X, U)`-semilinear and exhibits
  `A(U)ₙ` as the base change `Γ(X, U) ⊗_{Γ(X, V)} A(V)ₙ`
  (`GradedRingHom.IsGradedBaseChangeAlong`).

This is the standard description of quasi-coherent modules as compatible systems of modules
over the rings `Γ(X, U)`, `U` affine, with base change isomorphisms (quasi-coherent sheaves on
`X` are the limit of the categories of `Γ(X, U)`-modules along base change); applied in each
degree, compatibly with the multiplication. In particular, for a basic open `U = D(f) ⊆ V`, the
restriction map identifies `A(U)` with the coefficientwise localization `A(V)[1/f]`.

## Main definitions

- `AlgebraicGeometry.Scheme.GradedAlgebraData` — quasi-coherent graded algebras on `X`, described
  on affine opens (the input of the admissible blow-up construction).
- `AlgebraicGeometry.Scheme.GradedAlgebraData.Hom` — degree-preserving morphisms, and the
  category structure.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A **quasi-coherent graded `𝒪_X`-algebra**, described by its values on the affine opens of `X`.

It consists of, for every affine open `U`, a graded `Γ(X, U)`-algebra `A.grading U` on the ring
`A.obj U` (the sections over `U`), and for every inclusion `U ≤ V` of affine opens a graded
restriction homomorphism `A.res: A.grading V →+*ᵍ A.grading U`, functorial in `U ≤ V`.
**Quasi-coherence** is encoded by `isGradedBaseChangeAlong`: every restriction map is, in each
degree `n`, the base change `A(U)ₙ = Γ(X, U) ⊗_{Γ(X, V)} A(V)ₙ` along the restriction map
`Γ(X, V) → Γ(X, U)` of the structure sheaf. -/
structure GradedAlgebraData (X : Scheme.{u}) where
  /-- The sections over an affine open. -/
  obj : X.affineOpens → Type u
  [commRing (U : X.affineOpens) : CommRing (obj U)]
  [algebra (U : X.affineOpens) : Algebra Γ(X, U.1) (obj U)]
  /-- The grading of the sections over an affine open. -/
  grading (U : X.affineOpens) : ℕ → Submodule Γ(X, U.1) (obj U)
  [gradedAlgebra (U : X.affineOpens) : GradedAlgebra (grading U)]
  /-- The restriction maps. -/
  res {U V : X.affineOpens} (h : U ≤ V) : grading V →+*ᵍ grading U
  res_id (U : X.affineOpens) (x : obj U) : res le_rfl x = x
  res_res {U V W : X.affineOpens} (h₁ : U ≤ V) (h₂ : V ≤ W) (x : obj W) :
    res h₁ (res h₂ x) = res (h₁.trans h₂) x
  /-- Quasi-coherence: the restriction maps are coefficientwise base changes. -/
  isGradedBaseChangeAlong {U V : X.affineOpens} (h : U ≤ V) :
    (res h).IsGradedBaseChangeAlong (X.presheaf.map (homOfLE (X := X.Opens) h).op).hom

namespace GradedAlgebraData

attribute [instance] commRing algebra gradedAlgebra

variable {X : Scheme.{u}} (A : X.GradedAlgebraData)

lemma res_comp {U V W : X.affineOpens} (h₁ : U ≤ V) (h₂ : V ≤ W) :
    (A.res h₁).comp (A.res h₂) = A.res (h₁.trans h₂) :=
  GradedRingHom.ext fun x ↦ A.res_res h₁ h₂ x

lemma res_id' (U : X.affineOpens) : A.res (le_refl U) = .id _ :=
  GradedRingHom.ext fun x ↦ A.res_id U x

lemma res_algebraMap {U V : X.affineOpens} (h : U ≤ V) (r : Γ(X, V.1)) :
    A.res h (algebraMap _ _ r) =
      algebraMap _ _ (X.presheaf.map (homOfLE (X := X.Opens) h).op r) :=
  (A.isGradedBaseChangeAlong h).map_algebraMap r

lemma irrelevant_le_map_res {U V : X.affineOpens} (h : U ≤ V) :
    HomogeneousIdeal.irrelevant (A.grading U) ≤
      (HomogeneousIdeal.irrelevant (A.grading V)).map (A.res h) :=
  (A.isGradedBaseChangeAlong h).irrelevant_le

/-- A morphism of quasi-coherent graded algebras: degree-preserving `Γ(X, U)`-algebra
homomorphisms on every affine open `U`, compatible with the restriction maps. -/
@[ext]
structure Hom (A B : X.GradedAlgebraData) where
  /-- The component over an affine open. -/
  app (U : X.affineOpens) : A.grading U →+*ᵍ B.grading U
  app_algebraMap (U : X.affineOpens) (r : Γ(X, U.1)) : app U (algebraMap _ _ r) = algebraMap _ _ r
  naturality {U V : X.affineOpens} (h : U ≤ V) (x : A.obj V) :
    app U (A.res h x) = B.res h (app V x)

instance : Category X.GradedAlgebraData where
  Hom := Hom
  id A :=
    { app U := .id _
      app_algebraMap _ _ := rfl
      naturality _ _ := rfl }
  comp f g :=
    { app U := (g.app U).comp (f.app U)
      app_algebraMap U r := by
        simp only [GradedRingHom.comp_apply, f.app_algebraMap, g.app_algebraMap]
      naturality h x := by
        simp only [GradedRingHom.comp_apply, f.naturality, g.naturality] }
  id_comp f := Hom.ext (funext fun _ ↦ GradedRingHom.ext fun _ ↦ rfl)
  comp_id f := Hom.ext (funext fun _ ↦ GradedRingHom.ext fun _ ↦ rfl)
  assoc f g h := Hom.ext (funext fun _ ↦ GradedRingHom.ext fun _ ↦ rfl)

variable {A}

@[ext]
lemma hom_ext {B : X.GradedAlgebraData} {f g : A ⟶ B} (h : ∀ U, f.app U = g.app U) : f = g :=
  Hom.ext (funext h)

@[simp]
lemma id_app (U : X.affineOpens) : Hom.app (𝟙 A) U = .id _ :=
  rfl

@[simp]
lemma comp_app {B C : X.GradedAlgebraData} (f : A ⟶ B) (g : B ⟶ C) (U : X.affineOpens) :
    (f ≫ g).app U = (g.app U).comp (f.app U) :=
  rfl

end GradedAlgebraData

end AlgebraicGeometry.Scheme
