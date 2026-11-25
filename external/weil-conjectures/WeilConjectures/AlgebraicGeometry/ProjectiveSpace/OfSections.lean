/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace

/-!
# Morphisms into projective space given by global sections

A family `s : n → Γ(X, ⊤)` of global sections generating the unit ideal defines, over any
morphism `g : X ⟶ S`, a morphism `X ⟶ ℙ(n; S)` sending the `i`-th homogeneous coordinate `Tᵢ`
to `s i`. This is the case of the trivial line bundle in the description of morphisms into a
projective space by a line bundle together with generating sections, and it is what all
constructions of morphisms into a projective space in this development are built from.

The morphism is the base change along `g` of Mathlib's
`AlgebraicGeometry.Proj.fromOfGlobalSections` for the graded ring `ℤ[Tᵢ]`.

## Main definitions

- `AlgebraicGeometry.ProjectiveSpace.homOfSections` — the morphism `X ⟶ ℙ(n; S)` over `S`
  attached to a morphism `g : X ⟶ S` and a family of global sections `s : n → Γ(X, ⊤)`
  generating the unit ideal.
- `AlgebraicGeometry.ProjectiveSpace.standardOpen` — the standard open `D₊(Tᵢ)` of `ℙ(n; S)`.

## Main results

- `AlgebraicGeometry.ProjectiveSpace.iSup_standardOpen` — the standard opens cover `ℙ(n; S)`.
- `AlgebraicGeometry.ProjectiveSpace.homOfSections_preimage_standardOpen` — the preimage of
  `D₊(Tᵢ)` under `homOfSections g s hs` is the basic open `X_{s i}`.
- `AlgebraicGeometry.ProjectiveSpace.homOfSections_resLE_comp_toProjInt_resLE` — the induced
  morphism `X_{s i} ⟶ D₊(Tᵢ)` is, after passing to the integral model, Mathlib's
  `Proj.toBasicOpenOfGlobalSections`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MvPolynomial

noncomputable section

namespace AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X S : Scheme.{u}} {n : Type u}

/-- The ring homomorphism `ℤ[Tᵢ] →+* Γ(X, ⊤)` evaluating the variable `Tᵢ` at the global
section `s i`. -/
def evalSections (s : n → Γ(X, ⊤)) : MvPolynomial n (ULift.{u} ℤ) →+* Γ(X, ⊤) :=
  eval₂Hom ((Int.castRingHom Γ(X, ⊤)).comp (ULift.ringEquiv (R := ℤ)).toRingHom) s

@[simp]
lemma evalSections_X (s : n → Γ(X, ⊤)) (i : n) : evalSections s (MvPolynomial.X i) = s i :=
  eval₂Hom_X' _ _ i

/-- If the global sections `s i` generate the unit ideal, the image of the irrelevant ideal
of `ℤ[Tᵢ]` under `evalSections s` is the unit ideal. -/
lemma map_irrelevant_evalSections_eq_top (s : n → Γ(X, ⊤)) (hs : Ideal.span (Set.range s) = ⊤) :
    (HomogeneousIdeal.irrelevant (homogeneousSubmodule n (ULift.{u} ℤ))).toIdeal.map
      (evalSections s) = ⊤ := by
  rw [toIdeal_irrelevant_homogeneousSubmodule, Ideal.map_span, ← Set.range_comp]
  simpa [Function.comp_def] using hs

/-- `evalSections` is natural in `X`: restricting along a morphism `h : Y ⟶ X` evaluates the
homogeneous coordinates at the restricted sections. -/
lemma comp_evalSections {Y : Scheme.{u}} (h : Y ⟶ X) (s : n → Γ(X, ⊤)) :
    h.appTop.hom.comp (evalSections s) = evalSections fun i ↦ h.appTop.hom (s i) := by
  rw [evalSections, evalSections, comp_eval₂Hom]
  congr 1
  ext x
  simp

/-- Scaling all the sections by a global section `u` scales the value of `evalSections` at a
form of degree `i` by `u ^ i`. -/
lemma evalSections_const_mul {i : ℕ} (u : Γ(X, ⊤)) (s : n → Γ(X, ⊤))
    {a : MvPolynomial n (ULift.{u} ℤ)} (ha : a ∈ homogeneousSubmodule n (ULift.{u} ℤ) i) :
    evalSections (fun k ↦ u * s k) a = u ^ i * evalSections s a :=
  ((mem_homogeneousSubmodule _ _).mp ha).eval₂Hom_const_mul _ _ _

variable (g : X ⟶ S) (s : n → Γ(X, ⊤)) (hs : Ideal.span (Set.range s) = ⊤)

/-- The morphism `X ⟶ ℙ(n; S)` over `g : X ⟶ S` attached to a family `s : n → Γ(X, ⊤)` of
global sections generating the unit ideal, sending the homogeneous coordinate `Tᵢ` to `s i`.

This is the base change along `g` of `Proj.fromOfGlobalSections` for the graded ring `ℤ[Tᵢ]`. -/
def homOfSections : X ⟶ ℙ(n; S) :=
  pullback.lift g
    (Proj.fromOfGlobalSections _ (evalSections s) (map_irrelevant_evalSections_eq_top s hs))
    (terminal.hom_ext _ _)

/-- `homOfSections g s hs` is a morphism over `S`, namely over `g`. -/
@[reassoc (attr := simp)]
lemma homOfSections_over : homOfSections g s hs ≫ ℙ(n; S) ↘ S = g :=
  pullback.lift_fst _ _ _

/-- Composed with the map to the integral model `ℙⁿ_ℤ`, `homOfSections g s hs` is the
morphism into `Proj ℤ[Tᵢ]` given by `Tᵢ ↦ s i`. -/
@[reassoc (attr := simp)]
lemma homOfSections_toProjInt :
    homOfSections g s hs ≫ toProjInt n S =
      Proj.fromOfGlobalSections _ (evalSections s) (map_irrelevant_evalSections_eq_top s hs) :=
  pullback.lift_snd _ _ _

/-- The standard open `D₊(Tᵢ)` of `ℙ(n; S)`, i.e. the locus where the `i`-th homogeneous
coordinate does not vanish, defined as the preimage of the basic open `D₊(Tᵢ)` of the
integral model `ℙⁿ_ℤ`. -/
def standardOpen (n : Type u) (S : Scheme.{u}) (i : n) : ℙ(n; S).Opens :=
  toProjInt n S ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) (MvPolynomial.X i)

/-- **The standard opens cover projective space**: `ℙ(n; S)` is the union of the loci
`D₊(Tᵢ)` where the `i`-th homogeneous coordinate does not vanish. -/
@[simp]
lemma iSup_standardOpen (n : Type u) (S : Scheme.{u}) : ⨆ i, standardOpen n S i = ⊤ :=
  Scheme.Hom.iSup_preimage_eq_top _ <| Proj.iSup_basicOpen_eq_top _ _
    (toIdeal_irrelevant_homogeneousSubmodule n (ULift.{u} ℤ)).le

/-- A morphism into the standard open `D₊(Tᵢ)` of `ℙ(n; S)` is determined by its composites
with the structure morphism to `S` and with the map to the standard open `D₊(Tᵢ)` of the
integral model `ℙⁿ_ℤ`. -/
@[ext 1100]
lemma standardOpen_hom_ext {T : Scheme.{u}} {i : n} {f₁ f₂ : T ⟶ (standardOpen n S i).toScheme}
    (h₁ : f₁ ≫ (standardOpen n S i).ι ≫ ℙ(n; S) ↘ S =
      f₂ ≫ (standardOpen n S i).ι ≫ ℙ(n; S) ↘ S)
    (h₂ : f₁ ≫ (toProjInt n S).resLE _ (standardOpen n S i) le_rfl =
      f₂ ≫ (toProjInt n S).resLE _ (standardOpen n S i) le_rfl) : f₁ = f₂ := by
  rw [← cancel_mono (standardOpen n S i).ι]
  refine hom_ext n S ?_ ?_
  · simpa using h₁
  · simpa using congrArg (· ≫ (Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ))
      (MvPolynomial.X i)).ι) h₂

/-- The preimage of the standard open `D₊(Tᵢ)` under `homOfSections g s hs` is the basic open
where the section `s i` does not vanish. -/
lemma homOfSections_preimage_standardOpen (i : n) :
    homOfSections g s hs ⁻¹ᵁ standardOpen n S i = X.basicOpen (s i) := by
  rw [standardOpen, ← Scheme.Hom.comp_preimage, homOfSections_toProjInt,
    Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ Nat.one_pos
      ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X _ i)), evalSections_X]

/-- The morphism `X_{s i} ⟶ D₊(Tᵢ)` induced by `homOfSections g s hs` is, after passing to
the standard open `D₊(Tᵢ)` of the integral model `ℙⁿ_ℤ`, Mathlib's
`Proj.toBasicOpenOfGlobalSections`, i.e. the morphism of affine schemes given by the map
`ℤ[Tⱼ/Tᵢ] → Γ(X_{s i}, ⊤)` sending `Tⱼ/Tᵢ` to `s j / s i`. -/
lemma homOfSections_resLE_comp_toProjInt_resLE (i : n) :
    (homOfSections g s hs).resLE (standardOpen n S i) (X.basicOpen (s i))
        (homOfSections_preimage_standardOpen g s hs i).ge ≫
      (toProjInt n S).resLE _ (standardOpen n S i) le_rfl =
      Proj.toBasicOpenOfGlobalSections _ (evalSections s) (evalSections_X s i) Nat.one_pos
        ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X _ i)) := by
  have hd : MvPolynomial.X i ∈ homogeneousSubmodule n (ULift.{u} ℤ) 1 :=
    (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X _ i)
  suffices h : ∀ (x : Γ(X, ⊤)) (hx : evalSections s (MvPolynomial.X i) = x)
      (e : X.basicOpen x ≤ homOfSections g s hs ⁻¹ᵁ standardOpen n S i),
      (homOfSections g s hs).resLE (standardOpen n S i) (X.basicOpen x) e ≫
        (toProjInt n S).resLE _ (standardOpen n S i) le_rfl =
        Proj.toBasicOpenOfGlobalSections _ (evalSections s) hx Nat.one_pos hd from
    h _ (evalSections_X s i) _
  rintro x rfl e
  rw [← cancel_mono (Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ))
    (MvPolynomial.X i)).ι, Category.assoc, Scheme.Hom.resLE_comp_ι,
    Scheme.Hom.resLE_comp_ι_assoc, homOfSections_toProjInt,
    ← Proj.fromOfGlobalSections_resLE _ _ _ Nat.one_pos hd, Scheme.Hom.resLE_comp_ι]

/-- `homOfSections g s hs` restricted to the standard open `D₊(Tᵢ)` is still a morphism
over `g`. -/
@[reassoc]
lemma homOfSections_resLE_ι_over (i : n) :
    (homOfSections g s hs).resLE (standardOpen n S i) (X.basicOpen (s i))
        (homOfSections_preimage_standardOpen g s hs i).ge ≫
      (standardOpen n S i).ι ≫ ℙ(n; S) ↘ S = (X.basicOpen (s i)).ι ≫ g := by
  rw [Scheme.Hom.resLE_comp_ι_assoc, homOfSections_over]

end AlgebraicGeometry.ProjectiveSpace
