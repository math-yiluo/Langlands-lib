/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Localization.Linear
public import Mathlib.CategoryTheory.Localization.Triangulated
public import Mathlib.CategoryTheory.Shift.Linear
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.RingTheory.Localization.Defs

/-!

# Rationalization of an `R`-linear triangulated category

Let `C` be a triangulated category which is linear over a commutative ring `R`, with
`R`-linear shift functors, and let `M` be a submonoid of `R`. An object `X` of `C` is
*`M`-torsion* if `m • 𝟙 X = 0` for some `m ∈ M`. The `M`-torsion objects form a
triangulated subcategory `Rationalization.torsion M C`, and the *rationalization*

```
  Rationalization M C  :=  C / (M-torsion objects)
```

is the Verdier quotient by it: the localization of `C` at the class
`Rationalization.W M C` of morphisms whose mapping cone is annihilated by an element of
`M`. It is again a triangulated category, and the localization functor
`Rationalization.Q M C : C ⥤ Rationalization M C` is a triangulated functor.

For `m ∈ M` the mapping cone of `m • 𝟙 X` is annihilated by `m²`
(`Rationalization.smul_id_cone_eq_zero`), so the morphisms `m • 𝟙 X` are inverted in the
rationalization. Consequently every `m ∈ M` acts invertibly on the `Hom` groups of
`Rationalization M C`, and the rationalization is linear over any localization `A` of `R`
at `M` (`Rationalization.linear`), compatibly with its `R`-linear structure
(`Rationalization.algebraMap_smul`). Inverting a single element `π` of `R` is the case
`M = Submonoid.powers π`; the case of interest downstream is that of the ring of integers
`R = 𝒪_E` of an `ℓ`-adic field `E`, with `M` its nonzero elements and `A = E`.

## Main definitions

- `CategoryTheory.Rationalization.torsion` : the `M`-torsion objects of `C`.
- `CategoryTheory.Rationalization.W` : the morphisms with `M`-torsion mapping cone.
- `CategoryTheory.Rationalization` : the Verdier quotient of `C` by the `M`-torsion
  objects, a triangulated category.
- `CategoryTheory.Rationalization.Q` : the localization functor `C ⥤ Rationalization M C`.
- `CategoryTheory.Rationalization.linear` : the `A`-linear structure, for `A` a
  localization of `R` at `M`.

## Main results

- `CategoryTheory.Rationalization.instIsTriangulatedTorsion` : the `M`-torsion objects form
  a triangulated subcategory.
- `CategoryTheory.Rationalization.W_smul_id` : `m • 𝟙 X` lies in `W M C` for `m ∈ M`.
- `CategoryTheory.Rationalization.isIso_smul_id` : `m • 𝟙 Y` is an isomorphism of the
  rationalization for `m ∈ M`.

-/

@[expose] public section

universe w' w v u

open CategoryTheory Category Limits Pretriangulated ZeroObject

namespace CategoryTheory

variable {R : Type w} [CommRing R] (M : Submonoid R) (C : Type u) [Category.{v} C]
  [Preadditive C] [Linear R C]

namespace Rationalization

/-- An object `X` is *`M`-torsion* if `m • 𝟙 X = 0` for some `m ∈ M`. -/
def torsion : ObjectProperty C :=
  fun X ↦ ∃ m ∈ M, m • 𝟙 X = 0

variable {M C}

lemma torsion_iff (X : C) : torsion M C X ↔ ∃ m ∈ M, m • 𝟙 X = 0 := Iff.rfl

/-- Multiplication by `m` on an object, conjugated by an isomorphism. -/
lemma smul_id_eq_conj {X Y : C} (e : X ≅ Y) (m : R) :
    m • 𝟙 Y = e.inv ≫ (m • 𝟙 X) ≫ e.hom := by
  simp

instance : (torsion M C).IsClosedUnderIsomorphisms where
  of_iso e := by
    rintro ⟨m, hm, h⟩
    exact ⟨m, hm, by rw [smul_id_eq_conj e, h, zero_comp, comp_zero]⟩

section Pretriangulated

variable [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor C n).Linear R] [Pretriangulated C]

instance : (torsion M C).ContainsZero where
  exists_zero := ⟨0, isZero_zero C, 1, M.one_mem, (isZero_zero C).eq_of_src _ _⟩

instance : (torsion M C).IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨fun _ ⟨m, hm, h⟩ ↦ ⟨m, hm, by
    rw [← Functor.map_id, ← Functor.map_smul, h, Functor.map_zero]⟩⟩

omit [∀ n : ℤ, (shiftFunctor C n).Linear R] in
/-- In a distinguished triangle `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧`, if `m₁` kills `X₁` and `m₃` kills
`X₃`, then `m₁ m₃` kills `X₂`. -/
lemma smul_id_obj₂_eq_zero {T : Triangle C} (hT : T ∈ distTriang C) {m₁ m₃ : R}
    (h₁ : m₁ • 𝟙 T.obj₁ = 0) (h₃ : m₃ • 𝟙 T.obj₃ = 0) : (m₁ * m₃) • 𝟙 T.obj₂ = 0 := by
  obtain ⟨b, hb⟩ := Triangle.coyoneda_exact₂ T hT (m₃ • 𝟙 T.obj₂) (by
    simpa using congrArg (T.mor₂ ≫ ·) h₃)
  have h : m₁ • T.mor₁ = 0 := by simpa using congrArg (· ≫ T.mor₁) h₁
  rw [mul_smul, hb, ← Linear.comp_smul, h, comp_zero]

instance instIsTriangulatedTorsion : (torsion M C).IsTriangulated where
  toIsTriangulatedClosed₂ := .mk' fun _ hT ⟨m₁, hm₁, h₁⟩ ⟨m₃, hm₃, h₃⟩ ↦
    ⟨m₁ * m₃, M.mul_mem hm₁ hm₃, smul_id_obj₂_eq_zero hT h₁ h₃⟩

/-- The mapping cone of `m • 𝟙 X` is killed by `m²`. -/
lemma smul_id_cone_eq_zero {X Z : C} (m : R) (g : X ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (m • 𝟙 X) g h ∈ distTriang C) : (m * m) • 𝟙 Z = 0 := by
  obtain ⟨u, hu⟩ := Triangle.yoneda_exact₃ _ hT (X := Z) (m • 𝟙 Z) (by
    have := comp_distTriang_mor_zero₁₂ _ hT
    simp only [Triangle.mk_mor₁, Triangle.mk_mor₂, Linear.smul_comp] at this
    erw [id_comp] at this
    change g ≫ (m • 𝟙 Z) = 0
    simpa using this)
  have h₀ : m • h = 0 := by
    have := comp_distTriang_mor_zero₃₁ _ hT
    simp only [Triangle.mk_mor₃, Triangle.mk_mor₁, Functor.map_smul, Linear.comp_smul] at this
    erw [Functor.map_id, comp_id] at this
    exact this
  change m • 𝟙 Z = h ≫ u at hu
  rw [mul_smul, hu, ← Linear.smul_comp, h₀, zero_comp]

variable (M C)

/-- The morphisms whose mapping cone is `M`-torsion. These are the morphisms inverted in
the rationalization. -/
@[reducible]
def W : MorphismProperty C := (torsion M C).trW

variable {M C}

/-- For `m ∈ M`, multiplication by `m` has `M`-torsion mapping cone. -/
lemma W_smul_id {m : R} (hm : m ∈ M) (X : C) : W M C (m • 𝟙 X) := by
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle (m • 𝟙 X)
  exact ObjectProperty.trW.mk _ hT ⟨m * m, M.mul_mem hm hm, smul_id_cone_eq_zero m g h hT⟩

end Pretriangulated

end Rationalization

variable [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor C n).Linear R] [Pretriangulated C] [IsTriangulated C]

/-- Blueprint `proposition-inverting-ell--2`: Rationalization (scalar localization),
`C[1/ϖ]`: the same objects as `C` (`CategoryTheory.Rationalization.essSurj_Q`) and morphisms
`Hom_C(K, L) ⊗_{𝒪_E} E` (`CategoryTheory.Rationalization.isLocalizedModule_mapLinearMap`); no
Karoubi completion is taken.

The *rationalization* of an `R`-linear triangulated category `C` at a submonoid `M` of
`R`: the Verdier quotient of `C` by the triangulated subcategory of `M`-torsion objects,
i.e. the localization of `C` at the morphisms whose mapping cone is annihilated by some
element of `M`. -/
@[reducible]
def Rationalization : Type _ := (Rationalization.W M C).Localization

namespace Rationalization

/-- The localization functor from `C` to its rationalization. -/
@[reducible]
noncomputable def Q : C ⥤ Rationalization M C := (W M C).Q

instance : (Q M C).IsTriangulated :=
  Triangulated.Localization.isTriangulated_functor (Q M C) (W M C)

variable {M C}

/-- For `m ∈ M`, multiplication by `m` is an isomorphism of every object of the
rationalization. -/
lemma isIso_smul_id {m : R} (hm : m ∈ M) (Y : Rationalization M C) : IsIso (m • 𝟙 Y) := by
  have e := (Q M C).objObjPreimageIso Y
  have : IsIso (m • 𝟙 ((Q M C).obj ((Q M C).objPreimage Y))) := by
    rw [← (Q M C).map_id, ← Functor.map_smul]
    exact Localization.inverts (Q M C) (W M C) _ (W_smul_id hm _)
  rw [smul_id_eq_conj e]
  infer_instance

open scoped IsMulCommutative

/-- The image of `m ∈ M` in the center of the rationalization is a unit. -/
lemma isUnit_toCatCenter {m : R} (hm : m ∈ M) :
    IsUnit (Linear.toCatCenter R (Rationalization M C) m) := by
  rw [isUnit_iff_isIso]
  have (Y : Rationalization M C) : IsIso ((Linear.toCatCenter R _ m).app Y) :=
    isIso_smul_id hm Y
  exact NatIso.isIso_of_isIso_app _

variable (M C) (A : Type w') [CommRing A] [Algebra R A] [IsLocalization M A]

/-- The action of a localization `A` of `R` at `M` on the rationalization, as a ring
morphism to its center. -/
noncomputable def toCatCenter : A →+* CatCenter (Rationalization M C) :=
  IsLocalization.lift (M := M) (g := Linear.toCatCenter R (Rationalization M C))
    fun m ↦ isUnit_toCatCenter m.2

/-- The rationalization of `C` at `M` is linear over any localization `A` of `R` at `M`,
for instance over the fraction field of `R` when `M` is the set of nonzero divisors. -/
noncomputable instance linear : Linear A (Rationalization M C) :=
  Linear.ofRingMorphism (toCatCenter M C A)

variable {M C}

/-- The `A`-linear structure of the rationalization extends its `R`-linear structure. -/
lemma algebraMap_smul (r : R) {X Y : Rationalization M C} (f : X ⟶ Y) :
    algebraMap R A r • f = r • f := by
  change (toCatCenter M C A (algebraMap R A r)).app X ≫ f = r • f
  rw [toCatCenter, IsLocalization.lift_eq]
  change (r • 𝟙 X) ≫ f = r • f
  rw [Linear.smul_comp, id_comp]

end Rationalization

end CategoryTheory
