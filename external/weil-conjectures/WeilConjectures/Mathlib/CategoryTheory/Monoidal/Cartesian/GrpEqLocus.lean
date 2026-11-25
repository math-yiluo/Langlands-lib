/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# Equalizers of morphisms of group objects

In a cartesian monoidal category, the equalizer of two morphisms `f g : G ⟶ H` is the fibre
product of `lift f g : G ⟶ H ⊗ H` with the diagonal `lift (𝟙 H) (𝟙 H) : H ⟶ H ⊗ H`:

```
  eqLocus f g ──── eqLocusι f g ────▶ G
       │                              │
       │                              │ lift f g
       ▼                              ▼
       H ─────── lift (𝟙 H) (𝟙 H) ──▶ H ⊗ H
```

Its `Y`-points are the `Y`-points `a` of `G` with `a ≫ f = a ≫ g`. For morphisms of group objects
the unit, multiplication and inverse of `G` factor through it, so it is a group object
(`CategoryTheory.GrpObj.ofMono`) and its inclusion into `G` is a morphism of group objects.

## Main definitions

- `CategoryTheory.GrpObj.eqLocus`: the equalizer of two morphisms into a cartesian monoidal
  category.
- `CategoryTheory.GrpObj.eqLocusι`: its canonical morphism to the source.
- `CategoryTheory.GrpObj.eqLocusLift`: the universal property of the equalizer.

## Main statements

- `CategoryTheory.GrpObj.mono_eqLocusι`: `eqLocusι f g` is a monomorphism.
- `CategoryTheory.GrpObj.isMonHom_eqLocusι`: for morphisms of group objects, `eqLocusι f g` is a
  morphism of group objects.
-/

@[expose] public section

namespace CategoryTheory

open Limits MonoidalCategory CartesianMonoidalCategory MonObj

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

namespace GrpObj

variable {G H : C} (f g : G ⟶ H) [HasPullback (lift f g) (lift (𝟙 H) (𝟙 H))]

/-- The equalizer of two morphisms `f g : G ⟶ H`: the fibre product of `lift f g : G ⟶ H ⊗ H`
with the diagonal of `H`. For morphisms of group schemes this is the subgroup scheme on which
`f` and `g` agree. -/
noncomputable def eqLocus : C :=
  pullback (lift f g) (lift (𝟙 H) (𝟙 H))

/-- The canonical morphism from the equalizer of `f` and `g` to their source. -/
noncomputable def eqLocusι : eqLocus f g ⟶ G :=
  pullback.fst _ _

theorem pullback_snd_eq_eqLocusι_comp :
    pullback.snd (lift f g) (lift (𝟙 H) (𝟙 H)) = eqLocusι f g ≫ f := by
  have h := congrArg (· ≫ fst H H) (pullback.condition (f := lift f g) (g := lift (𝟙 H) (𝟙 H)))
  simp only [Category.assoc, lift_fst, Category.comp_id] at h
  exact h.symm

theorem pullback_snd_eq_eqLocusι_comp' :
    pullback.snd (lift f g) (lift (𝟙 H) (𝟙 H)) = eqLocusι f g ≫ g := by
  have h := congrArg (· ≫ snd H H) (pullback.condition (f := lift f g) (g := lift (𝟙 H) (𝟙 H)))
  simp only [Category.assoc, lift_snd, Category.comp_id] at h
  exact h.symm

/-- The two morphisms agree on their equalizer. -/
@[reassoc]
theorem eqLocusι_comp_eq : eqLocusι f g ≫ f = eqLocusι f g ≫ g :=
  (pullback_snd_eq_eqLocusι_comp f g).symm.trans (pullback_snd_eq_eqLocusι_comp' f g)

/-- The universal property of the equalizer: a morphism `a : X ⟶ G` with `a ≫ f = a ≫ g`
factors through `eqLocus f g`. -/
noncomputable def eqLocusLift {X : C} (a : X ⟶ G) (h : a ≫ f = a ≫ g) : X ⟶ eqLocus f g :=
  pullback.lift a (a ≫ f) (by ext <;> simp [h])

@[reassoc (attr := simp)]
theorem eqLocusLift_eqLocusι {X : C} (a : X ⟶ G) (h : a ≫ f = a ≫ g) :
    eqLocusLift f g a h ≫ eqLocusι f g = a :=
  pullback.lift_fst _ _ _

/-- The inclusion of the equalizer is a monomorphism. -/
instance mono_eqLocusι : Mono (eqLocusι f g) :=
  ⟨fun a b h ↦ pullback.hom_ext h (by
    rw [pullback_snd_eq_eqLocusι_comp, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ f) h)⟩

theorem eqLocusLift_unique {X : C} (a : X ⟶ G) (h : a ≫ f = a ≫ g) (l : X ⟶ eqLocus f g)
    (hl : l ≫ eqLocusι f g = a) : l = eqLocusLift f g a h :=
  (cancel_mono (eqLocusι f g)).1 (by rw [hl, eqLocusLift_eqLocusι])

/-- A morphism `a : X ⟶ G` factors through the equalizer of `f` and `g` if and only if
`a ≫ f = a ≫ g`. -/
theorem exists_comp_eqLocusι_iff {X : C} (a : X ⟶ G) :
    (∃ l : X ⟶ eqLocus f g, l ≫ eqLocusι f g = a) ↔ a ≫ f = a ≫ g := by
  refine ⟨?_, fun h ↦ ⟨eqLocusLift f g a h, eqLocusLift_eqLocusι f g a h⟩⟩
  rintro ⟨l, rfl⟩
  rw [Category.assoc, Category.assoc, eqLocusι_comp_eq]

section GroupStructure

variable [GrpObj G] [GrpObj H] [IsMonHom f] [IsMonHom g]

omit [HasPullback (lift f g) (lift (𝟙 H) (𝟙 H))] in
theorem eqLocus_one_comp_eq : η[G] ≫ f = η[G] ≫ g := by
  rw [IsMonHom.one_hom, IsMonHom.one_hom]

theorem eqLocus_mul_comp_eq :
    ((eqLocusι f g ⊗ₘ eqLocusι f g) ≫ μ[G]) ≫ f = ((eqLocusι f g ⊗ₘ eqLocusι f g) ≫ μ[G]) ≫ g := by
  rw [Category.assoc, Category.assoc, IsMonHom.mul_hom, IsMonHom.mul_hom,
    tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom_assoc, eqLocusι_comp_eq]

theorem eqLocus_inv_comp_eq : (eqLocusι f g ≫ ι[G]) ≫ f = (eqLocusι f g ≫ ι[G]) ≫ g := by
  rw [Category.assoc, Category.assoc, GrpObj.inv_hom, GrpObj.inv_hom, eqLocusι_comp_eq_assoc]

/-- The equalizer of two morphisms of group objects is a group object: the unit, multiplication
and inverse of `G` factor through it. -/
noncomputable instance instGrpObjEqLocus : GrpObj (eqLocus f g) :=
  GrpObj.ofMono (eqLocusι f g) ⟨eqLocusLift f g η[G] (eqLocus_one_comp_eq f g), by simp⟩
    ⟨eqLocusLift f g _ (eqLocus_mul_comp_eq f g), by simp⟩
    ⟨eqLocusLift f g _ (eqLocus_inv_comp_eq f g), by simp⟩

/-- The inclusion of the equalizer of two morphisms of group objects is a morphism of group
objects. -/
instance isMonHom_eqLocusι : IsMonHom (eqLocusι f g) :=
  GrpObj.isMonHom_ofMono _ _ _ _

end GroupStructure

end GrpObj

end CategoryTheory
