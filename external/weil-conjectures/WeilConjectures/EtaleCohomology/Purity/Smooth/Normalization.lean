/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Trace

/-!
# Normalization of the smooth trace on the affine line

The fundamental class of the affine line `p : 𝔸¹_k ⟶ Spec k` is the image of the orientation
`pur_s : Λ_{V(t)} ⟶ Rs^! Λ(1)[2]` of its zero section
(`AlgebraicGeometry.Etale.affineLineOrientation`)
under `Rp_!` and the counit of `Rs_! ⊣ Rs^!`:

`cl : Λ ≅ R(s ≫ p)_! Λ ≅ Rp_! Rs_! Λ ⟶ Rp_! Rs_! Rs^! Λ(1)[2] ⟶ Rp_! Λ(1)[2]`.

The statement proved here is that *some* purity isomorphism `γ` has `Tr^sm_p(cl) = 1`. It does
not single out the canonical `γ` of blueprint `proposition-transitivity-trace-map--1`
(normalized on the projective line): the orientation `pur_s` is the Kummer boundary `∂κ(t)`,
which forgets supports to `-c₁(𝒪(V(t)))` (blueprint `lemma-cycle-class-cartier-divisor` (b)), so for
the canonical `γ` the trace of `cl` is `-1`, and `(-1)^d` for the ordered fundamental class of
`𝔸^d`.

## Main definitions

- `AlgebraicGeometry.Etale.affineLineFundamentalClass`: the fundamental class `cl`.

## Main statements

- `AlgebraicGeometry.Etale.isIso_affineLineFundamentalClass_comp_smoothPurityTrace`: for every
  purity isomorphism, the trace of the fundamental class is invertible. It is the adjoint of the
  orientation, which is an isomorphism, and the counit of `R(s ≫ p)_! ⊣ R(s ≫ p)^!` is an
  isomorphism since `s ≫ p` is.
- `AlgebraicGeometry.Etale.exists_affineLineFundamentalClass_comp_smoothPurityTrace`: for some
  purity isomorphism, the trace of the fundamental class is `1`.

## Implementation notes

The composition isomorphism `α : R(s ≫ p)_! ≅ Rs_! ⋙ Rp_!` and the identification
`ψ : Λ_k ≅ R(s ≫ p)_! Λ_{V(t)}` (the morphism `s ≫ p` is an isomorphism) are only known to
exist, so they are arguments; the purity map of `p` is only known to exist as well, so the
normalization asserts that some purity map is normalized, which is the form in which it
determines the canonical one.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ] (Y : Scheme.{u})
  [HasInvertibleExponent Λ Y]
  [HasCompactification (𝔸(ULift.{u} (Fin 1); Y).zeroLocusSubschemeι
    {AffineSpace.coord Y (ULift.up 0)} ≫ (𝔸(ULift.{u} (Fin 1); Y) ↘ Y))]

/-- The identification `Lp^* Λ_Y(1)[2] ≅ Λ_{𝔸¹}(1)[2]` of the source of the smooth trace of the
affine line with the shifted Tate twist. -/
noncomputable def affineLineTwistShiftIso :
    (twistShift Λ 𝔸(ULift.{u} (Fin 1); Y) ((1 : ℕ) : ℤ)).obj
        ((L((𝔸(ULift.{u} (Fin 1); Y) ↘ Y)^*[ModuleCat.{u + 1} Λ])).obj (constantComplex Λ Y)) ≅
      (tateObject Λ 𝔸(ULift.{u} (Fin 1); Y) 1)⟦(2 : ℤ)⟧ :=
  (twistShift Λ _ _).mapIso (leftDerivedUpperStarConstantComplexIso Λ _) ≪≫
    twistShiftConstantComplexIso Λ _ _ ≪≫ eqToIso (by norm_num)

/-- The fundamental class `cl : R(s ≫ p)_! Λ ⟶ Rp_! Λ(1)[2]` of the affine line, the image of
the orientation of the zero section `s` under `Rp_!` and the counit of `Rs_! ⊣ Rs^!`, read
through a composition isomorphism `α : R(s ≫ p)_! ≅ Rs_! ⋙ Rp_!`. -/
noncomputable def affineLineFundamentalClass
    (α : R(𝔸(ULift.{u} (Fin 1); Y).zeroLocusSubschemeι
        {AffineSpace.coord Y (ULift.up 0)} ≫ (𝔸(ULift.{u} (Fin 1); Y) ↘ Y))_![ModuleCat.{u + 1} Λ] ≅
      R(𝔸(ULift.{u} (Fin 1); Y).zeroLocusSubschemeι
        {AffineSpace.coord Y (ULift.up 0)})_![ModuleCat.{u + 1} Λ] ⋙
        R(𝔸(ULift.{u} (Fin 1); Y) ↘ Y)_![ModuleCat.{u + 1} Λ]) :
    (R(𝔸(ULift.{u} (Fin 1); Y).zeroLocusSubschemeι
        {AffineSpace.coord Y (ULift.up 0)} ≫
          (𝔸(ULift.{u} (Fin 1); Y) ↘ Y))_![ModuleCat.{u + 1} Λ]).obj
        (constantComplex Λ _) ⟶
      (R(𝔸(ULift.{u} (Fin 1); Y) ↘ Y)_![ModuleCat.{u + 1} Λ]).obj
        ((tateObject Λ 𝔸(ULift.{u} (Fin 1); Y) 1)⟦(2 : ℤ)⟧) :=
  α.hom.app _ ≫ (R(𝔸(ULift.{u} (Fin 1); Y) ↘ Y)_![ModuleCat.{u + 1} Λ]).map
    ((R(𝔸(ULift.{u} (Fin 1); Y).zeroLocusSubschemeι
        {AffineSpace.coord Y (ULift.up 0)})_![ModuleCat.{u + 1} Λ]).map
        (affineLineOrientation Λ Y) ≫
      (rightDerivedUpperShriekAdjunction Λ
        (𝔸(ULift.{u} (Fin 1); Y).zeroLocusSubschemeι
        {AffineSpace.coord Y (ULift.up 0)})).counit.app
          ((tateObject Λ 𝔸(ULift.{u} (Fin 1); Y) 1)⟦(2 : ℤ)⟧))

/-- Blueprint `proposition-transitivity-trace-map--1`: Trace normalization and transitivity

**The trace of the fundamental class is invertible.** For `Y` separated and locally
of finite type over a field and every purity isomorphism
`γ_{p,Λ} : Lp^* Λ(1)[2] ≅ Rp^! Λ` of the affine line `p : 𝔸¹_Y ⟶ Y`, the composite
`Tr^sm_{p,Λ} ∘ cl ∘ ψ : Λ_Y ⟶ Λ_Y` is an isomorphism. Writing `u = γ ∘ ι⁻¹ : Λ(1)[2] ≅ Rp^! Λ`,
the composite is the adjoint, for the composite adjunction `Rs_! ⋙ Rp_! ⊣ Rp^! ⋙ Rs^!`, of the
isomorphism `Rs^!(u) ∘ pur_s : Λ_{V(t)} ≅ Rs^! Rp^! Λ` (the orientation `pur_s` is an
isomorphism, `AlgebraicGeometry.Etale.isIso_affineLineOrientation`):

```
Λ_Y ──ψ──▶ R(s ≫ p)_! Λ ──α──▶ Rp_! Rs_! Λ ──Rp_! Rs_!(Rs^!(u) ∘ pur_s)──▶ Rp_! Rs_! Rs^! Rp^! Λ
                                                                                │ counit
                                                                                ▼
                                                                               Λ_Y
```

and the counit of the composite adjunction is an isomorphism because `s ≫ p : V(t) ⟶ Y` is an
isomorphism (`AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekAdjunction_counit_of_isIso`),
through `α : R(s ≫ p)_! ≅ Rs_! ⋙ Rp_!`. -/
theorem isIso_affineLineFundamentalClass_comp_smoothPurityTrace [HasKummerClass.IsNormalized Λ]
    {k : Type u} [Field k] (aY : Y ⟶ Spec (.of k)) [IsSeparated aY] [LocallyOfFiniteType aY]
    (α : R(𝔸(ULift.{u} (Fin 1); Y).zeroLocusSubschemeι
        {AffineSpace.coord Y (ULift.up 0)} ≫ (𝔸(ULift.{u} (Fin 1); Y) ↘ Y))_![ModuleCat.{u + 1} Λ] ≅
      R(𝔸(ULift.{u} (Fin 1); Y).zeroLocusSubschemeι
        {AffineSpace.coord Y (ULift.up 0)})_![ModuleCat.{u + 1} Λ] ⋙
        R(𝔸(ULift.{u} (Fin 1); Y) ↘ Y)_![ModuleCat.{u + 1} Λ])
    (ψ : constantComplex Λ Y ≅
      (R(𝔸(ULift.{u} (Fin 1); Y).zeroLocusSubschemeι
        {AffineSpace.coord Y (ULift.up 0)} ≫
          (𝔸(ULift.{u} (Fin 1); Y) ↘ Y))_![ModuleCat.{u + 1} Λ]).obj
        (constantComplex Λ _))
    (γ : (twistShift Λ 𝔸(ULift.{u} (Fin 1); Y) ((1 : ℕ) : ℤ)).obj
        ((L((𝔸(ULift.{u} (Fin 1); Y) ↘ Y)^*[ModuleCat.{u + 1} Λ])).obj
          (constantComplex Λ Y)) ≅
      (R(𝔸(ULift.{u} (Fin 1); Y) ↘ Y)^![Λ]).obj (constantComplex Λ Y)) :
    IsIso (ψ.hom ≫ affineLineFundamentalClass Λ Y α ≫
      (R(𝔸(ULift.{u} (Fin 1); Y) ↘ Y)_![ModuleCat.{u + 1} Λ]).map
        (affineLineTwistShiftIso Λ Y).inv ≫
      smoothPurityTrace Λ ((1 : ℕ) : ℤ) _ γ) := by
  have := isIso_affineLineOrientation Λ Y aY
  have : IsIso (𝔸(ULift.{u} (Fin 1); Y).zeroLocusSubschemeι
      {AffineSpace.coord Y (ULift.up 0)} ≫ (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)) :=
    inferInstanceAs (IsIso (AffineSpace.zeroSectionIsoZeroLocusSubscheme (ULift.{u} (Fin 1)) Y
      (s := {AffineSpace.coord Y (ULift.up 0)}) Set.range_unique).inv)
  have hb := isIso_rightDerivedUpperShriekAdjunction_counit_of_isIso Λ
    (𝔸(ULift.{u} (Fin 1); Y).zeroLocusSubschemeι
      {AffineSpace.coord Y (ULift.up 0)} ≫ (𝔸(ULift.{u} (Fin 1); Y) ↘ Y))
  set as := rightDerivedUpperShriekAdjunction Λ
    (𝔸(ULift.{u} (Fin 1); Y).zeroLocusSubschemeι {AffineSpace.coord Y (ULift.up 0)})
  set ap := rightDerivedUpperShriekAdjunction Λ
    (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)
  set b := rightDerivedUpperShriekAdjunction Λ
    (𝔸(ULift.{u} (Fin 1); Y).zeroLocusSubschemeι
      {AffineSpace.coord Y (ULift.up 0)} ≫ (𝔸(ULift.{u} (Fin 1); Y) ↘ Y))
  have : IsIso (as.comp ap).counit := (as.comp ap).isIso_counit_of_iso
    (Functor.isoWhiskerRight ((as.comp ap).rightAdjointUniq (b.ofNatIsoLeft α)) _ ≪≫
      Functor.isoWhiskerLeft _ α.symm ≪≫ asIso b.counit)
  have key : affineLineFundamentalClass Λ Y α ≫
      (R(𝔸(ULift.{u} (Fin 1); Y) ↘ Y)_![ModuleCat.{u + 1} Λ]).map
        (affineLineTwistShiftIso Λ Y).inv ≫ smoothPurityTrace Λ ((1 : ℕ) : ℤ) _ γ =
      α.hom.app _ ≫ (R(𝔸(ULift.{u} (Fin 1); Y).zeroLocusSubschemeι
        {AffineSpace.coord Y (ULift.up 0)})_![ModuleCat.{u + 1} Λ] ⋙
          R(𝔸(ULift.{u} (Fin 1); Y) ↘ Y)_![ModuleCat.{u + 1} Λ]).map
        (affineLineOrientation Λ Y ≫ (R(𝔸(ULift.{u} (Fin 1); Y).zeroLocusSubschemeι
          {AffineSpace.coord Y (ULift.up 0)})^![Λ]).map
            ((affineLineTwistShiftIso Λ Y).inv ≫ γ.hom)) ≫
        (as.comp ap).counit.app _ := by
    have h := congrArg (R(𝔸(ULift.{u} (Fin 1); Y) ↘ Y)_![ModuleCat.{u + 1} Λ]).map
      (as.counit.naturality ((affineLineTwistShiftIso Λ Y).inv ≫ γ.hom))
    simp only [Functor.comp_map, Functor.id_map, Functor.map_comp, Category.assoc] at h
    simp only [affineLineFundamentalClass, smoothPurityTrace, Adjunction.comp_counit_app,
      Functor.comp_map, Functor.map_comp, Category.assoc, reassoc_of% h]
    rfl
  rw [key]
  infer_instance

/-- Blueprint `proposition-transitivity-trace-map--1`: Trace normalization and transitivity

**Normalization on the affine line.** Over a separably closed field `k`: for every
composition isomorphism `α` and identification `ψ : Λ_k ≅ R(s ≫ p)_! Λ_{V(t)}` there is a
purity isomorphism `γ_{p,Λ} : Lp^* Λ(1)[2] ≅ Rp^! Λ` of the affine line `p : 𝔸¹_k ⟶ Spec k`
with `Tr^sm_{p,Λ} ∘ cl ∘ ψ = 1`. This `γ` is not the canonical one of the blueprint (normalized
on the projective line): `cl` is built from the Kummer boundary `∂κ(t)`, which forgets supports
to `-c₁(𝒪(V(t)))` (blueprint `lemma-cycle-class-cartier-divisor` (b)), so the canonical `γ` gives
`Tr^sm_{p,Λ} ∘ cl ∘ ψ = -1`, and `(-1)^d` on the ordered fundamental class of `𝔸^d`. -/
theorem exists_affineLineFundamentalClass_comp_smoothPurityTrace {k : Type u} [Field k]
    [IsSepClosed k] [HasKummerClass.IsNormalized Λ]
    [HasInvertibleExponent Λ (Spec (.of k))]
    [HasCompactification (𝔸(ULift.{u} (Fin 1); Spec (.of k)).zeroLocusSubschemeι
      {AffineSpace.coord (Spec (.of k)) (ULift.up 0)} ≫
        (𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k)))]
    (α : R(𝔸(ULift.{u} (Fin 1); Spec (.of k)).zeroLocusSubschemeι
        {AffineSpace.coord (Spec (.of k)) (ULift.up 0)} ≫
          (𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k)))_![ModuleCat.{u + 1} Λ] ≅
      R(𝔸(ULift.{u} (Fin 1); Spec (.of k)).zeroLocusSubschemeι
        {AffineSpace.coord (Spec (.of k)) (ULift.up 0)})_![ModuleCat.{u + 1} Λ] ⋙
        R(𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k))_![ModuleCat.{u + 1} Λ])
    (ψ : constantComplex Λ (Spec (.of k)) ≅
      (R(𝔸(ULift.{u} (Fin 1); Spec (.of k)).zeroLocusSubschemeι
        {AffineSpace.coord (Spec (.of k)) (ULift.up 0)} ≫
          (𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k)))_![ModuleCat.{u + 1} Λ]).obj
        (constantComplex Λ _)) :
    ∃ γ : (twistShift Λ 𝔸(ULift.{u} (Fin 1); Spec (.of k)) ((1 : ℕ) : ℤ)).obj
        ((L((𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k))^*[ModuleCat.{u + 1} Λ])).obj
          (constantComplex Λ (Spec (.of k)))) ≅
      (R(𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k))^![Λ]).obj
        (constantComplex Λ (Spec (.of k))),
      ψ.hom ≫ affineLineFundamentalClass Λ (Spec (.of k)) α ≫
        (R(𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k))_![ModuleCat.{u + 1} Λ]).map
          (affineLineTwistShiftIso Λ (Spec (.of k))).inv ≫
        smoothPurityTrace Λ ((1 : ℕ) : ℤ) _ γ = 𝟙 _ := by
  have : SmoothOfRelativeDimension 1 (𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k)) := by
    have := AffineSpace.smoothOfRelativeDimension_over (ULift.{u} (Fin 1)) (Spec (.of k))
    rwa [show Nat.card (ULift.{u} (Fin 1)) = 1 by simp] at this
  have : HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin 1); Spec (.of k)) :=
    .of_hom (𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k))
  obtain ⟨θ⟩ := nonempty_iso_dualizingComplex_twistShift Λ (d := 1)
    (𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k)) (𝟙 _)
  let γ₀ : (twistShift Λ 𝔸(ULift.{u} (Fin 1); Spec (.of k)) ((1 : ℕ) : ℤ)).obj
        ((L((𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k))^*[ModuleCat.{u + 1} Λ])).obj
          (constantComplex Λ (Spec (.of k)))) ≅
      (R(𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k))^![Λ]).obj
        (constantComplex Λ (Spec (.of k))) :=
    (twistShift Λ _ _).mapIso
      (leftDerivedUpperStarConstantComplexIso Λ (𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k)))
      ≪≫ θ.symm
  have hu :=
    isIso_affineLineFundamentalClass_comp_smoothPurityTrace Λ (Spec (.of k)) (𝟙 _) α ψ γ₀
  refine ⟨γ₀ ≪≫
    (R(𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k))^![Λ]).mapIso
      (asIso (ψ.hom ≫ affineLineFundamentalClass Λ (Spec (.of k)) α ≫
        (R(𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k))_![ModuleCat.{u + 1} Λ]).map
          (affineLineTwistShiftIso Λ (Spec (.of k))).inv ≫
          smoothPurityTrace Λ ((1 : ℕ) : ℤ) _ γ₀)).symm, ?_⟩
  rw [smoothPurityTrace, Iso.trans_hom, Functor.map_comp, Category.assoc, Functor.mapIso_hom,
    (rightDerivedUpperShriekAdjunction Λ _).counit_naturality]
  simp only [smoothPurityTrace, Iso.symm_hom, asIso_inv] at hu ⊢
  simp only [← Category.assoc] at hu ⊢
  exact IsIso.hom_inv_id _

end Etale

end AlgebraicGeometry
