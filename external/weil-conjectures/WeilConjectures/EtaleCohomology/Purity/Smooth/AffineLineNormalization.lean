/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange
public import WeilConjectures.Mathlib.CategoryTheory.Shift.ShiftSequence
public import WeilConjectures.SixFunctors.Etale.Derived.Triangulated

/-!
# The rank-one normalisation from the cohomology of `𝔸¹` and `𝔾ₘ`

Let `p : 𝔸¹_B ⟶ B` be the projection, `s : V(t) ⟶ 𝔸¹_B` the zero section (cut out by the
coordinate `t`) and `j : 𝔾_{m,B} ⟶ 𝔸¹_B` its open complement. The proof of `sk-prop-a1` applies
`Rp_*` to the localization triangle `Rs_! Rs^! Λ(1) ⟶ Λ(1) ⟶ Rj_* Lj^* Λ(1) ⟶ [1]` and reads off
the long exact sequence of cohomology sheaves with the computations of `sk-prop-a1-kummer`:
`Rp_* Λ(1)` sits in degree zero, `p^*` identifies it with `R⁰π_* Λ(1)`, `R¹π_* Λ(1)` is free
on the Kummer class `κ(t)` and `R^mπ_* Λ(1) = 0` for `m ≥ 2`. Hence `Rs^! Λ(1)[2]` sits in degree
zero, and the boundary `∂κ(t)` generates it: the adjoint `Λ_{V(t)} ⟶ Rs^! Λ(1)[2]` of the Kummer
boundary is an isomorphism.

This file proves that implication for an arbitrary rank-one datum
(`AlgebraicGeometry.Etale.isIso_supportedClassMap_kummerBoundary_coord_of_affineLine`); the
inputs are verified for the concrete Kummer classes in
`WeilConjectures.EtaleCohomology.TateTwist.AffineLine`.

## Main definitions

- `AlgebraicGeometry.Etale.kummerClassAdjoint`: `Λ_U ⟶ (Rj_* Lj^* Λ_U(1))[1]`, adjoint to `κ(f)`.
- `AlgebraicGeometry.Etale.kummerClassAffineLineDirectImage`: `κ(t)` as a section
  `Λ_B ⟶ (Rπ_* Λ(1))[1]`.

## Main statements

- `DerivedCategory.isIso_shiftedHomComp_of_distTriang`: the homological algebra of the argument.
- `AlgebraicGeometry.Etale.isIso_supportedClassMap_kummerBoundary_coord_of_affineLine`
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor

namespace DerivedCategory

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

/-- Let `A ⟶ P ⟶ Q ⟶ A[1]` be a distinguished triangle in `D(C)` and `κ : E ⟶ Q[1]`, where `E`
and `P` have cohomology only in degree `0`, `Q` only in degrees `0` and `1`, `H⁰(P) ⟶ H⁰(Q)` is
an isomorphism and `κ` induces an isomorphism `H⁰(E) ≅ H¹(Q)`. Then the composite
`E ⟶ Q[1] ⟶ A[2]` is an isomorphism: by the long exact sequence, `A` has cohomology only in
degree `2`, and the boundary `H¹(Q) ⟶ H²(A)` is an isomorphism. -/
theorem isIso_shiftedHomComp_of_distTriang (T : Triangle (DerivedCategory C))
    (hT : T ∈ distTriang _) {E : DerivedCategory C} (κ : E ⟶ T.obj₃⟦(1 : ℤ)⟧)
    (hE : ∀ n : ℤ, n ≠ 0 → IsZero ((homologyFunctor C n).obj E))
    (hP : ∀ n : ℤ, n ≠ 0 → IsZero ((homologyFunctor C n).obj T.obj₂))
    (h₀ : IsIso ((homologyFunctor C 0).map T.mor₂))
    (hQ : ∀ n : ℤ, n ≠ 0 → n ≠ 1 → IsZero ((homologyFunctor C n).obj T.obj₃))
    (hκ : IsIso ((homologyFunctor C 0).shiftMap κ 0 1 (by simp))) :
    IsIso (ShiftedHom.comp κ T.mor₃ (by norm_num : (1 : ℤ) + 1 = 2)) := by
  -- `H^n(mor₂)` is a monomorphism for every `n`
  have hmono : ∀ n : ℤ, Mono ((homologyFunctor C n).map T.mor₂) := fun n ↦ by
    by_cases hn : n = 0
    · subst hn; infer_instance
    · exact ⟨fun _ _ _ ↦ (hP n hn).eq_of_tgt _ _⟩
  have hepi : ∀ n : ℤ, n ≠ 1 → Epi ((homologyFunctor C n).map T.mor₂) := fun n hn ↦ by
    by_cases hn0 : n = 0
    · subst hn0; infer_instance
    · exact ⟨fun _ _ _ ↦ (hQ n hn0 hn).eq_of_src _ _⟩
  -- the supported term has cohomology only in degree `2`
  have hA : ∀ n : ℤ, n ≠ 2 → IsZero ((homologyFunctor C n).obj T.obj₁) := fun n hn ↦ by
    have h₁ : (homologyFunctor C n).map T.mor₁ = 0 :=
      (HomologySequence.mono_homologyMap_mor₂_iff T hT n).1 (hmono n)
    have h₂ : Mono ((homologyFunctor C n).map T.mor₁) :=
      (HomologySequence.mono_homologyMap_mor₁_iff T hT (n - 1) n (by lia)).2
        ((HomologySequence.epi_homologyMap_mor₂_iff T hT (n - 1) n (by lia)).1
          (hepi (n - 1) (by lia)))
    rw [h₁] at h₂
    exact IsZero.of_mono_zero _ ((homologyFunctor C n).obj T.obj₂)
  -- the boundary `H¹(Q) ⟶ H²(A)` is an isomorphism
  have hδ : IsIso (HomologySequence.δ T 1 2) := by
    have hm : Mono (HomologySequence.δ T 1 2) :=
      (HomologySequence.exact₃ T hT 1 2).mono_g ((hP 1 one_ne_zero).eq_of_src _ _)
    have he : Epi (HomologySequence.δ T 1 2) :=
      (HomologySequence.exact₁ T hT 1 2).epi_f ((hP 2 two_ne_zero).eq_of_tgt _ _)
    exact isIso_of_mono_of_epi _
  rw [isIso_iff]
  intro n
  by_cases hn : n = 0
  · subst hn
    have h := (homologyFunctor C 0).shiftMap_shiftedHomComp κ T.mor₃
      (by norm_num : (1 : ℤ) + 1 = 2) 0 1 2 (by norm_num) (by norm_num)
    have : IsIso ((homologyFunctor C 0).shiftMap
        (ShiftedHom.comp κ T.mor₃ (by norm_num : (1 : ℤ) + 1 = 2)) 0 2 (by norm_num)) := by
      rw [h]
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ hκ hδ
    rw [Functor.shiftMap] at this
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _
      (((homologyFunctor C 0).shiftIso (2 : ℤ) 0 2 (by norm_num)).hom.app T.obj₁) _ this
  · refine ⟨0, (hE n hn).eq_of_src _ _, ?_⟩
    refine IsZero.eq_of_src ?_ _ _
    exact (hA (2 + n) (by lia)).of_iso (((homologyFunctor C 0).shiftIso 2 n (2 + n) rfl).app _)

end DerivedCategory

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

section Abstract

variable {X Z B : Scheme.{u}}

/-- A class with supports is recovered from its adjoint (`supportedClassMap`) by applying
`Ri_!` and precomposing with the unit `Λ_X ⟶ Ri_! Λ_Z`. -/
lemma eq_comp_rightDerivedLowerShriek_map_supportedClassMap (i : Z ⟶ X) [IsClosedImmersion i]
    {L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (γ : constantComplex Λ X ⟶
      (R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj L)) :
    γ = (((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
          (HasCompactification.compactification i).g).comp
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
          (HasCompactification.compactification i).i)).unit.app (constantComplex Λ X) ≫
        (R(((HasCompactification.compactification i).i)_*[ModuleCat.{u + 1} Λ]) ⋙
          R(((HasCompactification.compactification i).g)_*[ModuleCat.{u + 1} Λ])).map
            (compactificationConstantComplexIso Λ i).hom ≫
        inv ((rightDerivedLowerShriekToLowerStarComp (ModuleCat.{u + 1} Λ) i).app
          (constantComplex Λ Z))) ≫
      (R(i)_![ModuleCat.{u + 1} Λ]).map (supportedClassMap Λ i γ) := by
  let fs := rightDerivedLowerShriekToLowerStarComp (ModuleCat.{u + 1} Λ) i
  rw [← cancel_mono (fs.app ((R(i)^![Λ]).obj L)), Category.assoc,
    fs.naturality, Category.assoc, Category.assoc, IsIso.inv_hom_id_assoc, ← Functor.map_comp,
    supportedClassMap, Iso.hom_inv_id_assoc, rightDerivedLowerShriekTranspose,
    ← Adjunction.homEquiv_unit, Equiv.apply_symm_apply]

omit [Finite Λ] in
/-- For a closed immersion `i : Z ⟶ X` and `p : X ⟶ B` with `i ≫ p` an isomorphism, the
derived pullback along `p` followed by the pullbacks along the chosen compactification of `i` is
an equivalence: it is the derived pullback along the isomorphism `i ≫ p`. -/
lemma isEquivalence_leftDerivedUpperStar_comp_compactification (i : Z ⟶ X) [IsClosedImmersion i]
    (p : X ⟶ B) [IsIso (i ≫ p)] :
    (L((p)^*[ModuleCat.{u + 1} Λ]) ⋙
      (L(((HasCompactification.compactification i).g)^*[ModuleCat.{u + 1} Λ]) ⋙
        L(((HasCompactification.compactification i).i)^*[ModuleCat.{u + 1} Λ]))).IsEquivalence := by
  let c := HasCompactification.compactification i
  have : IsIso ((c.i ≫ c.g) ≫ p) := by rw [← c.comm]; infer_instance
  exact Functor.isEquivalence_of_iso
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) (c.i ≫ c.g) p ≪≫
      Functor.isoWhiskerLeft _ (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) c.i c.g))

omit [Finite Λ] in
/-- For a closed immersion `i : Z ⟶ X` and `p : X ⟶ B` with `i ≫ p` an isomorphism,
`Rp_* ∘ Ri_!` reflects isomorphisms. -/
lemma isIso_of_isIso_rightDerivedLowerStar_map_rightDerivedLowerShriek_map (i : Z ⟶ X)
    [IsClosedImmersion i] (p : X ⟶ B) [IsIso (i ≫ p)]
    {M N : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (φ : M ⟶ N)
    (h : IsIso ((R((p)_*[ModuleCat.{u + 1} Λ])).map ((R(i)_![ModuleCat.{u + 1} Λ]).map φ))) :
    IsIso φ := by
  let c := HasCompactification.compactification i
  let adj := (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).comp
    ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) c.g).comp
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) c.i))
  have := isEquivalence_leftDerivedUpperStar_comp_compactification Λ i p
  have := adj.isEquivalence_right_of_isEquivalence_left
  let fs := rightDerivedLowerShriekToLowerStarComp (ModuleCat.{u + 1} Λ) i
  have hφ : (R(((HasCompactification.compactification i).i)_*[ModuleCat.{u + 1} Λ]) ⋙
      R(((HasCompactification.compactification i).g)_*[ModuleCat.{u + 1} Λ])).map φ =
        inv (fs.app M) ≫ (R(i)_![ModuleCat.{u + 1} Λ]).map φ ≫ fs.app N := by
    rw [fs.naturality, IsIso.inv_hom_id_assoc]
  have : IsIso (((R(((HasCompactification.compactification i).i)_*[ModuleCat.{u + 1} Λ]) ⋙
      R(((HasCompactification.compactification i).g)_*[ModuleCat.{u + 1} Λ])) ⋙
        R((p)_*[ModuleCat.{u + 1} Λ])).map φ) := by
    rw [Functor.comp_map, hφ, Functor.map_comp, Functor.map_comp]
    infer_instance
  exact isIso_of_reflects_iso φ ((R(((HasCompactification.compactification i).i)_*[
    ModuleCat.{u + 1} Λ]) ⋙ R(((HasCompactification.compactification i).g)_*[
      ModuleCat.{u + 1} Λ])) ⋙ R((p)_*[ModuleCat.{u + 1} Λ]))

omit [Finite Λ] in
/-- For a closed immersion `i : Z ⟶ X` and `p : X ⟶ B` with `i ≫ p` an isomorphism, the
composite of the unit `Λ_B ⟶ Rp_* Λ_X` and of `Rp_*` of the unit `Λ_X ⟶ Ri_! Λ_Z` is an
isomorphism. -/
lemma isIso_unit_comp_rightDerivedLowerStar_map_unit (i : Z ⟶ X) [IsClosedImmersion i]
    (p : X ⟶ B) [IsIso (i ≫ p)] :
    IsIso ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).unit.app
        (constantComplex Λ B) ≫
      (R((p)_*[ModuleCat.{u + 1} Λ])).map ((leftDerivedUpperStarConstantComplexIso Λ p).hom ≫
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
          (HasCompactification.compactification i).g).comp
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
          (HasCompactification.compactification i).i)).unit.app (constantComplex Λ X) ≫
        (R(((HasCompactification.compactification i).i)_*[ModuleCat.{u + 1} Λ]) ⋙
          R(((HasCompactification.compactification i).g)_*[ModuleCat.{u + 1} Λ])).map
            (compactificationConstantComplexIso Λ i).hom ≫
        inv ((rightDerivedLowerShriekToLowerStarComp (ModuleCat.{u + 1} Λ) i).app
          (constantComplex Λ Z)))) := by
  let c := HasCompactification.compactification i
  let adj₂ := (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) c.g).comp
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) c.i)
  let adj := (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).comp adj₂
  have := isEquivalence_leftDerivedUpperStar_comp_compactification Λ i p
  have : IsIso adj.unit := adj.unit_isIso_of_L_fully_faithful
  have h : (leftDerivedUpperStarConstantComplexIso Λ p).hom ≫
      adj₂.unit.app (constantComplex Λ X) =
        adj₂.unit.app _ ≫ (R((c.i)_*[ModuleCat.{u + 1} Λ]) ⋙ R((c.g)_*[ModuleCat.{u + 1} Λ])).map
          ((L((c.g)^*[ModuleCat.{u + 1} Λ]) ⋙ L((c.i)^*[ModuleCat.{u + 1} Λ])).map
            (leftDerivedUpperStarConstantComplexIso Λ p).hom) :=
    adj₂.unit.naturality (leftDerivedUpperStarConstantComplexIso Λ p).hom
  rw [← Category.assoc (leftDerivedUpperStarConstantComplexIso Λ p).hom]
  erw [h]
  simp only [Functor.map_comp, ← Category.assoc]
  have : IsIso ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).unit.app
      (constantComplex Λ B) ≫ (R((p)_*[ModuleCat.{u + 1} Λ])).map (adj₂.unit.app
        ((L((p)^*[ModuleCat.{u + 1} Λ])).obj (constantComplex Λ B)))) := by
    have h2 : IsIso (adj.unit.app (constantComplex Λ B)) := inferInstance
    rwa [Adjunction.comp_unit_app] at h2
  infer_instance

end Abstract

section Kummer

variable [HasKummerClass Λ]

attribute [local instance] HasInvertibleExponent.opens

variable {U : Scheme.{u}} [HasInvertibleExponent Λ U]

/-- The adjoint `Λ_U ⟶ (Rj_* Lj^* Λ_U(1))[1]` of the Kummer class `κ(f) ∈ H¹(U_f, Λ(1))` of a
global function `f`, for the open immersion `j : U_f ⟶ U`. -/
noncomputable def kummerClassAdjoint (f : Γ(U, ⊤)) :
    constantComplex Λ U ⟶ ((R(((U.basicOpen f).ι)_*[ModuleCat.{u + 1} Λ])).obj
      ((L(((U.basicOpen f).ι)^*[ModuleCat.{u + 1} Λ])).obj (tateObject Λ U 1)))⟦(1 : ℤ)⟧ :=
  (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (U.basicOpen f).ι).unit.app _ ≫
    (R(((U.basicOpen f).ι)_*[ModuleCat.{u + 1} Λ])).map
      ((leftDerivedUpperStarConstantComplexIso Λ (U.basicOpen f).ι).hom ≫
        kummerClass Λ (U.basicOpenUnit f) ≫
          (leftDerivedUpperStarTateObjectIso (U.basicOpen f).ι 1).inv⟦(1 : ℤ)⟧') ≫
    ((R(((U.basicOpen f).ι)_*[ModuleCat.{u + 1} Λ])).commShiftIso (1 : ℤ)).hom.app _

/-- The Kummer boundary `∂κ(f)` is the composite, as shifted morphisms, of the adjoint of the
Kummer class (`AlgebraicGeometry.Etale.kummerClassAdjoint`) and of the boundary of the supported
localization triangle. -/
lemma kummerBoundary_eq_comp (f : Γ(U, ⊤)) :
    kummerBoundary Λ f = ShiftedHom.comp (kummerClassAdjoint Λ f)
      (supportedLocalizationBoundary Λ _ _
        (range_zeroLocusSubschemeι_singleton f) (tateObject Λ U 1)) (by norm_num) := by
  rw [kummerBoundary_eq]
  rfl

variable (B : Scheme.{u}) [HasInvertibleExponent Λ B]

/-- The Kummer class `κ(t)` of the coordinate of `𝔾_{m,B}`, as a section
`Λ_B ⟶ (Rπ_* Λ(1))[1]` of the direct image along `π : 𝔾_{m,B} ⟶ 𝔸¹_B ⟶ B`. -/
noncomputable def kummerClassAffineLineDirectImage :
    constantComplex Λ B ⟶ ((R((𝔸(ULift.{u} (Fin 1); B) ↘ B)_*[ModuleCat.{u + 1} Λ])).obj
      ((R(((𝔸(ULift.{u} (Fin 1); B).basicOpen (AffineSpace.coord B (ULift.up 0))).ι)_*[
          ModuleCat.{u + 1} Λ])).obj
        ((L(((𝔸(ULift.{u} (Fin 1); B).basicOpen (AffineSpace.coord B (ULift.up 0))).ι)^*[
          ModuleCat.{u + 1} Λ])).obj (tateObject Λ 𝔸(ULift.{u} (Fin 1); B) 1))))⟦(1 : ℤ)⟧ :=
  ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
      (𝔸(ULift.{u} (Fin 1); B) ↘ B)).unit.app (constantComplex Λ B) ≫
    (R((𝔸(ULift.{u} (Fin 1); B) ↘ B)_*[ModuleCat.{u + 1} Λ])).map
      (leftDerivedUpperStarConstantComplexIso Λ (𝔸(ULift.{u} (Fin 1); B) ↘ B)).hom) ≫
  ShiftedHom.map (kummerClassAdjoint Λ (AffineSpace.coord B (ULift.up 0)))
    (R((𝔸(ULift.{u} (Fin 1); B) ↘ B)_*[ModuleCat.{u + 1} Λ]))

/-- Blueprint `sk-prop-a1`: Rank-one orientation: the fundamental class of the zero section

*The proof from `sk-prop-a1-kummer`.* For a rank-one datum, suppose that, with
`p : 𝔸¹_B ⟶ B`, `j : 𝔾_{m,B} ⟶ 𝔸¹_B` and `π = p ∘ j`,

* `Rp_* Λ(1)` has cohomology only in degree `0` (`ha`);
* the restriction `R⁰p_* Λ(1) ⟶ R⁰π_* Λ(1)` is an isomorphism (`hb₀`);
* the Kummer class induces an isomorphism `Λ_B ≅ R¹π_* Λ(1)`, `1 ↦ κ(t)` (`hb₁`);
* `R^mπ_* Λ(1) = 0` for `m ≠ 0, 1` (`hc`).

Then the adjoint `Λ_{V(t)} ⟶ Rs^! Λ(1)[2]` of the Kummer boundary `∂κ(t)` is an isomorphism.
Indeed `Rp_*` of the localization triangle of `(s, j)` is a triangle
`Rp_* Rs_! Rs^! Λ(1) ⟶ Rp_* Λ(1) ⟶ Rπ_* Λ(1) ⟶ [1]`, in which `Rp_* Rs_! ≅ R(ps)_*` is an
equivalence as `ps` is an isomorphism, and `Rp_*` of `∂κ(t)` is `κ(t)` followed by the boundary
of this triangle; `DerivedCategory.isIso_shiftedHomComp_of_distTriang` concludes. -/
theorem isIso_supportedClassMap_kummerBoundary_coord_of_affineLine
    (ha : ∀ n : ℤ, n ≠ 0 → IsZero ((_root_.DerivedCategory.homologyFunctor _ n).obj
      ((R((𝔸(ULift.{u} (Fin 1); B) ↘ B)_*[ModuleCat.{u + 1} Λ])).obj
        (tateObject Λ 𝔸(ULift.{u} (Fin 1); B) 1))))
    (hb₀ : IsIso ((_root_.DerivedCategory.homologyFunctor _ 0).map
      ((R((𝔸(ULift.{u} (Fin 1); B) ↘ B)_*[ModuleCat.{u + 1} Λ])).map
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
          ((𝔸(ULift.{u} (Fin 1); B).basicOpen (AffineSpace.coord B (ULift.up 0))).ι)).unit.app
            (tateObject Λ 𝔸(ULift.{u} (Fin 1); B) 1)))))
    (hb₁ : IsIso ((_root_.DerivedCategory.homologyFunctor _ 0).shiftMap
      (kummerClassAffineLineDirectImage Λ B) 0 1 (by norm_num)))
    (hc : ∀ n : ℤ, n ≠ 0 → n ≠ 1 → IsZero ((_root_.DerivedCategory.homologyFunctor _ n).obj
      ((R((𝔸(ULift.{u} (Fin 1); B) ↘ B)_*[ModuleCat.{u + 1} Λ])).obj
        ((R(((𝔸(ULift.{u} (Fin 1); B).basicOpen (AffineSpace.coord B (ULift.up 0))).ι)_*[
            ModuleCat.{u + 1} Λ])).obj
          ((L(((𝔸(ULift.{u} (Fin 1); B).basicOpen (AffineSpace.coord B (ULift.up 0))).ι)^*[
            ModuleCat.{u + 1} Λ])).obj (tateObject Λ 𝔸(ULift.{u} (Fin 1); B) 1)))))) :
    IsIso (supportedClassMap Λ (𝔸(ULift.{u} (Fin 1); B).zeroLocusSubschemeι
        {AffineSpace.coord B (ULift.up 0)})
      (shiftSupportedClass Λ _ 2
        (kummerBoundary Λ (AffineSpace.coord B (ULift.up 0))))) := by
  let t := AffineSpace.coord B (ULift.up.{u} (0 : Fin 1))
  let X := 𝔸(ULift.{u} (Fin 1); B)
  let p := X ↘ B
  let i := X.zeroLocusSubschemeι {t}
  let Rp := R((p)_*[ModuleCat.{u + 1} Λ])
  have : IsIso (i ≫ p) :=
    inferInstanceAs (IsIso (AffineSpace.zeroSectionIsoZeroLocusSubscheme (ULift.{u} (Fin 1)) B
      (s := {t}) Set.range_unique).inv)
  -- the localization triangle of `(V(t), 𝔾_m)`, pushed forward to `B`
  let T₁ := supportedLocalizationTriangle Λ i (X.basicOpen t).ι
    (tateObject Λ X 1) (supportedLocalizationBoundary Λ _ _
      (range_zeroLocusSubschemeι_singleton t) (tateObject Λ X 1))
  have hT₁ : T₁ ∈ distTriang _ := supportedLocalizationTriangle_mem_distTriang _ _ _ _ _
  let T₂ := Rp.mapTriangle.obj T₁
  have hT₂ : T₂ ∈ distTriang _ := Rp.map_distinguished _ hT₁
  have hE : ∀ n : ℤ, n ≠ 0 → IsZero ((_root_.DerivedCategory.homologyFunctor _ n).obj
      (constantComplex Λ B)) := fun n hn ↦
    (HomologicalComplex.isZero_single_obj_homology _ _ _ _ hn).of_iso
      ((_root_.DerivedCategory.homologyFunctor _ n).mapIso
        (constantComplexIsoSingleFunctor Λ B ≪≫
          (_root_.DerivedCategory.singleFunctorIsoCompQ _ 0).app _) ≪≫
        (_root_.DerivedCategory.homologyFunctorFactors _ n).app _)
  have hmain := _root_.DerivedCategory.isIso_shiftedHomComp_of_distTriang T₂ hT₂
    (kummerClassAffineLineDirectImage Λ B) hE ha hb₀ hc hb₁
  -- the class `∂κ(t)` pushed forward to `B` is the composite of `κ(t)` and the boundary
  let u := (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).unit.app
      (constantComplex Λ B) ≫ Rp.map (leftDerivedUpperStarConstantComplexIso Λ p).hom
  have hmain' : IsIso (ShiftedHom.comp (kummerClassAffineLineDirectImage Λ B)
      (ShiftedHom.map (supportedLocalizationBoundary Λ _ _
        (range_zeroLocusSubschemeι_singleton t) (tateObject Λ X 1)) Rp)
      (by norm_num : (1 : ℤ) + 1 = 2)) := hmain
  have hkey : u ≫ Rp.map (kummerBoundary Λ t) =
      ShiftedHom.comp (kummerClassAffineLineDirectImage Λ B)
        (ShiftedHom.map (supportedLocalizationBoundary Λ _ _
          (range_zeroLocusSubschemeι_singleton t) (tateObject Λ X 1)) Rp) (by norm_num) ≫
        (Rp.commShiftIso (2 : ℤ)).inv.app _ := by
    have h1 : Rp.map (kummerBoundary Λ t) = ShiftedHom.map (kummerBoundary Λ t) Rp ≫
        (Rp.commShiftIso (2 : ℤ)).inv.app _ := by
      simp [ShiftedHom.map]
    rw [h1, kummerBoundary_eq_comp, ShiftedHom.map_comp]
    simp only [ShiftedHom.comp, kummerClassAffineLineDirectImage, u, t, X, p, Rp,
      Category.assoc]
  -- the adjoint `φ` of `∂κ(t)`: `Rp_* Ri_! φ` is an isomorphism
  refine isIso_of_isIso_rightDerivedLowerStar_map_rightDerivedLowerShriek_map Λ i p _ ?_
  have hγ := eq_comp_rightDerivedLowerShriek_map_supportedClassMap Λ i
    (shiftSupportedClass Λ i 2 (kummerBoundary Λ t))
  have hu := isIso_unit_comp_rightDerivedLowerStar_map_unit Λ i p
  rw [Functor.map_comp Rp (leftDerivedUpperStarConstantComplexIso Λ p).hom,
    ← Category.assoc] at hu
  have h3 : IsIso (u ≫ Rp.map (shiftSupportedClass Λ i 2
      (kummerBoundary Λ t))) := by
    rw [shiftSupportedClass, Functor.map_comp, ← Category.assoc, hkey]
    infer_instance
  conv at h3 => rw [hγ, Functor.map_comp, ← Category.assoc]
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ hu h3

end Kummer

end Etale

end AlgebraicGeometry
