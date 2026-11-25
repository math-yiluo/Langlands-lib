/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Sections of formally unramified morphisms

A section `s : Y ⟶ Z` of a morphism `a : Z ⟶ Y` is the base change of the diagonal of `a` along
the graph `(𝟙, a ≫ s) : Z ⟶ Z ×_Y Z`. Hence the sections of a formally unramified morphism
locally of finite type are open immersions. Over an algebraically closed field `K`, a formally
unramified scheme `Z` locally of finite type is therefore the disjoint union of copies of
`Spec K` indexed by its `K`-points.

## Main statements

- `AlgebraicGeometry.isPullback_section_diagonal`: a section is a base change of the diagonal.
- `AlgebraicGeometry.FormallyUnramified.isOpenImmersion_of_comp_eq_id`: sections of formally
  unramified morphisms locally of finite type are open immersions.
- `AlgebraicGeometry.FormallyUnramified.isIso_sigmaDesc_of_isAlgClosed`: a formally unramified
  scheme locally of finite type over an algebraically closed field `K` is the disjoint union of
  copies of `Spec K` indexed by its `K`-points.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {Y Z : Scheme.{u}} (a : Z ⟶ Y)

/-- A section `s` of `a : Z ⟶ Y` is the base change of the diagonal `Δ_a : Z ⟶ Z ×_Y Z` along
the graph `(𝟙, a ≫ s) : Z ⟶ Z ×_Y Z`. -/
lemma isPullback_section_diagonal (s : Y ⟶ Z) (hs : s ≫ a = 𝟙 Y) :
    IsPullback s s (pullback.lift (𝟙 Z) (a ≫ s) (by simp [hs])) (pullback.diagonal a) := by
  have w : s ≫ pullback.lift (𝟙 Z) (a ≫ s) (by simp [hs]) = s ≫ pullback.diagonal a := by
    apply pullback.hom_ext <;> simp [reassoc_of% hs]
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk w (fun c ↦ c.fst ≫ a) ?_ ?_ ?_)
  · intro c
    have h₁ : c.fst = c.snd := by simpa using c.condition =≫ pullback.fst a a
    have h₂ : c.fst ≫ a ≫ s = c.snd := by simpa using c.condition =≫ pullback.snd a a
    rw [Category.assoc c.fst a s, h₂, h₁]
  · intro c
    have h₂ : c.fst ≫ a ≫ s = c.snd := by simpa using c.condition =≫ pullback.snd a a
    rw [Category.assoc c.fst a s, h₂]
  · intro c m hm _
    simp [← hm, hs]

namespace FormallyUnramified

/-- A section of a formally unramified morphism locally of finite type is an open immersion,
being a base change of the diagonal, which is an open immersion. -/
lemma isOpenImmersion_of_comp_eq_id [FormallyUnramified a] [LocallyOfFiniteType a]
    (s : Y ⟶ Z) (hs : s ≫ a = 𝟙 Y) : IsOpenImmersion s :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) (isPullback_section_diagonal a s hs).flip
    inferInstance

variable {K : Type u} [Field K] [IsAlgClosed K]

/-- Every point of a formally unramified scheme `Z` locally of finite type over an algebraically
closed field `K` lies on a section `Spec K ⟶ Z`: its residue field is a separable algebraic
extension of `K`, hence `K` itself. -/
lemma exists_comp_eq_id_of_isAlgClosed (a : Z ⟶ Spec (.of K)) [FormallyUnramified a]
    [LocallyOfFiniteType a] (z : Z) :
    ∃ s : Spec (.of K) ⟶ Z, s ≫ a = 𝟙 _ ∧ z ∈ Set.range s := by
  set φ := Spec.preimage (Z.fromSpecResidueField z ≫ a)
  set χ := Spec.preimage ((Spec (.of K)).fromSpecResidueField (a z))
  have hφ : φ = χ ≫ a.residueFieldMap z := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  have hχ : Function.Surjective χ.hom := by
    have h := Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField (.of K) (a z)
    rw [← Spec.map_comp, ← Spec.map_preimage ((Spec (.of K)).fromSpecResidueField (a z))] at h
    have hχ' : χ = _ := (Spec.map_injective h).symm
    rw [hχ']
    have : (a z).asIdeal.IsMaximal := by
      rw [Ideal.eq_bot_of_prime (a z).asIdeal]
      exact Ideal.bot_isMaximal
    exact (ConcreteCategory.bijective_of_isIso
      (Scheme.Spec.residueFieldIso (.of K) (a z)).inv).2.comp
      (Ideal.algebraMap_residueField_surjective _)
  have hint : φ.hom.IsIntegral := by
    let : Algebra ((Spec (.of K)).residueField (a z)) (Z.residueField z) :=
      (a.residueFieldMap z).hom.toAlgebra
    rw [hφ, CommRingCat.hom_comp]
    exact RingHom.IsIntegral.trans _ _ (RingHom.isIntegral_of_surjective _ hχ)
      (Algebra.IsSeparable.isIntegral _)
  let : Algebra K (Z.residueField z) := φ.hom.toAlgebra
  have : Algebra.IsIntegral K (Z.residueField z) := ⟨hint⟩
  let ψ : Z.residueField z →ₐ[K] K := IsAlgClosed.lift
  refine ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ Z.fromSpecResidueField z, ?_,
    ⟨IsLocalRing.closedPoint K, Z.fromSpecResidueField_apply z _⟩⟩
  rw [Category.assoc, ← Spec.map_preimage (Z.fromSpecResidueField z ≫ a), ← Spec.map_comp,
    ← Spec.map_id]
  congr 1
  ext c
  exact ψ.commutes c

omit [IsAlgClosed K] in
/-- Two sections `Spec K ⟶ Z` of a formally unramified morphism locally of finite type through
the same point are equal. -/
lemma eq_of_comp_eq_id_of_apply_eq (a : Z ⟶ Spec (.of K)) [FormallyUnramified a]
    [LocallyOfFiniteType a] {s t : Spec (.of K) ⟶ Z} (hs : s ≫ a = 𝟙 _) (ht : t ≫ a = 𝟙 _)
    {x y : Spec (.of K)} (h : s x = t y) : s = t := by
  have := isOpenImmersion_of_comp_eq_id a s hs
  have hsub : Set.range t ⊆ Set.range s := by
    rintro _ ⟨y', rfl⟩
    exact ⟨x, by rw [Subsingleton.elim y' y, h]⟩
  have he := IsOpenImmersion.lift_fac s t hsub
  have hid : IsOpenImmersion.lift s t hsub = 𝟙 _ :=
    calc IsOpenImmersion.lift s t hsub = IsOpenImmersion.lift s t hsub ≫ s ≫ a := by
          rw [hs, Category.comp_id]
      _ = t ≫ a := by rw [reassoc_of% he]
      _ = 𝟙 _ := ht
  rw [← he, hid, Category.id_comp]

/-- A formally unramified scheme `Z` locally of finite type over an algebraically closed field
`K` is the disjoint union of copies of `Spec K`: for a family `s` of sections `Spec K ⟶ Z` of
the structure morphism hitting every section exactly once, `∐ Spec K ⟶ Z` is an isomorphism. -/
theorem isIso_sigmaDesc_of_isAlgClosed (a : Z ⟶ Spec (.of K)) [FormallyUnramified a]
    [LocallyOfFiniteType a] {σ : Type u} (s : σ → (Spec (.of K) ⟶ Z))
    (hs : ∀ i, s i ≫ a = 𝟙 _) (hinj : Function.Injective s)
    (hsurj : ∀ t : Spec (.of K) ⟶ Z, t ≫ a = 𝟙 _ → ∃ i, s i = t) :
    IsIso (Sigma.desc s) := by
  have (i : σ) : IsOpenImmersion (s i) := isOpenImmersion_of_comp_eq_id a (s i) (hs i)
  have : IsOpenImmersion (Sigma.desc s) := by
    refine isOpenImmersion_sigmaDesc _ _ fun i j hij ↦ ?_
    rw [Function.onFun, Set.disjoint_left]
    rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
    exact hij (hinj (eq_of_comp_eq_id_of_apply_eq a (hs i) (hs j) hy.symm))
  refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ (eq_top_iff.2 fun z _ ↦ ?_)
  obtain ⟨t, ht, x, rfl⟩ := exists_comp_eq_id_of_isAlgClosed a z
  obtain ⟨i, rfl⟩ := hsurj t ht
  refine ⟨(Sigma.ι (fun _ : σ ↦ Spec (.of K)) i) x, ?_⟩
  rw [← Scheme.Hom.comp_apply, Sigma.ι_comp_desc]

end FormallyUnramified

end AlgebraicGeometry
