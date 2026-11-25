/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.ValuativeCriterion
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteRefinement.GeometricLifts
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.Mathlib.RingTheory.Etale.QuasiFinite

/-!
# Geometric fibres of an étale morphism under specialization

Let `u : U ⟶ T` be separated and étale, factored as an open immersion `j : U ⟶ Y` followed by a
separated `π : Y ⟶ T`. If `u` has at most `d + 1` geometric lifts and `y ∈ Y \ U` is a
specialization of a point of `U`, then every geometric point of `T` over `π y` has at most `d`
lifts along `u`.

This is the specialization step in the proof of Stacks Project Tag 09Z0. The specialization is
realised by a valuation ring `A` with algebraically closed fraction field `Ω`. Over `Spec A`,
the base change of `u` is a disjoint union of open subschemes mapping isomorphically onto opens
of `Spec A` (Stacks Project Tag 09Z9). Every lift of the closed point therefore extends to a
section, and the generic points of these sections are distinct lifts of the generic point. One
more lift of the generic point comes from `U ⊆ Y`, and it does not extend to a section because
`y ∉ U`.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.not_injective_lifts_of_specializes`: the bound on geometric
  lifts drops at specializations outside `U`.
-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

namespace AlgebraicGeometry

/-- **The bound on geometric lifts drops at a specialization outside `U`.** Let `u : U ⟶ T` be
separated and étale with at most `d + 1` geometric lifts, and let `u = j ≫ π` with `j : U ⟶ Y`
an open immersion and `π : Y ⟶ T` separated. If `y ∈ Y` is not in `U` but specializes a point
of `U`, then no separably closed point of `T` over `π y` has `d + 1` distinct lifts along `u`. -/
theorem Scheme.Hom.not_injective_lifts_of_specializes {U Y T : Scheme.{u}} (u : U ⟶ T)
    [Etale u] [IsSeparated u] (j : U ⟶ Y) [IsOpenImmersion j] (π : Y ⟶ T) [IsSeparated π]
    (hjπ : j ≫ π = u) {d : ℕ} (hd : u.HasAtMostGeometricLifts (d + 1)) {x₀ : U} {y : Y}
    (hx₀ : j x₀ ⤳ y) (hy : y ∉ Set.range j) {K : Type u} [Field K] [IsSepClosed K]
    (σ : Spec (.of K) ⟶ T) (hσ : σ (closedPoint K) = π y)
    (x : Fin (d + 1) → (Spec (.of K) ⟶ U)) (hx : ∀ i, x i ≫ u = σ) :
    ¬ Function.Injective x := by
  intro hinj
  obtain ⟨A, ρ, hρ, hηρ⟩ := Scheme.exists_valuationSubring_of_specializes hx₀
  let Ω := AlgebraicClosure (Y.residueField (j x₀))
  let η : Spec (.of Ω) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (algebraMap A Ω))
  let τ := ρ ≫ π
  -- the closed point of `Spec A` and the lifts over it
  have : IsSepClosed (ResidueField A) := isSepClosed_residueField_of_isSepClosed_fractionRing Ω
  let s₀ : Spec (.of (ResidueField A)) ⟶ Spec (.of A) :=
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))
  have hs₀ : s₀ (closedPoint (ResidueField A)) = closedPoint A :=
    IsLocalRing.comap_closedPoint (IsLocalRing.residue A)
  obtain ⟨y', hy'u, hy'inj⟩ := u.exists_injective_lifts_of_apply_eq σ (s₀ ≫ τ)
    (by rw [hσ]; simp only [τ, Scheme.Hom.comp_apply, hs₀, hρ]) x hx hinj
  -- the base change of `u` to `Spec A` is a disjoint union of opens of `Spec A`
  have : IsSepClosed (Spec (.of A)).functionField :=
    let : Algebra (CommRingCat.of A) (Spec (.of A)).functionField :=
      instAlgebraCarrierFunctionFieldSpec (CommRingCat.of A)
    have := functionField_isFractionRing_of_affine (CommRingCat.of A)
    let : Algebra (CommRingCat.of A) Ω := inferInstanceAs (Algebra A Ω)
    have : IsFractionRing (CommRingCat.of A) Ω := inferInstanceAs (IsFractionRing A Ω)
    have : IsAlgClosed (Spec (.of A)).functionField := IsAlgClosed.of_ringEquiv (k := Ω) _
      (IsLocalization.algEquiv (nonZeroDivisors (CommRingCat.of A)) Ω
        (Spec (.of A)).functionField).toRingEquiv
    inferInstance
  obtain ⟨ι, V, hdisj, hcov, hV⟩ := Etale.exists_opens_isOpenImmersion_of_isSepClosed_functionField
    (Scheme.isIntegrallyClosed_stalk_Spec A) (pullback.snd u τ)
  let G := {a : ι // IsIso ((V a).ι ≫ pullback.snd u τ)}
  let sec (a : G) : Spec (.of A) ⟶ pullback u τ :=
    have := a.2
    inv ((V a.1).ι ≫ pullback.snd u τ) ≫ (V a.1).ι
  have sec_snd (a : G) : sec a ≫ pullback.snd u τ = 𝟙 _ := by
    have := a.2
    simp [sec]
  have range_sec (a : G) (w) : sec a w ∈ V a.1 := by
    simp only [sec, Scheme.Hom.comp_apply]
    exact Subtype.prop _
  -- every lift of the closed point extends to a section
  have hlift (i : Fin (d + 1)) : ∃ a : G, pullback.lift (y' i) s₀ (hy'u i) = s₀ ≫ sec a := by
    let z := pullback.lift (y' i) s₀ (hy'u i)
    obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (hcov.ge (TopologicalSpace.Opens.mem_top (z (closedPoint (ResidueField A)))))
    have hmem : closedPoint A ∈ ((V a).ι ≫ pullback.snd u τ).opensRange := by
      refine ⟨⟨_, ha⟩, ?_⟩
      change (pullback.snd u τ) ((V a).ι ⟨_, ha⟩) = _
      rw [Scheme.Opens.ι_apply, ← Scheme.Hom.comp_apply, pullback.lift_snd, hs₀]
    have : IsIso ((V a).ι ≫ pullback.snd u τ) := by
      rw [isIso_iff_isOpenImmersion_and_surjective]
      refine ⟨inferInstance, ⟨fun w ↦ ?_⟩⟩
      have h' := IsLocalRing.closed_point_mem_iff.mp hmem
      exact (show w ∈ ((V a).ι ≫ pullback.snd u τ).opensRange by rw [h']; trivial)
    refine ⟨⟨a, this⟩, ?_⟩
    have hz : Set.range z ⊆ Set.range (V a).ι := by
      rintro _ ⟨w, rfl⟩
      rw [Subsingleton.elim w (closedPoint _), Scheme.Opens.range_ι]
      exact ha
    have hz' := IsOpenImmersion.lift_fac (V a).ι z hz
    have hz'' : IsOpenImmersion.lift (V a).ι z hz = s₀ ≫ inv ((V a).ι ≫ pullback.snd u τ) := by
      rw [IsIso.eq_comp_inv, ← Category.assoc, hz', pullback.lift_snd]
    exact hz'.symm.trans (by rw [hz'', Category.assoc])
  choose a ha using hlift
  -- the lifts of the generic point
  let g (i : Fin (d + 1)) : Spec (.of Ω) ⟶ U := η ≫ sec (a i) ≫ pullback.fst u τ
  have hg (i : Fin (d + 1)) : g i ≫ u = η ≫ τ := by
    simp only [g, Category.assoc, pullback.condition, reassoc_of% sec_snd]
  have hginj : Function.Injective g := by
    intro i₁ i₂ h
    have h' : η ≫ sec (a i₁) = η ≫ sec (a i₂) := by
      apply pullback.hom_ext
      · simpa only [Category.assoc] using h
      · simp only [Category.assoc, sec_snd]
    have : a i₁ = a i₂ := by
      by_contra hne
      have hne' : (a i₁).1 ≠ (a i₂).1 := fun e ↦ hne (Subtype.ext e)
      have w := closedPoint Ω
      have h₁ := range_sec (a i₁) (η w)
      have h₂ := range_sec (a i₂) (η w)
      rw [← Scheme.Hom.comp_apply, h', Scheme.Hom.comp_apply] at h₁
      have := (hdisj _ _ hne').le_bot ⟨h₁, h₂⟩
      simp at this
    apply hy'inj
    rw [← pullback.lift_fst (y' i₁) s₀ (hy'u i₁), ← pullback.lift_fst (y' i₂) s₀ (hy'u i₂), ha,
      ha, this]
  -- the lift of the generic point through `U ⊆ Y`
  have hδ : Set.range (η ≫ ρ) ⊆ Set.range j := by
    rintro _ ⟨w, rfl⟩
    rw [hηρ, Scheme.Hom.comp_apply]
    exact ⟨x₀, (Scheme.fromSpecResidueField_apply _ _).symm⟩
  let δ : Spec (.of Ω) ⟶ U := IsOpenImmersion.lift j (η ≫ ρ) hδ
  have hδu : δ ≫ u = η ≫ τ := by
    rw [← hjπ, ← Category.assoc, IsOpenImmersion.lift_fac, Category.assoc]
  have hδg (i : Fin (d + 1)) : δ ≠ g i := by
    intro e
    let S : ValuativeCommSq π :=
      { R := A, K := Ω, i₁ := η ≫ ρ, i₂ := τ, commSq := ⟨by simp [τ, η]⟩ }
    let l₁ : S.commSq.LiftStruct := ⟨ρ, rfl, rfl⟩
    let l₂ : S.commSq.LiftStruct :=
      ⟨sec (a i) ≫ pullback.fst u τ ≫ j, by
        change η ≫ sec (a i) ≫ pullback.fst u τ ≫ j = η ≫ ρ
        rw [← IsOpenImmersion.lift_fac j (η ≫ ρ) hδ]
        exact congr($e.symm ≫ j).symm.trans (by simp [g]) |>.symm, by
        change (sec (a i) ≫ pullback.fst u τ ≫ j) ≫ π = τ
        simp only [Category.assoc, hjπ, pullback.condition, reassoc_of% sec_snd]⟩
    have hl := congr_arg CommSq.LiftStruct.l
      (Subsingleton.elim (h := IsSeparated.valuativeCriterion π S) l₁ l₂)
    apply hy
    refine ⟨pullback.fst u τ (sec (a i) (closedPoint A)), ?_⟩
    change ρ (closedPoint A) = _ at hρ
    rw [← hρ, show ρ = _ from hl]
    change _ = (sec (a i) ≫ pullback.fst u τ ≫ j) _
    simp only [Scheme.Hom.comp_apply]
  refine hd Ω (η ≫ τ) (Fin.cons δ g) (Fin.cases hδu hg) ?_
  rw [Fin.cons_injective_iff]
  exact ⟨fun ⟨i, hi⟩ ↦ hδg i hi.symm, hginj⟩

end AlgebraicGeometry
