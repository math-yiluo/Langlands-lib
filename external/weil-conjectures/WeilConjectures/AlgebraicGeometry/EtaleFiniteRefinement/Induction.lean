/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteRefinement.FiniteBound
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteRefinement.Specialization
public import WeilConjectures.AlgebraicGeometry.Morphisms.QuasiFiniteFactorization
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Finite refinement of a surjective étale morphism: the induction on the degree

Let `u : U ⟶ T` be surjective, étale, separated and quasi-compact, with `T` quasi-compact and
quasi-separated. We show that there is a finite surjective `r : T' ⟶ T` which factors through
`u` Zariski locally on `T'` (`AlgebraicGeometry.Scheme.Hom.FactorsLocallyThrough`). This is the
integral form of Stacks Project Tag 09Z0, with finite in place of integral.

The proof is by induction on a bound `d` for the number of points of the geometric fibres of `u`
(`AlgebraicGeometry.Scheme.Hom.HasAtMostGeometricLifts`). If `d = 0`, then `T` is empty. In
general, Zariski's main theorem factors `u` as a dense quasi-compact open immersion `U ⊆ Y`
followed by a finite `π : Y ⟶ T`. The graph of `U ⊆ Y` is open and closed in `U ×_T Y`; let
`W` be its complement and `V ⊆ Y` the image of `W`. Then `V` contains `Y \ U`, and `W ⟶ V`
has at most `d - 1` geometric lifts: over `U` the diagonal point is missing, and over `Y \ U`
the bound drops by specialization
(`AlgebraicGeometry.Scheme.Hom.not_injective_lifts_of_specializes`). By induction, a finite
`T₁ ⟶ V` refines `W ⟶ V`. It extends to a finite `Z ⟶ Y` with `T₁ ⊆ Z` open (Zariski's main
theorem again), in which `T₁` is open and closed over `V`. The closed subscheme of `Z` obtained
by removing the rest of the preimage of `V`, together with the closed subscheme `Y \ V ⊆ U`,
is the required refinement.

## Main definitions

- `AlgebraicGeometry.Scheme.Hom.FactorsLocallyThrough`: `r` factors through `u` Zariski
  locally on its source.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.exists_isFinite_factorsLocallyThrough`: the induction.
-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

namespace AlgebraicGeometry

variable {U T T' T'' : Scheme.{u}}

/-- A morphism `r : T' ⟶ T` *factors locally through* `u : U ⟶ T` if every point of `T'` has an
open neighbourhood `O ⟶ T'` and a morphism `φ : O ⟶ U` with `φ ≫ u = (O ⟶ T') ≫ r`. -/
def Scheme.Hom.FactorsLocallyThrough (r : T' ⟶ T) (u : U ⟶ T) : Prop :=
  ∀ z : T', ∃ (O : Scheme.{u}) (ι : O ⟶ T') (_ : IsOpenImmersion ι) (φ : O ⟶ U),
    z ∈ Set.range ι ∧ φ ≫ u = ι ≫ r

namespace Scheme.Hom.FactorsLocallyThrough

variable {r : T' ⟶ T} {u : U ⟶ T}

lemma comp_left (h : r.FactorsLocallyThrough u) (k : T'' ⟶ T') :
    (k ≫ r).FactorsLocallyThrough u := by
  intro z
  obtain ⟨O, ι, _, φ, hz, hφ⟩ := h (k z)
  refine ⟨pullback ι k, pullback.snd ι k, inferInstance, pullback.fst ι k ≫ φ, ?_, ?_⟩
  · rw [IsOpenImmersion.range_pullbackSnd]
    exact hz
  · rw [Category.assoc, hφ, pullback.condition_assoc]

lemma comp_right {W V : Scheme.{u}} {u' : W ⟶ V} {r : T' ⟶ V} (h : r.FactorsLocallyThrough u')
    (a : W ⟶ U) (b : V ⟶ T) (hab : a ≫ u = u' ≫ b) : (r ≫ b).FactorsLocallyThrough u := by
  intro z
  obtain ⟨O, ι, _, φ, hz, hφ⟩ := h z
  exact ⟨O, ι, inferInstance, φ ≫ a, hz, by rw [Category.assoc, hab, reassoc_of% hφ]⟩

/-- A local factorization on an open subscheme gives local factorizations near its points. -/
lemma exists_of_mem_range {O : Scheme.{u}} {ι : O ⟶ T'} [IsOpenImmersion ι]
    (h : (ι ≫ r).FactorsLocallyThrough u) {z : T'} (hz : z ∈ Set.range ι) :
    ∃ (O' : Scheme.{u}) (ι' : O' ⟶ T') (_ : IsOpenImmersion ι') (φ : O' ⟶ U),
      z ∈ Set.range ι' ∧ φ ≫ u = ι' ≫ r := by
  obtain ⟨o, rfl⟩ := hz
  obtain ⟨O₂, ι₂, _, φ, ⟨o₂, ho₂⟩, hφ⟩ := h o
  exact ⟨O₂, ι₂ ≫ ι, inferInstance, φ, ⟨o₂, by rw [Scheme.Hom.comp_apply, ho₂]⟩,
    by rw [hφ, Category.assoc]⟩

lemma coprodDesc {A B : Scheme.{u}} {r₁ : A ⟶ T} {r₂ : B ⟶ T}
    (h₁ : r₁.FactorsLocallyThrough u) (h₂ : r₂.FactorsLocallyThrough u) :
    (coprod.desc r₁ r₂).FactorsLocallyThrough u := by
  intro z
  obtain ⟨s, rfl⟩ := (coprodMk A B).surjective z
  rcases s with a | b
  · refine exists_of_mem_range (ι := coprod.inl) ?_ ⟨a, (coprodMk_inl A B a).symm⟩
    rwa [coprod.inl_desc]
  · refine exists_of_mem_range (ι := coprod.inr) ?_ ⟨b, (coprodMk_inr A B b).symm⟩
    rwa [coprod.inr_desc]

end Scheme.Hom.FactorsLocallyThrough

/-- Near a point mapping into an open `U ⊆ Y`, a morphism to `Y` factors through `U`. -/
lemma Scheme.Hom.exists_factorsLocallyThrough_of_mem_range {Y : Scheme.{u}} (j : U ⟶ Y)
    [IsOpenImmersion j] (π : Y ⟶ T) (h : T' ⟶ Y) {z : T'} (hz : h z ∈ Set.range j) :
    ∃ (O : Scheme.{u}) (ι : O ⟶ T') (_ : IsOpenImmersion ι) (φ : O ⟶ U),
      z ∈ Set.range ι ∧ φ ≫ j ≫ π = ι ≫ h ≫ π :=
  ⟨pullback j h, pullback.snd j h, inferInstance, pullback.fst j h,
    by rw [IsOpenImmersion.range_pullbackSnd]; exact hz, pullback.condition_assoc _⟩

/-- **The induction step.** Let `u : U ⟶ T` be surjective, étale, separated and quasi-compact
with at most `d + 1` geometric lifts, factored as a dense quasi-compact open immersion
`j : U ⟶ Y` followed by a finite `π : Y ⟶ T`. If the finite refinement exists for all such
morphisms with at most `d` geometric lifts, then it exists for `u`. -/
theorem Scheme.Hom.exists_isFinite_factorsLocallyThrough_of_isDominant {Y : Scheme.{u}}
    (u : U ⟶ T) [Etale u] [IsSeparated u] [QuasiCompact u] [Surjective u] [CompactSpace T]
    [QuasiSeparatedSpace T] (j : U ⟶ Y) [IsOpenImmersion j] [QuasiCompact j] [IsDominant j]
    (π : Y ⟶ T) [IsFinite π] (hjπ : j ≫ π = u) {d : ℕ}
    (hd : u.HasAtMostGeometricLifts (d + 1))
    (IH : ∀ {U' V : Scheme.{u}} (u' : U' ⟶ V) [Etale u'] [IsSeparated u'] [QuasiCompact u']
      [Surjective u'] [CompactSpace V] [QuasiSeparatedSpace V], u'.HasAtMostGeometricLifts d →
      ∃ (T' : Scheme.{u}) (r : T' ⟶ V), IsFinite r ∧ Surjective r ∧
        r.FactorsLocallyThrough u') :
    ∃ (T' : Scheme.{u}) (r : T' ⟶ T), IsFinite r ∧ Surjective r ∧ r.FactorsLocallyThrough u := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace π
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated π
  have : CompactSpace ↥(pullback u π) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd u π)
  -- the graph of `j` is open and closed in `U ×_T Y`
  let g : U ⟶ pullback u π := pullback.lift (𝟙 U) j (by rw [Category.id_comp, hjπ])
  have hg₁ : g ≫ pullback.fst u π = 𝟙 U := pullback.lift_fst _ _ _
  have hg₂ : g ≫ pullback.snd u π = j := pullback.lift_snd _ _ _
  have : IsClosedImmersion g := MorphismProperty.of_postcomp (W := @IsClosedImmersion)
    (W' := @IsSeparated) g (pullback.fst u π) inferInstance (by rw [hg₁]; infer_instance)
  have : Etale g := MorphismProperty.of_postcomp (W := @Etale) (W' := @Etale) g
    (pullback.snd u π) inferInstance (by rw [hg₂]; infer_instance)
  let W : (pullback u π).Opens := ⟨(Set.range g)ᶜ, g.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hWc : IsClosed (W : Set ↥(pullback u π)) := g.isOpenMap.isOpen_range.isClosed_compl
  have : QuasiCompact W.ι := W.quasiCompact_ι_of_isClosed hWc
  -- its complement maps onto an open `V ⊆ Y` containing `Y \ U`
  let V : Y.Opens := ⟨pullback.snd u π '' W, (pullback.snd u π).isOpenMap _ W.2⟩
  have hWV : Set.range (W.ι ≫ pullback.snd u π) ⊆ Set.range V.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact ⟨w.1, w.2, rfl⟩
  let u' : W.toScheme ⟶ V.toScheme := IsOpenImmersion.lift V.ι (W.ι ≫ pullback.snd u π) hWV
  have hu' : u' ≫ V.ι = W.ι ≫ pullback.snd u π := IsOpenImmersion.lift_fac _ _ _
  have : Etale u' := MorphismProperty.of_postcomp (W := @Etale) (W' := @Etale) u' V.ι
    inferInstance (by rw [hu']; infer_instance)
  have : IsSeparated u' := MorphismProperty.of_postcomp (W := @IsSeparated) (W' := ⊤) u' V.ι
    trivial (by rw [hu']; infer_instance)
  have : QuasiCompact u' := MorphismProperty.of_postcomp (W := @QuasiCompact)
    (W' := @QuasiSeparated) u' V.ι inferInstance (by rw [hu']; infer_instance)
  have : Surjective u' := by
    refine ⟨fun v ↦ ?_⟩
    obtain ⟨w, hw, hwv⟩ := v.2
    refine ⟨⟨w, hw⟩, V.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hu']
    exact hwv
  have hVc : IsCompact (V : Set Y) := hWc.isCompact.image (pullback.snd u π).continuous
  have : CompactSpace V.toScheme := isCompact_iff_compactSpace.mp hVc
  have : QuasiSeparatedSpace V.toScheme := quasiSeparatedSpace_of_quasiSeparated V.ι
  have hYV (y : Y) (hy : y ∉ Set.range j) : y ∈ V := by
    obtain ⟨p, hp⟩ := (pullback.snd u π).surjective y
    refine ⟨p, fun ⟨x, hx⟩ ↦ hy ⟨x, ?_⟩, hp⟩
    rw [← hp, ← hx, ← Scheme.Hom.comp_apply, hg₂]
  -- `W ⟶ V` has at most `d` geometric lifts
  have hd' : u'.HasAtMostGeometricLifts d := by
    intro K _ _ σ x hx hinj
    let X (i : Fin (d + 1)) := x i ≫ W.ι ≫ pullback.fst u π
    have hXsnd (i : Fin (d + 1)) : x i ≫ W.ι ≫ pullback.snd u π = σ ≫ V.ι := by
      rw [← hu', reassoc_of% (hx i)]
    have hXu (i : Fin (d + 1)) : X i ≫ u = σ ≫ V.ι ≫ π := by
      simp only [X, Category.assoc, pullback.condition]
      rw [reassoc_of% (hXsnd i)]
    have hXinj : Function.Injective X := by
      intro i₁ i₂ e
      apply hinj
      rw [← cancel_mono W.ι]
      apply pullback.hom_ext
      · simpa only [Category.assoc] using e
      · simp only [Category.assoc, hXsnd]
    by_cases hy : V.ι (σ (closedPoint K)) ∈ Set.range j
    · -- over `U`, the point of the graph is one more lift
      have hσj : Set.range (σ ≫ V.ι) ⊆ Set.range j := by
        rintro _ ⟨w, rfl⟩
        rw [Subsingleton.elim w (closedPoint K)]
        exact hy
      let δ := IsOpenImmersion.lift j (σ ≫ V.ι) hσj
      have hδ : δ ≫ j = σ ≫ V.ι := IsOpenImmersion.lift_fac _ _ _
      have hδu : δ ≫ u = σ ≫ V.ι ≫ π := by rw [← hjπ, reassoc_of% hδ]
      have hδX (i : Fin (d + 1)) : δ ≠ X i := by
        intro e
        have he : x i ≫ W.ι = δ ≫ g := by
          apply pullback.hom_ext
          · rw [Category.assoc, Category.assoc, hg₁, Category.comp_id]
            exact e.symm
          · rw [Category.assoc, hXsnd, Category.assoc, hg₂, hδ]
        apply (x i (closedPoint K)).2
        refine ⟨δ (closedPoint K), ?_⟩
        rw [← Scheme.Hom.comp_apply, ← he]
        rfl
      exact hd K (σ ≫ V.ι ≫ π) (Fin.cons δ X) (Fin.cases hδu hXu)
        (Fin.cons_injective_iff.mpr ⟨fun ⟨i, hi⟩ ↦ hδX i hi.symm, hXinj⟩)
    · -- over `Y \ U`, the bound drops by specialization
      obtain ⟨x₀, hx₀⟩ := exists_specializes_of_mem_closure_range j
        (z := V.ι (σ (closedPoint K))) (by rw [j.denseRange.closure_range]; trivial)
      exact u.not_injective_lifts_of_specializes j π hjπ hd hx₀ hy (σ ≫ V.ι ≫ π)
        (by simp only [Scheme.Hom.comp_apply]) X hXu hXinj
  -- the refinement of `W ⟶ V`, extended to a finite `Y`-scheme `Z`
  obtain ⟨T₁, r₁, _, _, hr₁⟩ := IH u' hd'
  have : QuasiCompact V.ι := V.quasiCompact_ι hVc
  obtain ⟨Z, e, π', _, _, _, heπ'⟩ :=
    (r₁ ≫ V.ι).exists_isOpenImmersion_isFinite_of_locallyQuasiFinite
  let O := π' ⁻¹ᵁ V
  have heO : Set.range e ⊆ Set.range O.ι := by
    rintro _ ⟨t, rfl⟩
    rw [Scheme.Opens.range_ι]
    change π' (e t) ∈ V
    rw [← Scheme.Hom.comp_apply, heπ', Scheme.Hom.comp_apply]
    exact (r₁ t).2
  let e' : T₁ ⟶ O.toScheme := IsOpenImmersion.lift O.ι e heO
  have he' : e' ≫ O.ι = e := IsOpenImmersion.lift_fac _ _ _
  have he'π' : e' ≫ π' ∣_ V = r₁ := by
    rw [← cancel_mono V.ι, Category.assoc, morphismRestrict_ι, reassoc_of% he', heπ']
  have : UniversallyClosed e' := MorphismProperty.of_postcomp (W := @UniversallyClosed)
    (W' := @IsSeparated) e' (π' ∣_ V) inferInstance (by rw [he'π']; infer_instance)
  -- the part `B` of the preimage of `V` outside `T₁` is open
  have hB : IsOpen ((O : Set Z) ∩ (Set.range e)ᶜ) := by
    convert O.ι.isOpenMap _ e'.isClosedMap.isClosed_range.isOpen_compl using 1
    ext p
    constructor
    · rintro ⟨hpO, hpe⟩
      refine ⟨⟨p, hpO⟩, fun ⟨t, ht⟩ ↦ hpe ⟨t, ?_⟩, rfl⟩
      rw [← he', Scheme.Hom.comp_apply, ht]
      rfl
    · rintro ⟨q, hq, rfl⟩
      refine ⟨q.2, fun ⟨t, ht⟩ ↦ hq ⟨t, O.ι.isOpenEmbedding.injective ?_⟩⟩
      rw [← Scheme.Hom.comp_apply, he', ht]
  let G : TopologicalSpace.Closeds Z := ⟨_, hB.isClosed_compl⟩
  let ι₂ := (Scheme.IdealSheafData.vanishingIdeal G).subschemeι
  have hι₂ : Set.range ι₂ = (G : Set Z) := by
    rw [Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
  let C : TopologicalSpace.Closeds Y := ⟨_, V.2.isClosed_compl⟩
  let ι₃ := (Scheme.IdealSheafData.vanishingIdeal C).subschemeι
  have hι₃ : Set.range ι₃ = (C : Set Y) := by
    rw [Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
  refine ⟨_, coprod.desc (ι₂ ≫ π' ≫ π) (ι₃ ≫ π), inferInstance, ⟨fun t ↦ ?_⟩, ?_⟩
  · -- surjectivity
    obtain ⟨x, rfl⟩ := u.surjective t
    by_cases hx : j x ∈ V
    · obtain ⟨t₁, ht₁⟩ := r₁.surjective ⟨j x, hx⟩
      have hp : e t₁ ∈ (G : Set Z) := fun ⟨_, hne⟩ ↦ hne ⟨t₁, rfl⟩
      rw [← hι₂] at hp
      obtain ⟨z, hz⟩ := hp
      refine ⟨(coprod.inl (X := (Scheme.IdealSheafData.vanishingIdeal G).subscheme)
        (Y := (Scheme.IdealSheafData.vanishingIdeal C).subscheme)) z, ?_⟩
      rw [← Scheme.Hom.comp_apply, coprod.inl_desc, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply,
        hz, ← Scheme.Hom.comp_apply e, heπ', Scheme.Hom.comp_apply, ht₁, ← hjπ,
        Scheme.Hom.comp_apply]
      rfl
    · have hp : j x ∈ Set.range ι₃ := by rw [hι₃]; exact hx
      obtain ⟨z, hz⟩ := hp
      refine ⟨(coprod.inr (X := (Scheme.IdealSheafData.vanishingIdeal G).subscheme)
        (Y := (Scheme.IdealSheafData.vanishingIdeal C).subscheme)) z, ?_⟩
      rw [← Scheme.Hom.comp_apply, coprod.inr_desc, Scheme.Hom.comp_apply, hz, ← hjπ,
        Scheme.Hom.comp_apply]
  · -- local factorization
    have hW : (r₁ ≫ V.ι ≫ π).FactorsLocallyThrough u :=
      hr₁.comp_right (W.ι ≫ pullback.fst u π) (V.ι ≫ π)
        (by rw [Category.assoc, pullback.condition, ← reassoc_of% hu'])
    refine Scheme.Hom.FactorsLocallyThrough.coprodDesc (fun z ↦ ?_) (fun z ↦ ?_)
    · by_cases hz : π' (ι₂ z) ∈ V
      · have hmem : ι₂ z ∈ Set.range e := by
          have : ι₂ z ∈ (G : Set Z) := hι₂ ▸ ⟨z, rfl⟩
          by_contra h
          exact this ⟨hz, h⟩
        refine Scheme.Hom.FactorsLocallyThrough.exists_of_mem_range (ι := pullback.snd e ι₂) ?_
          (by rw [IsOpenImmersion.range_pullbackSnd]; exact hmem)
        have heq : pullback.snd e ι₂ ≫ ι₂ ≫ π' ≫ π = pullback.fst e ι₂ ≫ r₁ ≫ V.ι ≫ π := by
          rw [← pullback.condition_assoc, reassoc_of% heπ']
        rw [heq]
        exact hW.comp_left (pullback.fst e ι₂)
      · obtain ⟨O, ι, _, φ, hzO, hφ⟩ := Scheme.Hom.exists_factorsLocallyThrough_of_mem_range j π
          (ι₂ ≫ π') (z := z) (by
            by_contra h
            exact hz (hYV _ h))
        exact ⟨O, ι, inferInstance, φ, hzO, by rw [← hjπ, hφ, Category.assoc]⟩
    · obtain ⟨O, ι, _, φ, hzO, hφ⟩ := Scheme.Hom.exists_factorsLocallyThrough_of_mem_range j π
        ι₃ (z := z) (by
          by_contra h
          have : ι₃ z ∈ (C : Set Y) := hι₃ ▸ ⟨z, rfl⟩
          exact this (hYV _ h))
      exact ⟨O, ι, inferInstance, φ, hzO, by rw [← hjπ, hφ]⟩

/-- **Finite refinement of a surjective étale morphism, by induction on the degree.** Let
`u : U ⟶ T` be surjective, étale, separated and quasi-compact, with `T` quasi-compact and
quasi-separated, and with at most `d` geometric lifts. Then there is a finite surjective
`r : T' ⟶ T` which factors through `u` Zariski locally on `T'`. -/
theorem Scheme.Hom.exists_isFinite_factorsLocallyThrough (d : ℕ) :
    ∀ {U T : Scheme.{u}} (u : U ⟶ T) [Etale u] [IsSeparated u] [QuasiCompact u] [Surjective u]
      [CompactSpace T] [QuasiSeparatedSpace T], u.HasAtMostGeometricLifts d →
      ∃ (T' : Scheme.{u}) (r : T' ⟶ T), IsFinite r ∧ Surjective r ∧
        r.FactorsLocallyThrough u := by
  induction d with
  | zero =>
    intro U T u _ _ _ _ _ _ hd
    have : IsEmpty T := by
      refine ⟨fun t ↦ ?_⟩
      obtain ⟨x, rfl⟩ := u.surjective t
      let σ := Spec.map (CommRingCat.ofHom (algebraMap (U.residueField x)
        (AlgebraicClosure (U.residueField x)))) ≫ U.fromSpecResidueField x
      exact hd (AlgebraicClosure (U.residueField x)) (σ ≫ u) (fun _ ↦ σ) (fun _ ↦ rfl)
        (fun i₁ i₂ _ ↦ Fin.ext (by have := i₁.2; have := i₂.2; omega))
    exact ⟨T, 𝟙 T, inferInstance, inferInstance, fun z ↦ isEmptyElim z⟩
  | succ d ih =>
    intro U T u _ _ _ _ _ _ hd
    obtain ⟨Y, j, π, _, _, _, hjπ⟩ := u.exists_isOpenImmersion_isFinite_of_locallyQuasiFinite
    exact u.exists_isFinite_factorsLocallyThrough_of_isDominant j.toImage (j.imageι ≫ π)
      (by rw [j.toImage_imageι_assoc, hjπ]) hd (fun u' ↦ ih u')

end AlgebraicGeometry
