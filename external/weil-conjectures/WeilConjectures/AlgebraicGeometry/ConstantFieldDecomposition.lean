/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FormallyUnramifiedSections
public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius.FiberMapPow
public import WeilConjectures.FieldTheory.FiniteFieldEmbeddings
public import WeilConjectures.WeilSheaf.ConstantFieldComponent
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# The geometric fibre over a smaller base field is a disjoint union of components

Let `k₀ ⊆ k'` be fields with `k'` algebraic over `k₀`, and let `V` be a scheme over `k'` through
`c : V ⟶ Spec k'`, hence over `k₀` through `f = c ≫ (Spec k' ⟶ Spec k₀)`. Put
`S = Spec k' ×_{k₀} Spec k̄`. The geometric fibre `V ⊗_{k₀} k̄` maps to `S`
(`AlgebraicGeometry.Scheme.Hom.geometricFiberToConstantFieldFiber`), and is the base change of
`c` along `S ⟶ Spec k'`. The component map `θ : V ⊗_{k'} k̄' ⟶ V ⊗_{k₀} k̄`
(`AlgebraicGeometry.Scheme.Hom.geometricFiberComponentMap`) is the base change of a section
`s₀ : Spec k̄ ⟶ S` of the projection `S ⟶ Spec k̄`; when `k'/k₀` is separable, sections of this
étale projection are open immersions, so `θ` is an open immersion onto the preimage of the
range of `s₀` (`AlgebraicGeometry.Scheme.Hom.isOpenImmersion_geometricFiberComponentMap`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom

variable {k₀ k' : Type u} [Field k₀] [Field k'] [Algebra k₀ k'] [Algebra.IsAlgebraic k₀ k']
  {V : Scheme.{u}} (c : V ⟶ Spec (.of k')) (f : V ⟶ Spec (.of k₀))
  (hc : c ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ k')) = f)

variable (k₀ k') in
/-- The scheme `S = Spec k' ×_{k₀} Spec k̄`. -/
abbrev constantFieldFiber : Scheme.{u} :=
  pullback (Spec.map (CommRingCat.ofHom (algebraMap k₀ k'))) (Scheme.specAlgebraicClosure k₀).hom

include hc in
/-- The map `V ⊗_{k₀} k̄ ⟶ Spec k' ×_{k₀} Spec k̄` induced by `c`. -/
def geometricFiberToConstantFieldFiber : f.geometricFiber ⟶ constantFieldFiber k₀ k' :=
  pullback.lift (f.geometricFiberProj ≫ c) f.geometricFiberToAlgebraicClosure (by
    rw [Category.assoc, hc, geometricFiber_condition])

omit [Algebra.IsAlgebraic k₀ k'] in
@[reassoc (attr := simp)]
lemma geometricFiberToConstantFieldFiber_fst :
    geometricFiberToConstantFieldFiber c f hc ≫ pullback.fst _ _ = f.geometricFiberProj ≫ c :=
  pullback.lift_fst _ _ _

omit [Algebra.IsAlgebraic k₀ k'] in
@[reassoc (attr := simp)]
lemma geometricFiberToConstantFieldFiber_snd :
    geometricFiberToConstantFieldFiber c f hc ≫ pullback.snd _ _ =
      f.geometricFiberToAlgebraicClosure :=
  pullback.lift_snd _ _ _

omit [Algebra.IsAlgebraic k₀ k'] in
/-- The geometric fibre `V ⊗_{k₀} k̄` is the base change of `c : V ⟶ Spec k'` along
`S ⟶ Spec k'`. -/
lemma isPullback_geometricFiberToConstantFieldFiber :
    IsPullback f.geometricFiberProj (geometricFiberToConstantFieldFiber c f hc) c
      (pullback.fst _ _) := by
  refine IsPullback.of_bot ?_ (geometricFiberToConstantFieldFiber_fst c f hc).symm
    (IsPullback.of_hasPullback _ _)
  rw [geometricFiberToConstantFieldFiber_snd, hc]
  exact IsPullback.of_hasPullback _ _

/-- The section `s₀ : Spec k̄ ⟶ S` given by `k' ⟶ k̄' ≅ k̄`. -/
def constantFieldFiberSection : Spec (.of (AlgebraicClosure k₀)) ⟶ constantFieldFiber k₀ k' :=
  pullback.lift (Spec.map (CommRingCat.ofHom (algebraicClosureAlgEquiv k₀ k').toRingHom) ≫
    (Scheme.specAlgebraicClosure k').hom) (𝟙 _) (by
    rw [Category.id_comp, Category.assoc]
    simp only [Scheme.specAlgebraicClosure, Over.mk_hom, ← Spec.map_comp]
    congr 1
    ext x
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    rw [← IsScalarTower.algebraMap_apply]
    exact (algebraicClosureAlgEquiv k₀ k').commutes x)

@[reassoc (attr := simp)]
lemma constantFieldFiberSection_snd :
    constantFieldFiberSection (k₀ := k₀) (k' := k') ≫ pullback.snd _ _ = 𝟙 _ :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
lemma constantFieldFiberSection_fst :
    constantFieldFiberSection (k₀ := k₀) (k' := k') ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (algebraicClosureAlgEquiv k₀ k').toRingHom) ≫
        (Scheme.specAlgebraicClosure k').hom :=
  pullback.lift_fst _ _ _

/-- The component map `θ` is the base change of the section `s₀` along
`V ⊗_{k₀} k̄ ⟶ S`. -/
lemma isPullback_geometricFiberComponentMap :
    IsPullback (geometricFiberComponentMap c f hc)
      (c.geometricFiberToAlgebraicClosure ≫
        Spec.map (CommRingCat.ofHom (algebraicClosureAlgEquiv k₀ k').symm.toRingHom))
      (geometricFiberToConstantFieldFiber c f hc) constantFieldFiberSection := by
  let e : Spec (.of (AlgebraicClosure k')) ≅ Spec (.of (AlgebraicClosure k₀)) :=
    Scheme.Spec.mapIso (algebraicClosureAlgEquiv k₀ k').symm.toRingEquiv.toCommRingCatIso.op
  refine IsPullback.of_right ?_ ?_ (isPullback_geometricFiberToConstantFieldFiber c f hc)
  · rw [geometricFiberComponentMap_comp_geometricFiberProj, constantFieldFiberSection_fst]
    have h := (IsPullback.of_hasPullback c (Scheme.specAlgebraicClosure k').hom)
    refine IsPullback.of_iso h (Iso.refl _) (Iso.refl _) e (Iso.refl _) ?_ ?_ ?_ ?_
    · simp only [Iso.refl_hom, Category.comp_id]
      rfl
    · simp only [Iso.refl_hom, Category.id_comp]
      rfl
    · simp
    · have he : e.hom = Spec.map (CommRingCat.ofHom
          (algebraicClosureAlgEquiv k₀ k').symm.toRingEquiv.toRingHom) := rfl
      simp only [Iso.refl_hom, Category.comp_id]
      rw [he, ← Category.assoc, spec_map_comp_spec_map_eq _ _ (RingHom.id _) (fun x ↦ by simp),
        CommRingCat.ofHom_id, Spec.map_id]
      exact (Category.id_comp _).symm
  · refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, geometricFiberToConstantFieldFiber_fst,
        geometricFiberComponentMap_comp_geometricFiberProj_assoc, constantFieldFiberSection_fst]
      have h1 : Spec.map (CommRingCat.ofHom
            (algebraicClosureAlgEquiv k₀ k').symm.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraicClosureAlgEquiv k₀ k').toRingHom) = 𝟙 _ := by
        rw [spec_map_comp_spec_map_eq _ _ (RingHom.id _) (fun x ↦ by simp), CommRingCat.ofHom_id,
          Spec.map_id]
      rw [geometricFiber_condition]
      erw [reassoc_of% h1]
    · simp

omit [Algebra.IsAlgebraic k₀ k'] in
/-- The map to `S` is the base change of `c` to the algebraic closure. -/
lemma geometricFiberToConstantFieldFiber_eq :
    geometricFiberToConstantFieldFiber c f hc = geometricFiberMap c hc :=
  pullback.hom_ext (by simp [geometricFiberMap]; rfl) (by simp [geometricFiberMap]; rfl)

/-- The component map lands exactly over the range of the section `s₀`. -/
lemma range_geometricFiberComponentMap :
    Set.range (geometricFiberComponentMap c f hc).base =
      (geometricFiberToConstantFieldFiber c f hc).base ⁻¹'
        Set.range (constantFieldFiberSection (k₀ := k₀) (k' := k')).base := by
  have h := isPullback_geometricFiberComponentMap c f hc
  rw [← Scheme.Pullback.range_fst, ← h.isoPullback_hom_fst, Scheme.Hom.comp_base,
    TopCat.coe_comp, Set.range_comp, Set.range_eq_univ.2, Set.image_univ]
  exact h.isoPullback.hom.homeomorph.surjective

section Separable

variable [Algebra.IsSeparable k₀ k'] [Module.Finite k₀ k']

omit [Algebra.IsAlgebraic k₀ k'] [Module.Finite k₀ k'] in
variable (k₀ k') in
lemma formallyUnramified_specMap_algebraMap :
    FormallyUnramified (Spec.map (CommRingCat.ofHom (algebraMap k₀ k'))) := by
  rw [HasRingHomProperty.Spec_iff (P := @FormallyUnramified)]
  exact RingHom.formallyUnramified_algebraMap.2 (Algebra.FormallyUnramified.of_isSeparable k₀ k')

omit [Algebra.IsAlgebraic k₀ k'] [Algebra.IsSeparable k₀ k'] in
variable (k₀ k') in
lemma locallyOfFiniteType_specMap_algebraMap :
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k₀ k'))) := by
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  exact RingHom.finiteType_algebraMap.2 inferInstance

omit [Algebra.IsAlgebraic k₀ k'] [Module.Finite k₀ k'] in
variable (k₀ k') in
/-- The projection `S ⟶ Spec k̄` is formally unramified and locally of finite type. -/
lemma formallyUnramified_constantFieldFiber_snd :
    FormallyUnramified (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k₀ k')))
      (Scheme.specAlgebraicClosure k₀).hom) :=
  have := formallyUnramified_specMap_algebraMap k₀ k'
  MorphismProperty.pullback_snd _ _ inferInstance

omit [Algebra.IsAlgebraic k₀ k'] [Algebra.IsSeparable k₀ k'] in
variable (k₀ k') in
lemma locallyOfFiniteType_constantFieldFiber_snd :
    LocallyOfFiniteType (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k₀ k')))
      (Scheme.specAlgebraicClosure k₀).hom) :=
  have := locallyOfFiniteType_specMap_algebraMap k₀ k'
  MorphismProperty.pullback_snd _ _ inferInstance

/-- The section `s₀` is an open immersion. -/
lemma isOpenImmersion_constantFieldFiberSection :
    IsOpenImmersion (constantFieldFiberSection (k₀ := k₀) (k' := k')) :=
  have := formallyUnramified_constantFieldFiber_snd k₀ k'
  have := locallyOfFiniteType_constantFieldFiber_snd k₀ k'
  FormallyUnramified.isOpenImmersion_of_comp_eq_id _ _ constantFieldFiberSection_snd

/-- **The component map is an open immersion.** -/
instance isOpenImmersion_geometricFiberComponentMap :
    IsOpenImmersion (geometricFiberComponentMap c f hc) :=
  have := isOpenImmersion_constantFieldFiberSection (k₀ := k₀) (k' := k')
  MorphismProperty.of_isPullback (isPullback_geometricFiberComponentMap c f hc).flip inferInstance

end Separable

section Finite

variable [Finite k₀] [Finite k']

variable (k₀ k') in
/-- The `k₀`-embedding `k' ⟶ k̄' ≅ k̄`. -/
def constantFieldEmbedding : k' →ₐ[k₀] AlgebraicClosure k₀ :=
  (algebraicClosureAlgEquiv k₀ k').toAlgHom.comp
    (IsScalarTower.toAlgHom k₀ k' (AlgebraicClosure k'))

omit [Finite k₀] [Finite k'] in
lemma constantFieldFiberSection_fst' :
    constantFieldFiberSection (k₀ := k₀) (k' := k') ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (constantFieldEmbedding k₀ k').toRingHom) := by
  rw [constantFieldFiberSection_fst]
  exact spec_map_comp_spec_map_eq _ _ _ fun x ↦ rfl

variable (k₀) in
/-- The inverse of the `n`-th power of the geometric Frobenius `σ` of `Spec k̄` is the spectrum of
the `n`-th power of the arithmetic Frobenius `x ↦ x ^ q`. -/
lemma specGeometricFrobenius_pow_inv [Fintype k₀] (n : ℕ) :
    (specGeometricFrobenius k₀ ^ n).asIso.inv =
      Spec.map (CommRingCat.ofHom (FiniteField.frobeniusAlgHom k₀ (AlgebraicClosure k₀) ^
        n).toRingHom) := by
  rw [← cancel_epi (specGeometricFrobenius k₀ ^ n).asIso.hom, Iso.hom_inv_id,
    specGeometricFrobenius_pow_hom, spec_map_comp_spec_map_eq _ _ (RingHom.id _) fun x ↦ ?_,
    CommRingCat.ofHom_id, Spec.map_id]
  simp only [RingHom.coe_coe, AlgHom.toRingHom_eq_coe, RingHom.id_apply]
  rw [FiniteField.geometricFrobeniusAlgEquivOfAlgebraic_eq_inv, inv_pow, AlgEquiv.aut_inv]
  change ((FiniteField.frobeniusAlgEquivOfAlgebraic k₀ (AlgebraicClosure k₀) ^ n).symm) _ = x
  rw [AlgEquiv.symm_apply_eq, AlgEquiv.coe_pow, AlgHom.coe_pow,
    FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate, FiniteField.coe_frobeniusAlgHom,
    pow_iterate]

variable (k₀ k') in
/-- The sections `tₙ = σ⁻ⁿ ≫ s₀ ≫ φⁿ : Spec k̄ ⟶ S` of the projection `S ⟶ Spec k̄`, where `φ`
is the geometric Galois Frobenius of `S` and `σ` that of `Spec k̄`. -/
def constantFieldFiberSectionPow (n : ℕ) :
    Spec (.of (AlgebraicClosure k₀)) ⟶ constantFieldFiber k₀ k' :=
  (specGeometricFrobenius k₀ ^ n).asIso.inv ≫ constantFieldFiberSection ≫
    ((Spec.map (CommRingCat.ofHom (algebraMap k₀ k'))).geometricGaloisFrobenius ^ n).asIso.hom

omit [Finite k'] in
lemma constantFieldFiberSectionPow_snd (n : ℕ) :
    constantFieldFiberSectionPow k₀ k' n ≫ pullback.snd _ _ = 𝟙 _ := by
  have h := geometricGaloisFrobenius_pow_hom_comp_geometricFiberToAlgebraicClosure
    (Spec.map (CommRingCat.ofHom (algebraMap k₀ k'))) n
  have h0 : constantFieldFiberSection (k₀ := k₀) (k' := k') ≫
      (Spec.map (CommRingCat.ofHom (algebraMap k₀ k'))).geometricFiberToAlgebraicClosure = 𝟙 _ :=
    constantFieldFiberSection_snd
  have h1 : (specGeometricFrobenius k₀ ^ n).asIso.inv ≫
      (specGeometricFrobenius k₀ ^ n).asIso.hom = 𝟙 _ :=
    Iso.inv_hom_id _
  change _ ≫ (Spec.map (CommRingCat.ofHom (algebraMap k₀ k'))).geometricFiberToAlgebraicClosure = _
  simp only [constantFieldFiberSectionPow, Category.assoc, h, reassoc_of% h0, h1]

omit [Finite k'] in
lemma constantFieldFiberSectionPow_fst [Fintype k₀] (n : ℕ) :
    constantFieldFiberSectionPow k₀ k' n ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom ((FiniteField.frobeniusAlgHom k₀ (AlgebraicClosure k₀) ^ n).comp
        (constantFieldEmbedding k₀ k')).toRingHom) := by
  have h := geometricGaloisFrobenius_pow_hom_comp_geometricFiberProj
    (Spec.map (CommRingCat.ofHom (algebraMap k₀ k'))) n
  have h0 : constantFieldFiberSection (k₀ := k₀) (k' := k') ≫
      (Spec.map (CommRingCat.ofHom (algebraMap k₀ k'))).geometricFiberProj =
        Spec.map (CommRingCat.ofHom (constantFieldEmbedding k₀ k').toRingHom) :=
    constantFieldFiberSection_fst'
  change _ ≫ (Spec.map (CommRingCat.ofHom (algebraMap k₀ k'))).geometricFiberProj = _
  simp only [constantFieldFiberSectionPow, Category.assoc, h, h0]
  rw [specGeometricFrobenius_pow_inv]
  exact spec_map_comp_spec_map_eq _ _ _ fun x ↦ rfl

/-- Every section of the projection `S ⟶ Spec k̄` is one of the `tₙ`, `n < [k' : k₀]`. -/
lemma exists_eq_constantFieldFiberSectionPow
    (t : Spec (.of (AlgebraicClosure k₀)) ⟶ constantFieldFiber k₀ k')
    (ht : t ≫ pullback.snd _ _ = 𝟙 _) :
    ∃ n : Fin (Module.finrank k₀ k'), t = constantFieldFiberSectionPow k₀ k' n := by
  let := Fintype.ofFinite k₀
  have : Module.Finite k₀ k' := Module.Finite.of_finite
  set g := Spec.preimage (t ≫ pullback.fst _ _)
  have hg : CommRingCat.ofHom (algebraMap k₀ k') ≫ g =
      CommRingCat.ofHom (algebraMap k₀ (AlgebraicClosure k₀)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, Category.assoc, pullback.condition, reassoc_of% ht]
    rfl
  let g' : k' →ₐ[k₀] AlgebraicClosure k₀ :=
    { g.hom with commutes' := fun x ↦ congrArg (fun φ ↦ φ.hom x) hg }
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgHom_pow_comp k₀ k'
    (constantFieldEmbedding k₀ k')).2 g'
  refine ⟨n, pullback.hom_ext ?_ ?_⟩
  · rw [constantFieldFiberSectionPow_fst]
    dsimp only at hn
    rw [hn, ← Spec.map_preimage (t ≫ pullback.fst _ _)]
    rfl
  · rw [ht, constantFieldFiberSectionPow_snd]

/-- The sections `tₙ`, `n < [k' : k₀]`, are pairwise distinct. -/
lemma constantFieldFiberSectionPow_injective :
    Function.Injective fun n : Fin (Module.finrank k₀ k') ↦
      constantFieldFiberSectionPow k₀ k' n := by
  let := Fintype.ofFinite k₀
  have : Module.Finite k₀ k' := Module.Finite.of_finite
  intro n m h
  refine (FiniteField.bijective_frobeniusAlgHom_pow_comp k₀ k'
    (constantFieldEmbedding k₀ k')).1 (AlgHom.ext fun x ↦ ?_)
  have h' := congrArg (· ≫ pullback.fst _ _) h
  simp only [constantFieldFiberSectionPow_fst] at h'
  exact congrArg (fun φ ↦ φ.hom x) (Spec.map_injective h')

/-- Every point of `S` lies on exactly one of the sections `tₙ`, `n < [k' : k₀]`. -/
lemma existsUnique_mem_range_constantFieldFiberSectionPow (z : constantFieldFiber k₀ k') :
    ∃! n : Fin (Module.finrank k₀ k'),
      z ∈ Set.range (constantFieldFiberSectionPow k₀ k' n).base := by
  have : Module.Finite k₀ k' := Module.Finite.of_finite
  have := formallyUnramified_constantFieldFiber_snd k₀ k'
  have := locallyOfFiniteType_constantFieldFiber_snd k₀ k'
  obtain ⟨t, ht, hz⟩ := FormallyUnramified.exists_comp_eq_id_of_isAlgClosed (pullback.snd _ _) z
  obtain ⟨n, rfl⟩ := exists_eq_constantFieldFiberSectionPow t ht
  refine ⟨n, hz, fun m hm ↦ constantFieldFiberSectionPow_injective ?_⟩
  obtain ⟨x, hx⟩ := hm
  obtain ⟨y, hy⟩ := hz
  exact FormallyUnramified.eq_of_comp_eq_id_of_apply_eq (pullback.snd _ _)
    (constantFieldFiberSectionPow_snd _) (constantFieldFiberSectionPow_snd _) (hx.trans hy.symm)

private lemma comp_base_apply' {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) (x : X) :
    (a ≫ b).base x = b.base (a.base x) :=
  rfl

private lemma id_base_apply' {X : Scheme.{u}} (x : X) : (𝟙 X : X ⟶ X).base x = x :=
  rfl


private lemma iso_inv_hom_apply {X Y : Scheme.{u}} (e : X ≅ Y) (x : X) :
    e.inv.base (e.hom.base x) = x := by
  rw [← comp_base_apply', e.hom_inv_id]
  rfl

private lemma iso_hom_inv_apply {X Y : Scheme.{u}} (e : X ≅ Y) (y : Y) :
    e.hom.base (e.inv.base y) = y := by
  rw [← comp_base_apply', e.inv_hom_id]
  rfl

omit [Finite k'] in
lemma mem_range_geometricFiberComponentMap_comp_iff (n : ℕ) (x : f.geometricFiber) :
    x ∈ Set.range (geometricFiberComponentMap c f hc ≫
      (f.geometricGaloisFrobenius ^ n).asIso.hom).base ↔
      (geometricFiberToConstantFieldFiber c f hc).base x ∈
        Set.range (constantFieldFiberSectionPow k₀ k' n).base := by
  have h := geometricFiberMap_comp_geometricGaloisFrobenius_pow c hc n
  rw [← geometricFiberToConstantFieldFiber_eq c f hc] at h
  have h' : (f.geometricGaloisFrobenius ^ n).asIso.inv ≫ geometricFiberToConstantFieldFiber c f hc =
      geometricFiberToConstantFieldFiber c f hc ≫
        ((Spec.map (CommRingCat.ofHom (algebraMap k₀ k'))).geometricGaloisFrobenius ^
          n).asIso.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have hr := range_geometricFiberComponentMap c f hc
  constructor
  · rintro ⟨y, rfl⟩
    have hy : (geometricFiberToConstantFieldFiber c f hc).base
        ((geometricFiberComponentMap c f hc).base y) ∈
          Set.range (constantFieldFiberSection (k₀ := k₀) (k' := k')).base := by
      rw [← Set.mem_preimage, ← hr]
      exact ⟨y, rfl⟩
    obtain ⟨w, hw⟩ := hy
    refine ⟨(specGeometricFrobenius k₀ ^ n).asIso.hom.base w, ?_⟩
    change ((Spec.map (CommRingCat.ofHom (algebraMap k₀ k'))).geometricGaloisFrobenius ^
        n).asIso.hom.base
        (constantFieldFiberSection.base ((specGeometricFrobenius k₀ ^ n).asIso.inv.base
          ((specGeometricFrobenius k₀ ^ n).asIso.hom.base w))) =
      (geometricFiberToConstantFieldFiber c f hc).base ((f.geometricGaloisFrobenius ^
        n).asIso.hom.base
        ((geometricFiberComponentMap c f hc).base y))
    rw [iso_inv_hom_apply, hw]
    have := congrArg (fun g : c.geometricFiber ⟶ constantFieldFiber k₀ k' ↦ g y)
      (congrArg (geometricFiberComponentMap c f hc ≫ ·) h)
    simp only [Scheme.Hom.comp_apply] at this
    exact this
  · rintro ⟨u, hu⟩
    have hx : (f.geometricGaloisFrobenius ^ n).asIso.inv.base x ∈
        Set.range (geometricFiberComponentMap c f hc).base := by
      rw [hr, Set.mem_preimage, ← comp_base_apply', h', comp_base_apply', ← hu]
      refine ⟨(specGeometricFrobenius k₀ ^ n).asIso.inv.base u, ?_⟩
      change constantFieldFiberSection.base ((specGeometricFrobenius k₀ ^ n).asIso.inv.base u) =
        ((Spec.map (CommRingCat.ofHom (algebraMap k₀ k'))).geometricGaloisFrobenius ^
          n).asIso.inv.base
          (((Spec.map (CommRingCat.ofHom (algebraMap k₀ k'))).geometricGaloisFrobenius ^
            n).asIso.hom.base
              (constantFieldFiberSection.base ((specGeometricFrobenius k₀ ^ n).asIso.inv.base u)))
      rw [iso_inv_hom_apply]
    obtain ⟨y, hy⟩ := hx
    refine ⟨y, ?_⟩
    change (f.geometricGaloisFrobenius ^ n).asIso.hom.base
      ((geometricFiberComponentMap c f hc).base y) = x
    rw [hy, iso_hom_inv_apply]

/-- **The geometric fibre over `k₀` is the disjoint union of the Frobenius translates of the
component**: every point of `V ⊗_{k₀} k̄` lies in the range of exactly one of the open immersions
`θ ≫ Frⁿ`, `n < [k' : k₀]`. -/
theorem existsUnique_mem_range_geometricFiberComponentMap_comp (x : f.geometricFiber) :
    ∃! n : Fin (Module.finrank k₀ k'), x ∈
      Set.range (geometricFiberComponentMap c f hc ≫
        (f.geometricGaloisFrobenius ^ n.1).asIso.hom).base := by
  simp only [mem_range_geometricFiberComponentMap_comp_iff]
  exact existsUnique_mem_range_constantFieldFiberSectionPow _

end Finite

end AlgebraicGeometry.Scheme.Hom
