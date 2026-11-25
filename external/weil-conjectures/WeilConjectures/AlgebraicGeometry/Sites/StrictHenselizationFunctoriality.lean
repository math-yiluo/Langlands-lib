/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
public import WeilConjectures.RingTheory.Henselian.EtaleRetraction

/-!
# Functoriality of the strict henselization

Let `g : T ⟶ S` be a morphism of schemes and `t : Spec Ω ⟶ T` a geometric point, so that
`t ≫ g` is a geometric point of `S`. We construct the local homomorphism
`h : 𝒪^{sh}_{S, t ≫ g} ⟶ 𝒪^{sh}_{T, t}` of strict henselizations
(`AlgebraicGeometry.Scheme.strictHenselizationMap g t`): it is the unique ring homomorphism such
that `Spec h` is compatible with the structure morphisms to `S` and `T` and `h` is compatible with
the evaluations at the geometric points. For an affine pointed étale neighbourhood `(V, v)` of
`t ≫ g`, the composite `S_(t) ⟶ T_(t ≫ g) ⟶ V` is the unique morphism `T_(t) ⟶ V` over `S`
through which `v` factors (`strictLocalizationLift`); in particular it agrees with
`T_(t) ⟶ W ⟶ V` for every affine pointed étale neighbourhood `(W, w)` of `t` mapping to `V`.

The key input is `AlgebraicGeometry.existsUnique_lift_of_etale`: morphisms from the spectrum of a
strictly henselian local ring `R` lift uniquely along étale morphisms through prescribed points
over the closed point.

## Main definitions

- `AlgebraicGeometry.Scheme.strictLocalizationLift g t x`: the morphism `T_(t) ⟶ V` over `S`.
- `AlgebraicGeometry.Scheme.strictHenselizationMap g t`: the map `𝒪^{sh}_{S,t ≫ g} ⟶ 𝒪^{sh}_{T,t}`.

## Main results

- `AlgebraicGeometry.Scheme.existsUnique_strictHenselizationMap`: the strict henselization map
  is the unique local homomorphism compatible with the structure morphisms and the points.
- `AlgebraicGeometry.Scheme.strictLocalizationCone_π_app_comp_eq`: compatibility of the strict
  henselization map with pointed étale neighbourhoods.

## References

- Stacks Project, Lemma 59.33.1 and Definition 59.33.4,
  <https://stacks.math.columbia.edu/tag/04HX>, <https://stacks.math.columbia.edu/tag/03PS>
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite IsLocalRing

namespace AlgebraicGeometry

/-- For a ring map `e : R ⟶ K` from a local ring to a field with kernel the maximal ideal,
`Spec e` maps the point of `Spec K` to the closed point. -/
lemma spec_map_apply_eq_closedPoint {R : CommRingCat.{u}} [IsLocalRing R] {K : Type u} [Field K]
    (e : R ⟶ CommRingCat.of K) (he : RingHom.ker e.hom = maximalIdeal R)
    (x : Spec (.of K)) : Spec.map e x = closedPoint R := by
  rw [Spec.map_apply]
  apply PrimeSpectrum.ext
  have hx : x.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
  rw [PrimeSpectrum.comap_asIdeal, hx, ← RingHom.ker_eq_comap_bot, he]
  rfl

/-- **Sections of étale morphisms over a strictly henselian local ring.** Let `R` be a strictly
henselian local ring, `e: R ⟶ K` a ring map to a field with kernel the maximal ideal,
`p: X ⟶ Spec R` an étale morphism and `μ: Spec K ⟶ X` a lift of `Spec e` along `p`. Then `p`
has exactly one section `σ` with `Spec e ≫ σ = μ`. -/
theorem existsUnique_section_of_etale {R : CommRingCat.{u}} [IsStrictlyHenselianLocalRing R]
    {K : Type u} [Field K] (e : R ⟶ CommRingCat.of K)
    (he : RingHom.ker e.hom = maximalIdeal R) {X : Scheme.{u}} (p : X ⟶ Spec R) [Etale p]
    (μ : Spec (.of K) ⟶ X) (hμ : μ ≫ p = Spec.map e) :
    ∃! σ : Spec R ⟶ X, σ ≫ p = 𝟙 _ ∧ Spec.map e ≫ σ = μ := by
  obtain ⟨x⟩ : Nonempty (Spec (.of K)) := inferInstance
  obtain ⟨D, j, _, hx, -⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (x := μ x) (U := ⊤) (by simp)
  have hμj : Set.range μ ⊆ Set.range j := by
    rintro _ ⟨a, rfl⟩
    rwa [Subsingleton.elim a x]
  let μ' := IsOpenImmersion.lift j μ hμj
  have hμ' : μ' ≫ j = μ := IsOpenImmersion.lift_fac j μ hμj
  let φ₀ : R ⟶ D := Spec.preimage (j ≫ p)
  have hφ₀ : Spec.map φ₀ = j ≫ p := Spec.map_preimage _
  let : Algebra R D := φ₀.hom.toAlgebra
  have : Algebra.Etale R D := by
    have : Etale (Spec.map φ₀) := by rw [hφ₀]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @Etale)).mp this
  let χ₀ : D ⟶ CommRingCat.of K := Spec.preimage μ'
  have hχ₀ : Spec.map χ₀ = μ' := Spec.map_preimage _
  let : Algebra R K := e.hom.toAlgebra
  have hφχ : φ₀ ≫ χ₀ = e := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ₀, hχ₀, ← Category.assoc, hμ', hμ]
  let χ : D →ₐ[R] K := { χ₀.hom with commutes' r := congr(($hφχ).hom r) }
  obtain ⟨τ, hτ, hτu⟩ := IsStrictlyHenselianLocalRing.existsUnique_algHom_comp_eq he χ
  -- every section through `μ` is `Spec τ' ≫ j` for an `R`-algebra map `τ'` lifting `χ`
  have key (σ : Spec R ⟶ X) (h₁ : σ ≫ p = 𝟙 _) (h₂ : Spec.map e ≫ σ = μ) :
      σ = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ j := by
    have hσj : Set.range σ ⊆ Set.range j := by
      rintro _ ⟨y, rfl⟩
      refine ((specializes_closedPoint y).map σ.continuous).mem_open
        j.isOpenEmbedding.isOpen_range ?_
      rw [← spec_map_apply_eq_closedPoint e he x, ← Scheme.Hom.comp_apply, h₂]
      exact hx
    let σ' := IsOpenImmersion.lift j σ hσj
    have hσ' : σ' ≫ j = σ := IsOpenImmersion.lift_fac j σ hσj
    let τ₀ : D ⟶ R := Spec.preimage σ'
    have hτ₀ : Spec.map τ₀ = σ' := Spec.map_preimage _
    have h₁' : φ₀ ≫ τ₀ = 𝟙 _ := by
      apply Spec.map_injective
      rw [Spec.map_comp, hφ₀, hτ₀, ← Category.assoc, hσ', h₁, Spec.map_id]
    have h₂' : τ₀ ≫ e = χ₀ := by
      apply Spec.map_injective
      rw [Spec.map_comp, hτ₀, hχ₀, ← cancel_mono j, Category.assoc, hσ', h₂, hμ']
    let τ' : D →ₐ[R] R := { τ₀.hom with commutes' r := congr(($h₁').hom r) }
    have : τ' = τ := hτu τ' (AlgHom.ext fun d ↦ congr(($h₂').hom d))
    rw [← hσ', ← hτ₀, ← this]
    rfl
  refine ⟨Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ j, ⟨?_, ?_⟩, fun σ ⟨h₁, h₂⟩ ↦ key σ h₁ h₂⟩
  · rw [Category.assoc, ← hφ₀, ← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext r
    exact τ.commutes r
  · rw [← Category.assoc, ← Spec.map_comp, ← hμ', ← hχ₀]
    congr 2
    ext d
    exact congr($hτ d)

/-- **Lifting along étale morphisms over a strictly henselian local ring.** Let `R` be a strictly
henselian local ring, `e: R ⟶ K` a ring map to a field with kernel the maximal ideal, `f: V ⟶ S`
an étale morphism, `ψ: Spec R ⟶ S` a morphism and `v: Spec K ⟶ V` a lift of
`Spec e ≫ ψ` along `f`. Then there is exactly one `φ: Spec R ⟶ V` with `φ ≫ f = ψ` and
`Spec e ≫ φ = v`. -/
theorem existsUnique_lift_of_etale {R : CommRingCat.{u}} [IsStrictlyHenselianLocalRing R]
    {K : Type u} [Field K] (e : R ⟶ CommRingCat.of K)
    (he : RingHom.ker e.hom = maximalIdeal R) {S V : Scheme.{u}} (f : V ⟶ S) [Etale f]
    (ψ : Spec R ⟶ S) (v : Spec (.of K) ⟶ V) (hv : v ≫ f = Spec.map e ≫ ψ) :
    ∃! φ : Spec R ⟶ V, φ ≫ f = ψ ∧ Spec.map e ≫ φ = v := by
  obtain ⟨σ, ⟨hσ₁, hσ₂⟩, hσu⟩ := existsUnique_section_of_etale e he (pullback.snd f ψ)
    (pullback.lift v (Spec.map e) hv) (pullback.lift_snd _ _ _)
  refine ⟨σ ≫ pullback.fst f ψ, ⟨?_, ?_⟩, fun φ ⟨h₁, h₂⟩ ↦ ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hσ₁, Category.id_comp]
  · rw [← Category.assoc, hσ₂, pullback.lift_fst]
  · have := hσu (pullback.lift φ (𝟙 _) (by rw [h₁, Category.id_comp]))
      ⟨pullback.lift_snd _ _ _, pullback.hom_ext (by simp [h₂]) (by simp)⟩
    rw [← this, pullback.lift_fst]

namespace Scheme

variable {S T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (g : T ⟶ S)
  (t : Spec (.of Ω) ⟶ T)

instance (s : Spec (.of Ω) ⟶ S) : IsStrictlyHenselianLocalRing (strictHenselization s) :=
  ⟨inferInstance⟩

lemma strictLocalizationLift_aux (x : AffinePointedEtaleNeighborhood (t ≫ g)) :
    ∃! φ : strictLocalization t ⟶ x.obj.1.left,
      φ ≫ x.obj.1.hom = strictLocalizationToBase t ≫ g ∧
        Spec.map (strictHenselizationEval t) ≫ φ = x.obj.2.left := by
  have : Etale x.obj.1.hom := x.obj.1.prop
  refine existsUnique_lift_of_etale (strictHenselizationEval t)
    (maximalIdeal_strictHenselization (s := t)).symm _ _ _ ?_
  refine (CategoryTheory.Over.w x.obj.2).trans ?_
  rw [← Category.assoc, spec_map_strictHenselizationEval_comp_strictLocalizationToBase]
  rfl

/-- For an affine pointed étale neighbourhood `(V, v)` of `t ≫ g`, the unique morphism
`T_(t) ⟶ V` over `S` (via `T_(t) ⟶ T ⟶ S`) through which `v` factors as
`Spec Ω ⟶ T_(t) ⟶ V`. -/
noncomputable def strictLocalizationLift (x : AffinePointedEtaleNeighborhood (t ≫ g)) :
    strictLocalization t ⟶ x.obj.1.left :=
  (strictLocalizationLift_aux g t x).exists.choose

@[reassoc]
lemma strictLocalizationLift_comp_hom (x : AffinePointedEtaleNeighborhood (t ≫ g)) :
    strictLocalizationLift g t x ≫ x.obj.1.hom = strictLocalizationToBase t ≫ g :=
  (strictLocalizationLift_aux g t x).exists.choose_spec.1

@[reassoc]
lemma spec_map_strictHenselizationEval_comp_strictLocalizationLift
    (x : AffinePointedEtaleNeighborhood (t ≫ g)) :
    Spec.map (strictHenselizationEval t) ≫ strictLocalizationLift g t x = x.obj.2.left :=
  (strictLocalizationLift_aux g t x).exists.choose_spec.2

/-- Uniqueness of `strictLocalizationLift`. -/
lemma eq_strictLocalizationLift (x : AffinePointedEtaleNeighborhood (t ≫ g))
    (φ : strictLocalization t ⟶ x.obj.1.left)
    (h₁ : φ ≫ x.obj.1.hom = strictLocalizationToBase t ≫ g)
    (h₂ : Spec.map (strictHenselizationEval t) ≫ φ = x.obj.2.left) :
    φ = strictLocalizationLift g t x :=
  (strictLocalizationLift_aux g t x).unique ⟨h₁, h₂⟩
    ⟨strictLocalizationLift_comp_hom g t x,
      spec_map_strictHenselizationEval_comp_strictLocalizationLift g t x⟩

/-- The local homomorphism `𝒪^{sh}_{S,t ≫ g} ⟶ 𝒪^{sh}_{T,t}` of strict henselizations induced
by `g: T ⟶ S`. -/
noncomputable def strictHenselizationMap :
    strictHenselization (t ≫ g) ⟶ strictHenselization t :=
  colimit.desc (strictHenselizationDiagram (t ≫ g))
    { pt := strictHenselization t
      ι :=
        { app x := Scheme.Γ.map (strictLocalizationLift g t x.unop).op ≫
            (Scheme.ΓSpecIso (strictHenselization t)).hom
          naturality x y f := by
            have h : strictLocalizationLift g t y.unop ≫ f.unop.hom.1.left =
                strictLocalizationLift g t x.unop := by
              refine eq_strictLocalizationLift g t _ _ ?_ ?_
              · rw [Category.assoc, ← strictLocalizationLift_comp_hom g t y.unop]
                congr 1
                exact f.unop.hom.1.w.trans (Category.comp_id _)
              · rw [spec_map_strictHenselizationEval_comp_strictLocalizationLift_assoc]
                exact congrArg CommaMorphism.left f.unop.hom.2
            change Scheme.Γ.map f.unop.hom.1.left.op ≫ Scheme.Γ.map _ ≫ _ =
              (Scheme.Γ.map _ ≫ _) ≫ 𝟙 _
            rw [Category.comp_id, ← h, op_comp, Scheme.Γ.map_comp, Category.assoc] } }


/-- Ring homomorphisms out of the strict henselization are determined by the composites of their
spectra with the legs of the strict localization cone. -/
lemma strictHenselization_hom_ext {s : Spec (.of Ω) ⟶ S} {R : CommRingCat.{u}}
    {f₁ f₂ : strictHenselization s ⟶ R}
    (h : ∀ x, Spec.map f₁ ≫ (strictLocalizationCone s).π.app x =
      Spec.map f₂ ≫ (strictLocalizationCone s).π.app x) : f₁ = f₂ :=
  Spec.map_injective ((isLimitStrictLocalizationCone s).hom_ext h)

set_option backward.isDefEq.respectTransparency false in
/-- The composite `T_(t) ⟶ S_(t ≫ g) ⟶ V` is `strictLocalizationLift g t x`. -/
@[reassoc]
lemma spec_map_strictHenselizationMap_comp_strictLocalizationCone_π_app
    (x : AffinePointedEtaleNeighborhood (t ≫ g)) :
    Spec.map (strictHenselizationMap g t) ≫ (strictLocalizationCone (t ≫ g)).π.app x =
      strictLocalizationLift g t x := by
  have hy : Spec.map (Scheme.Γ.map (strictLocalizationLift g t x).op ≫
      (Scheme.ΓSpecIso (strictHenselization t)).hom) =
      strictLocalizationLift g t x ≫ x.obj.1.left.toSpecΓ := by
    rw [Spec.map_comp, SpecMap_ΓSpecIso_hom, Scheme.Γ_map_op, Scheme.toSpecΓ_naturality]
  rw [strictLocalizationCone_π_app, ← Spec.map_comp_assoc, strictHenselizationMap,
    colimit.ι_desc]
  change Spec.map (Scheme.Γ.map (strictLocalizationLift g t x).op ≫
      (Scheme.ΓSpecIso (strictHenselization t)).hom) ≫ inv x.obj.1.left.toSpecΓ = _
  rw [hy, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-- `Spec` of the strict henselization map is compatible with the structure morphisms:
`j_S ∘ Spec h = g ∘ j_T`. -/
@[reassoc]
lemma spec_map_strictHenselizationMap_comp_strictLocalizationToBase :
    Spec.map (strictHenselizationMap g t) ≫ strictLocalizationToBase (t ≫ g) =
      strictLocalizationToBase t ≫ g := by
  obtain ⟨x⟩ := IsCofiltered.nonempty (C := AffinePointedEtaleNeighborhood (t ≫ g))
  rw [← strictLocalizationCone_π_app_hom (t ≫ g) x,
    spec_map_strictHenselizationMap_comp_strictLocalizationCone_π_app_assoc,
    strictLocalizationLift_comp_hom]

/-- The strict henselization map is compatible with the evaluations at the geometric points,
i.e. it induces the inclusion of residue fields inside `Ω`. -/
@[reassoc (attr := simp)]
lemma strictHenselizationMap_comp_strictHenselizationEval :
    strictHenselizationMap g t ≫ strictHenselizationEval t = strictHenselizationEval (t ≫ g) := by
  refine strictHenselization_hom_ext fun x ↦ ?_
  rw [Spec.map_comp, Category.assoc,
    spec_map_strictHenselizationMap_comp_strictLocalizationCone_π_app,
    spec_map_strictHenselizationEval_comp_strictLocalizationLift,
    spec_map_strictHenselizationEval_comp_strictLocalizationCone_π_app]

/-- The strict henselization map is a local homomorphism. -/
instance isLocalHom_strictHenselizationMap : IsLocalHom (strictHenselizationMap g t).hom := by
  refine ⟨fun a ha ↦ ?_⟩
  rw [isUnit_iff_strictHenselizationEval_ne_zero] at ha ⊢
  rwa [← CommRingCat.comp_apply, strictHenselizationMap_comp_strictHenselizationEval] at ha

/-- Uniqueness of the strict henselization map: a ring homomorphism compatible with the structure
morphisms and the evaluations at the geometric points is `strictHenselizationMap g t`. -/
lemma eq_strictHenselizationMap (h : strictHenselization (t ≫ g) ⟶ strictHenselization t)
    (h₁ : Spec.map h ≫ strictLocalizationToBase (t ≫ g) = strictLocalizationToBase t ≫ g)
    (h₂ : h ≫ strictHenselizationEval t = strictHenselizationEval (t ≫ g)) :
    h = strictHenselizationMap g t := by
  refine strictHenselization_hom_ext fun x ↦ ?_
  rw [spec_map_strictHenselizationMap_comp_strictLocalizationCone_π_app]
  refine eq_strictLocalizationLift g t _ _ ?_ ?_
  · rw [Category.assoc, strictLocalizationCone_π_app_hom, h₁]
  · rw [← Category.assoc, ← Spec.map_comp, h₂,
      spec_map_strictHenselizationEval_comp_strictLocalizationCone_π_app]

/-- **Functoriality of the strict henselization**: the strict henselization map is the
unique (local) ring homomorphism `h: 𝒪^{sh}_{S,t ≫ g} ⟶ 𝒪^{sh}_{T,t}` with
`j_S ∘ Spec h = g ∘ j_T` inducing the inclusion of residue fields inside `Ω`. -/
theorem existsUnique_strictHenselizationMap :
    ∃! h : strictHenselization (t ≫ g) ⟶ strictHenselization t,
      IsLocalHom h.hom ∧
      Spec.map h ≫ strictLocalizationToBase (t ≫ g) = strictLocalizationToBase t ≫ g ∧
      h ≫ strictHenselizationEval t = strictHenselizationEval (t ≫ g) :=
  ⟨strictHenselizationMap g t, ⟨inferInstance,
    spec_map_strictHenselizationMap_comp_strictLocalizationToBase g t,
    strictHenselizationMap_comp_strictHenselizationEval g t⟩,
    fun h ⟨_, h₁, h₂⟩ ↦ eq_strictHenselizationMap g t h h₁ h₂⟩

/-- **Compatibility of the strict henselization map with neighbourhoods**: if `(V, v)`
is an affine pointed étale neighbourhood of `t ≫ g`, `(W, w)` one of `t` and `w: W ⟶ V` is
compatible with the structure morphisms and the points, then `T_(t) ⟶ W ⟶ V` equals
`T_(t) ⟶ S_(t ≫ g) ⟶ V`. -/
theorem strictLocalizationCone_π_app_comp_eq (x : AffinePointedEtaleNeighborhood (t ≫ g))
    (y : AffinePointedEtaleNeighborhood t) (w : y.obj.1.left ⟶ x.obj.1.left)
    (hw : w ≫ x.obj.1.hom = y.obj.1.hom ≫ g) (hpt : y.obj.2.left ≫ w = x.obj.2.left) :
    (strictLocalizationCone t).π.app y ≫ w =
      Spec.map (strictHenselizationMap g t) ≫ (strictLocalizationCone (t ≫ g)).π.app x := by
  rw [spec_map_strictHenselizationMap_comp_strictLocalizationCone_π_app]
  refine eq_strictLocalizationLift g t _ _ ?_ ?_
  · rw [Category.assoc, hw, strictLocalizationCone_π_app_hom_assoc]
  · rw [spec_map_strictHenselizationEval_comp_strictLocalizationCone_π_app_assoc, hpt]

end Scheme

end AlgebraicGeometry
