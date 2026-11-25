/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Selected descent stages along cofiltered limits with affine transitions

Let `{Dⱼ}` be a cofiltered inverse system of schemes with affine transition morphisms and limit
cone `c`. For a morphism `p : Y ⟶ Dᵢ` the base-changed system `Yⱼ = Y ×_{Dᵢ} Dⱼ` (for `j ≥ i`,
i.e. `j : Over i`) has limit `Y ×_{Dᵢ} lim Dⱼ`; this is `AlgebraicGeometry.baseChangeDiagram`,
`AlgebraicGeometry.baseChangeCone` and `AlgebraicGeometry.isLimitBaseChangeCone`.

In this file we select, by `Classical.choose`, the finite stages at which various objects over the
limit descend, and record their defining properties as separate lemmas. A stage `j ≥ i` is
an object `j : Over i`, and "for every `k ≥ j`" is expressed by quantifying over morphisms
`k ⟶ j` in `Over i`.

## Main definitions

- `AlgebraicGeometry.qcOpenDescentIndex`, `AlgebraicGeometry.qcOpenDescent`: a quasi-compact
  open of the limit descends to a quasi-compact open of a stage.
- `AlgebraicGeometry.baseChangeQcOpenDescentStage`, `AlgebraicGeometry.baseChangeQcOpenDescent`:
  the same for the base-changed system.
- `AlgebraicGeometry.baseChangeQcOpenEqStage`: two quasi-compact opens of `Y` with equal
  preimages in `Y ×_{Dᵢ} lim Dⱼ` have equal preimages in every `Yₖ` past this stage.
- `AlgebraicGeometry.morphismDescentStage`, `AlgebraicGeometry.morphismDescent`: a morphism
  between base changes of schemes of finite presentation descends to a finite stage.
- `AlgebraicGeometry.morphismEqStage`: two morphisms with equal base change to the limit have
  equal base changes past this stage.
- `AlgebraicGeometry.closedImmersionStage`: a finitely presented morphism whose base change to
  the limit is a closed immersion is a closed immersion past this stage.
- `AlgebraicGeometry.separatedDescentStage`: a separated finite-presentation model of a
  separated scheme of finite presentation over the limit.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} {c : Cone D} (hc : IsLimit c)
  [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]

section QcOpen

/-- The stage at which a quasi-compact open `V` of the limit descends to a quasi-compact open
`qcOpenDescent hc V hV`. -/
noncomputable def qcOpenDescentIndex (V : c.pt.Opens) (hV : IsCompact (V : Set c.pt)) : I :=
  (exists_preimage_eq D c hc V hV).choose

/-- A quasi-compact open of the stage `qcOpenDescentIndex hc V hV` whose preimage in the limit is
the quasi-compact open `V`. -/
noncomputable def qcOpenDescent (V : c.pt.Opens) (hV : IsCompact (V : Set c.pt)) :
    (D.obj (qcOpenDescentIndex hc V hV)).Opens :=
  (exists_preimage_eq D c hc V hV).choose_spec.choose

lemma isCompact_qcOpenDescent (V : c.pt.Opens) (hV : IsCompact (V : Set c.pt)) :
    IsCompact (qcOpenDescent hc V hV : Set (D.obj (qcOpenDescentIndex hc V hV))) :=
  (exists_preimage_eq D c hc V hV).choose_spec.choose_spec.1

@[simp]
lemma preimage_qcOpenDescent (V : c.pt.Opens) (hV : IsCompact (V : Set c.pt)) :
    c.π.app (qcOpenDescentIndex hc V hV) ⁻¹ᵁ qcOpenDescent hc V hV = V :=
  (exists_preimage_eq D c hc V hV).choose_spec.choose_spec.2

variable {i : I} {Y : Scheme.{u}} (p : Y ⟶ D.obj i)

/-- The selected stage `λ_W ≥ i` of the base-changed system `Yⱼ = Y ×_{Dᵢ} Dⱼ` to which a
quasi-compact open `W` of `Y ×_{Dᵢ} lim Dⱼ` descends. -/
noncomputable def baseChangeQcOpenDescentStage (W : (pullback p (c.π.app i)).Opens)
    (hW : IsCompact (W : Set ↥(pullback p (c.π.app i)))) : Over i :=
  qcOpenDescentIndex (isLimitBaseChangeCone D c p hc) W hW

/-- Finite-stage model of a quasi-compact open: for `p: Y ⟶ Dᵢ` and a quasi-compact open `W` of
`Y ×_{Dᵢ} lim Dⱼ`, this is a quasi-compact open `W_{λ_W}` of `Y_{λ_W} = Y ×_{Dᵢ} D_{λ_W}`, where
`λ_W = baseChangeQcOpenDescentStage hc p W hW`, whose preimage under the projection
`Y ×_{Dᵢ} lim Dⱼ ⟶ Y_{λ_W}` is `W`. -/
noncomputable def baseChangeQcOpenDescent (W : (pullback p (c.π.app i)).Opens)
    (hW : IsCompact (W : Set ↥(pullback p (c.π.app i)))) :
    (pullback p (D.map (baseChangeQcOpenDescentStage hc p W hW).hom)).Opens :=
  qcOpenDescent (isLimitBaseChangeCone D c p hc) W hW

/-- The finite-stage model `W_{λ_W}` of a quasi-compact open is quasi-compact. -/
lemma isCompact_baseChangeQcOpenDescent (W : (pullback p (c.π.app i)).Opens)
    (hW : IsCompact (W : Set ↥(pullback p (c.π.app i)))) :
    IsCompact (baseChangeQcOpenDescent hc p W hW :
      Set ↥(pullback p (D.map (baseChangeQcOpenDescentStage hc p W hW).hom))) :=
  isCompact_qcOpenDescent (isLimitBaseChangeCone D c p hc) W hW

/-- The preimage of the finite-stage model `W_{λ_W}` in `Y ×_{Dᵢ} lim Dⱼ` is `W`. -/
@[simp]
lemma preimage_baseChangeQcOpenDescent (W : (pullback p (c.π.app i)).Opens)
    (hW : IsCompact (W : Set ↥(pullback p (c.π.app i)))) :
    (baseChangeCone D c p).π.app (baseChangeQcOpenDescentStage hc p W hW) ⁻¹ᵁ
      baseChangeQcOpenDescent hc p W hW = W :=
  preimage_qcOpenDescent (isLimitBaseChangeCone D c p hc) W hW

include hc in
/-- Two quasi-compact opens of a stage with the same preimage in the limit have the same
preimages at every stage past some stage. -/
lemma exists_forall_map_preimage_eq {V V' : (D.obj i).Opens}
    (hV : IsCompact (V : Set (D.obj i))) (hV' : IsCompact (V' : Set (D.obj i)))
    (H : c.π.app i ⁻¹ᵁ V = c.π.app i ⁻¹ᵁ V') :
    ∃ j : Over i, ∀ (k : Over i) (_ : k ⟶ j), D.map k.hom ⁻¹ᵁ V = D.map k.hom ⁻¹ᵁ V' := by
  obtain ⟨j, f, hf⟩ := exists_map_preimage_eq_map_preimage D c hc hV hV' H
  refine ⟨Over.mk f, fun k g ↦ ?_⟩
  rw [← Over.w g, Functor.map_comp, Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage]
  exact congrArg (D.map g.left ⁻¹ᵁ ·) hf

include hc in
/-- Two quasi-compact opens of `Y` with the same preimage in `Y ×_{Dᵢ} lim Dⱼ` have the same
preimages in `Y ×_{Dᵢ} Dₖ` for every stage `k` past some stage. -/
lemma exists_forall_pullback_fst_preimage_eq {W₁ W₂ : Y.Opens} (hW₁ : IsCompact (W₁ : Set Y))
    (hW₂ : IsCompact (W₂ : Set Y))
    (H : pullback.fst p (c.π.app i) ⁻¹ᵁ W₁ = pullback.fst p (c.π.app i) ⁻¹ᵁ W₂) :
    ∃ j : Over i, ∀ (k : Over i) (_ : k ⟶ j),
      pullback.fst p (D.map k.hom) ⁻¹ᵁ W₁ = pullback.fst p (D.map k.hom) ⁻¹ᵁ W₂ := by
  have : QuasiCompact (pullback.fst p (D.map (Over.mk (𝟙 i)).hom)) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  obtain ⟨j, f, hf⟩ := exists_map_preimage_eq_map_preimage (baseChangeDiagram D p)
    (baseChangeCone D c p) (isLimitBaseChangeCone D c p hc) (i := Over.mk (𝟙 i))
    (U := pullback.fst p (D.map (Over.mk (𝟙 i)).hom) ⁻¹ᵁ W₁)
    (V := pullback.fst p (D.map (Over.mk (𝟙 i)).hom) ⁻¹ᵁ W₂)
    (QuasiCompact.isCompact_preimage _ W₁.2 hW₁) (QuasiCompact.isCompact_preimage _ W₂.2 hW₂)
    (by rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, baseChangeCone_π_app_fst, H])
  refine ⟨j, fun k g ↦ ?_⟩
  rw [← baseChangeDiagram_map_fst D p (g ≫ f), Functor.map_comp, Scheme.Hom.comp_preimage,
    Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage]
  exact congrArg ((baseChangeDiagram D p).map g ⁻¹ᵁ ·) hf

/-- Stage of equality for descended quasi-compact opens: for quasi-compact opens `W₁, W₂ ⊆ Y` (with
`p: Y ⟶ Dᵢ`) whose preimages in `Y ×_{Dᵢ} lim Dⱼ` agree, a selected stage `λ_{W₁ = W₂} ≥ i` past
which their preimages in `Y ×_{Dᵢ} Dₖ` agree. -/
noncomputable def baseChangeQcOpenEqStage {W₁ W₂ : Y.Opens} (hW₁ : IsCompact (W₁ : Set Y))
    (hW₂ : IsCompact (W₂ : Set Y))
    (H : pullback.fst p (c.π.app i) ⁻¹ᵁ W₁ = pullback.fst p (c.π.app i) ⁻¹ᵁ W₂) : Over i :=
  (exists_forall_pullback_fst_preimage_eq hc p hW₁ hW₂ H).choose

/-- Eventual equality of descended quasi-compact opens: for every stage `k ≥ λ_{W₁ = W₂}`, the
preimages of `W₁` and `W₂` in `Y ×_{Dᵢ} Dₖ` are equal. -/
lemma pullback_fst_preimage_eq_of_baseChangeQcOpenEqStage {W₁ W₂ : Y.Opens}
    (hW₁ : IsCompact (W₁ : Set Y)) (hW₂ : IsCompact (W₂ : Set Y))
    (H : pullback.fst p (c.π.app i) ⁻¹ᵁ W₁ = pullback.fst p (c.π.app i) ⁻¹ᵁ W₂)
    (k : Over i) (g : k ⟶ baseChangeQcOpenEqStage hc p hW₁ hW₂ H) :
    pullback.fst p (D.map k.hom) ⁻¹ᵁ W₁ = pullback.fst p (D.map k.hom) ⁻¹ᵁ W₂ :=
  (exists_forall_pullback_fst_preimage_eq hc p hW₁ hW₂ H).choose_spec k g

end QcOpen

section Morphism

variable [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] {i : I}
  {V W : Scheme.{u}} (pV : V ⟶ D.obj i) (pW : W ⟶ D.obj i)
  [LocallyOfFinitePresentation pV] [QuasiCompact pV] [QuasiSeparated pV]
  [LocallyOfFinitePresentation pW] [QuasiCompact pW] [QuasiSeparated pW]

include hc in
/-- A morphism `V ×_{Dᵢ} lim Dⱼ ⟶ W ×_{Dᵢ} lim Dⱼ` over `lim Dⱼ` between base changes of schemes
of finite presentation over `Dᵢ` is the base change of a morphism `V ×_{Dᵢ} Dⱼ ⟶ W ×_{Dᵢ} Dⱼ`
over `Dⱼ` for some stage `j ≥ i`. -/
theorem exists_baseChangeCone_π_app_comp_eq
    (φ : pullback pV (c.π.app i) ⟶ pullback pW (c.π.app i))
    (hφ : φ ≫ pullback.snd pW (c.π.app i) = pullback.snd pV (c.π.app i)) :
    ∃ (j : Over i) (φj : pullback pV (D.map j.hom) ⟶ pullback pW (D.map j.hom)),
      φj ≫ pullback.snd pW (D.map j.hom) = pullback.snd pV (D.map j.hom) ∧
        (baseChangeCone D c pV).π.app j ≫ φj = φ ≫ (baseChangeCone D c pW).π.app j := by
  obtain ⟨j, f, ψj, hψj, hψ⟩ := Scheme.exists_pullback_hom_of_isLimit hc pV pW
    (φ ≫ pullback.fst pW (c.π.app i)) (by
      rw [Category.assoc, pullback.condition, reassoc_of% hφ, pullback.condition])
  have key (j : Over i) (ψj : pullback pV (D.map j.hom) ⟶ W)
      (hψj : ψj ≫ pW = pullback.fst pV (D.map j.hom) ≫ pV)
      (hψ : (baseChangeCone D c pV).π.app j ≫ ψj = φ ≫ pullback.fst pW (c.π.app i)) :
      ∃ φj : pullback pV (D.map j.hom) ⟶ pullback pW (D.map j.hom),
        φj ≫ pullback.snd pW (D.map j.hom) = pullback.snd pV (D.map j.hom) ∧
          (baseChangeCone D c pV).π.app j ≫ φj = φ ≫ (baseChangeCone D c pW).π.app j := by
    refine ⟨pullback.lift ψj (pullback.snd pV (D.map j.hom))
      (by rw [hψj, pullback.condition]), pullback.lift_snd _ _ _, ?_⟩
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, pullback.lift_fst, baseChangeCone_π_app_fst, hψ]
    · rw [Category.assoc, Category.assoc, pullback.lift_snd, baseChangeCone_π_app_snd,
        baseChangeCone_π_app_snd, reassoc_of% hφ]
  exact ⟨Over.mk f, key (Over.mk f) ψj hψj hψ⟩

/-- The selected stage `λ_φ ≥ i` to which a morphism `φ : V ×_{Dᵢ} lim Dⱼ ⟶ W ×_{Dᵢ} lim Dⱼ` over
`lim Dⱼ` descends. -/
noncomputable def morphismDescentStage (φ : pullback pV (c.π.app i) ⟶ pullback pW (c.π.app i))
    (hφ : φ ≫ pullback.snd pW (c.π.app i) = pullback.snd pV (c.π.app i)) : Over i :=
  (exists_baseChangeCone_π_app_comp_eq hc pV pW φ hφ).choose

/-- Finite-stage model of a morphism: for schemes `pV: V ⟶ Dᵢ`, `pW: W ⟶ Dᵢ` of finite presentation
and a morphism `φ: V ×_{Dᵢ} lim Dⱼ ⟶ W ×_{Dᵢ} lim Dⱼ` over `lim Dⱼ`, this is a morphism
`φ_{λ_φ}: V ×_{Dᵢ} D_{λ_φ} ⟶ W ×_{Dᵢ} D_{λ_φ}` over `D_{λ_φ}`, where
`λ_φ = morphismDescentStage hc pV pW φ hφ`, whose base change to `lim Dⱼ` is `φ`. -/
noncomputable def morphismDescent (φ : pullback pV (c.π.app i) ⟶ pullback pW (c.π.app i))
    (hφ : φ ≫ pullback.snd pW (c.π.app i) = pullback.snd pV (c.π.app i)) :
    pullback pV (D.map (morphismDescentStage hc pV pW φ hφ).hom) ⟶
      pullback pW (D.map (morphismDescentStage hc pV pW φ hφ).hom) :=
  (exists_baseChangeCone_π_app_comp_eq hc pV pW φ hφ).choose_spec.choose

/-- The descended morphism `φ_{λ_φ}` is a morphism over `D_{λ_φ}`. -/
@[reassoc (attr := simp)]
lemma morphismDescent_snd (φ : pullback pV (c.π.app i) ⟶ pullback pW (c.π.app i))
    (hφ : φ ≫ pullback.snd pW (c.π.app i) = pullback.snd pV (c.π.app i)) :
    morphismDescent hc pV pW φ hφ ≫
        pullback.snd pW (D.map (morphismDescentStage hc pV pW φ hφ).hom) =
      pullback.snd pV (D.map (morphismDescentStage hc pV pW φ hφ).hom) :=
  (exists_baseChangeCone_π_app_comp_eq hc pV pW φ hφ).choose_spec.choose_spec.1

/-- The base change of `φ_{λ_φ}` to `lim Dⱼ` is `φ`: the square formed by `φ`, `φ_{λ_φ}` and the
projections `V ×_{Dᵢ} lim Dⱼ ⟶ V ×_{Dᵢ} D_{λ_φ}`, `W ×_{Dᵢ} lim Dⱼ ⟶ W ×_{Dᵢ} D_{λ_φ}` commutes. -/
@[reassoc]
lemma baseChangeCone_π_app_comp_morphismDescent
    (φ : pullback pV (c.π.app i) ⟶ pullback pW (c.π.app i))
    (hφ : φ ≫ pullback.snd pW (c.π.app i) = pullback.snd pV (c.π.app i)) :
    (baseChangeCone D c pV).π.app (morphismDescentStage hc pV pW φ hφ) ≫
        morphismDescent hc pV pW φ hφ =
      φ ≫ (baseChangeCone D c pW).π.app (morphismDescentStage hc pV pW φ hφ) :=
  (exists_baseChangeCone_π_app_comp_eq hc pV pW φ hφ).choose_spec.choose_spec.2

include hc in
/-- Two morphisms `ψ χ : V ⟶ W` over `Dᵢ` of schemes of finite presentation whose base changes
to `lim Dⱼ` agree have equal base changes to `Dₖ` for every stage `k` past some stage. -/
theorem exists_forall_pullback_fst_comp_eq (ψ χ : V ⟶ W) (hψ : ψ ≫ pW = pV) (hχ : χ ≫ pW = pV)
    (h : pullback.fst pV (c.π.app i) ≫ ψ = pullback.fst pV (c.π.app i) ≫ χ) :
    ∃ j : Over i, ∀ (k : Over i) (_ : k ⟶ j),
      pullback.fst pV (D.map k.hom) ≫ ψ = pullback.fst pV (D.map k.hom) ≫ χ := by
  obtain ⟨j, f, hf⟩ := Scheme.exists_pullback_fst_comp_eq_of_isLimit hc pV pW ψ χ hψ hχ h
  refine ⟨Over.mk f, fun k g ↦ ?_⟩
  have hg := baseChangeDiagram_map_fst D pV g
  simp only [Over.mk_hom] at hg
  rw [← hg, Category.assoc, Category.assoc, hf]

/-- Stage of equality for two descended morphisms: for morphisms `ψ χ: V ⟶ W` over `Dᵢ` of schemes
of finite presentation whose base changes to `lim Dⱼ` agree, a selected stage `λ_{ψ = χ} ≥ i` past
which their base changes agree. -/
noncomputable def morphismEqStage (ψ χ : V ⟶ W) (hψ : ψ ≫ pW = pV) (hχ : χ ≫ pW = pV)
    (h : pullback.fst pV (c.π.app i) ≫ ψ = pullback.fst pV (c.π.app i) ≫ χ) : Over i :=
  (exists_forall_pullback_fst_comp_eq hc pV pW ψ χ hψ hχ h).choose

lemma pullback_fst_comp_eq_of_morphismEqStage (ψ χ : V ⟶ W) (hψ : ψ ≫ pW = pV)
    (hχ : χ ≫ pW = pV) (h : pullback.fst pV (c.π.app i) ≫ ψ = pullback.fst pV (c.π.app i) ≫ χ)
    (k : Over i) (g : k ⟶ morphismEqStage hc pV pW ψ χ hψ hχ h) :
    pullback.fst pV (D.map k.hom) ≫ ψ = pullback.fst pV (D.map k.hom) ≫ χ :=
  (exists_forall_pullback_fst_comp_eq hc pV pW ψ χ hψ hχ h).choose_spec k g

/-- Eventual equality of morphisms: for every stage `k ≥ λ_{ψ = χ}`, the base changes
`V ×_{Dᵢ} Dₖ ⟶ W ×_{Dᵢ} Dₖ` of `ψ` and `χ` are equal. -/
lemma pullback_map_eq_of_morphismEqStage (ψ χ : V ⟶ W) (hψ : ψ ≫ pW = pV)
    (hχ : χ ≫ pW = pV) (h : pullback.fst pV (c.π.app i) ≫ ψ = pullback.fst pV (c.π.app i) ≫ χ)
    (k : Over i) (g : k ⟶ morphismEqStage hc pV pW ψ χ hψ hχ h) :
    pullback.map pV (D.map k.hom) pW (D.map k.hom) ψ (𝟙 _) (𝟙 _) (by simp [hψ]) (by simp) =
      pullback.map pV (D.map k.hom) pW (D.map k.hom) χ (𝟙 _) (𝟙 _) (by simp [hχ])
        (by simp) := by
  apply pullback.hom_ext
  · simpa using pullback_fst_comp_eq_of_morphismEqStage hc pV pW ψ χ hψ hχ h k g
  · simp

end Morphism

section ClosedImmersion

variable {k : I} {Z Y : Over (D.obj k)} (γ : Z ⟶ Y)
  [LocallyOfFinitePresentation γ.left] [QuasiCompact γ.left] [QuasiSeparated γ.left]
  [CompactSpace Y.left] [QuasiSeparatedSpace Y.left]

/-- Stage at which a finite-presentation map is closed: for a morphism `γ: Z ⟶ Y` of finite
presentation between schemes over the stage `D_k`, with `Y` quasi-compact and quasi-separated, whose
base change to `lim Dⱼ` is a closed immersion, this is the index `μ_cl(γ) ≥ k` of the witness given
by `AlgebraicGeometry.Scheme.exists_isClosedImmersion_overPullbackMap`. -/
noncomputable def closedImmersionStage
    (hS : IsClosedImmersion ((Over.pullback (c.π.app k)).map γ).left) : Over k :=
  Over.mk (Scheme.exists_isClosedImmersion_overPullbackMap hc γ hS).choose_spec.choose

/-- A finite-presentation closed immersion descends at the selected stage: for every stage
`μ ≥ μ_cl(γ)`, the base change of `γ` to `D_μ` is a closed immersion. -/
lemma isClosedImmersion_of_closedImmersionStage
    (hS : IsClosedImmersion ((Over.pullback (c.π.app k)).map γ).left) (j : Over k)
    (g : j ⟶ closedImmersionStage hc γ hS) :
    IsClosedImmersion ((Over.pullback (D.map j.hom)).map γ).left := by
  rw [← Over.w g]
  exact (Scheme.exists_isClosedImmersion_overPullbackMap hc γ hS).choose_spec.choose_spec g.left

end ClosedImmersion

section Separated

variable {k : I} [CompactSpace (D.obj k)] [QuasiSeparatedSpace (D.obj k)] {Y : Scheme.{u}}
  {p : Y ⟶ D.obj k} [LocallyOfFinitePresentation p] [QuasiCompact p] [QuasiSeparated p]
  {X : Scheme.{u}} {g : X ⟶ c.pt} [IsSeparated g] {h : X ⟶ Y}

/-- Separated stage of a descended finite-presentation model: let `g: X ⟶ lim Dⱼ` be separated, and
let `p: Y ⟶ D_k` be a finite-presentation model of it, i.e. `H: IsPullback h g p (c.π.app k)`. This
is the index `λ_sep ≥ k` of the witness given by
`AlgebraicGeometry.Scheme.exists_isSeparated_pullback_snd`; the separated model is
`X^sep = Y ×_{D_k} D_{λ_sep}` (`AlgebraicGeometry.separatedDescentModel`). -/
noncomputable def separatedDescentStage (H : IsPullback h g p (c.π.app k)) : Over k :=
  Over.mk (Scheme.exists_isSeparated_pullback_snd hc H).choose_spec.choose

/-- The separated finite-presentation model `X^sep = Y ×_{D_k} D_{λ_sep}` over `D_{λ_sep}`. -/
noncomputable abbrev separatedDescentModel (H : IsPullback h g p (c.π.app k)) :
    pullback p (D.map (separatedDescentStage hc H).hom) ⟶ D.obj (separatedDescentStage hc H).left :=
  pullback.snd p (D.map (separatedDescentStage hc H).hom)

/-- The model at the selected stage `λ_sep` is separated. -/
instance isSeparated_separatedDescentModel (H : IsPullback h g p (c.π.app k)) :
    IsSeparated (separatedDescentModel hc H) :=
  (Scheme.exists_isSeparated_pullback_snd hc H).choose_spec.choose_spec

/-- The model at the selected stage `λ_sep` is locally of finite presentation. -/
instance locallyOfFinitePresentation_separatedDescentModel (H : IsPullback h g p (c.π.app k)) :
    LocallyOfFinitePresentation (separatedDescentModel hc H) :=
  MorphismProperty.pullback_snd _ _ inferInstance

/-- The model at the selected stage `λ_sep` is quasi-compact. -/
instance quasiCompact_separatedDescentModel (H : IsPullback h g p (c.π.app k)) :
    QuasiCompact (separatedDescentModel hc H) :=
  MorphismProperty.pullback_snd _ _ inferInstance

/-- The base change of the model at the selected stage `λ_sep` to `lim Dⱼ` is `g : X ⟶ lim Dⱼ`. -/
lemma isPullback_separatedDescentModel (H : IsPullback h g p (c.π.app k)) :
    IsPullback (isPullbackLift D c (separatedDescentStage hc H).hom H) g
      (separatedDescentModel hc H) (c.π.app (separatedDescentStage hc H).left) :=
  isPullback_isPullbackLift _ H

end Separated

end AlgebraicGeometry
