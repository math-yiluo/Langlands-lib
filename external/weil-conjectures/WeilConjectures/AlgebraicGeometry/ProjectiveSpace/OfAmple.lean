/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.AffineImmersion
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfInvertible

/-!
# Immersions into projective space from an ample invertible module

Let `X` be a scheme separated and of finite type over an affine scheme `S`, let `ℒ` be an
invertible `𝒪_X`-module and let `s₁, …, sᵣ` be global sections of `ℒ` whose non-vanishing loci
`X_{sᵢ}` are affine and cover `X`. Then `X` admits an immersion over `S` into a projective space
`ℙ(n; S)` with finitely many homogeneous coordinates (compare Stacks 01VS).

Each `Γ(X_{sᵢ}, 𝒪_X)` is generated over `Γ(S, 𝒪_S)` by finitely many sections `a`, and clearing
denominators (`AlgebraicGeometry.Scheme.Modules.exists_tensorPowSection_eq_restrict`) extends
every `a ⊗ sᵢ^{⊗ m}` to a global section of `ℒ^{⊗ m}` for one common `m ≥ 1`. The sections
`sᵢ^{⊗ m}` and these extensions define a morphism `φ : X ⟶ ℙ(n; S)`
(`AlgebraicGeometry.ProjectiveSpace.homOfIsFreeGenerator`) with `φ⁻¹ D₊(T_{sᵢ}) = X_{sᵢ}`, and on
`X_{sᵢ}` it is the closed immersion into the affine chart classified by the generators `a`.

## Main statements

- `AlgebraicGeometry.exists_isImmersion_projectiveSpace_of_isAffineOpen`: the immersion.
- `AlgebraicGeometry.Scheme.Modules.exists_isAffineOpen_compl_support_zeroLocus_of_isAffineHom`:
  families of sections with affine non-vanishing loci covering the target pull back along
  affine morphisms.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

open Scheme.Modules

section Auxiliary

variable {X : Scheme.{u}}

/-- Every section of a module over the empty open is a free generator. -/
lemma Scheme.Modules.isFreeGenerator_bot {M : X.Modules} (e : Γ(M, ⊥)) : IsFreeGenerator e :=
  isFreeGenerator_of_mem e (S := ⊥) (fun _ hx ↦ hx.elim) fun _ _ h ↦ h.elim

/-- If a power `σ^{⊗ m}(1)`, `m ≠ 0`, of a section `σ` of an invertible module is a free
generator on `W`, then `W` lies in the non-vanishing locus of `σ`. -/
lemma Scheme.Modules.le_compl_support_zeroLocus_of_isFreeGenerator {L : X.Modules}
    [SheafOfModules.IsInvertible.{u, u, u} L] (σ : 𝟙_ X.Modules ⟶ L) {m : ℕ} (hm : m ≠ 0)
    {W : X.Opens} (hW : IsFreeGenerator (tensorPowSectionOne σ m W)) :
    W ≤ (Hom.zeroLocus σ).support.compl := by
  intro x hx
  obtain ⟨V, hxV, hVW, e, he⟩ := exists_isFreeGenerator L hx
  obtain ⟨E, hE, hσE⟩ := exists_tensorPowSectionOne_eq_pow_smul σ he
    (he.coeff_smul (σ.app V.1 (unitSectionsEquiv _ 1))).symm m
  have hG := hW.map hVW
  rw [presheaf_map_tensorPowSectionOne, hσE] at hG
  obtain ⟨w, hw⟩ := hE.exists_unit_smul_eq hG
  have hc : IsUnit (he.coeff (σ.app V.1 (unitSectionsEquiv _ 1))) := by
    rw [← isUnit_pow_iff hm, hE.smul_left_injective hw]
    exact w.isUnit
  have h := basicOpen_coeff_eq σ V he
  rw [X.basicOpen_of_isUnit hc] at h
  exact (h.le hxV).2

/-- If a global section `v` of `ℒ^{⊗ k}` restricts on `U` to `a • σ^{⊗ k}(1)`, then for every
`l ≥ k` some global section of `ℒ^{⊗ l}` restricts on `U` to `a • σ^{⊗ l}(1)`: multiply by
`σ^{⊗ (l - k)}`. -/
lemma Scheme.Modules.exists_restrict_eq_smul_tensorPowSectionOne_of_le {L : X.Modules}
    (σ : 𝟙_ X.Modules ⟶ L) {U : X.Opens} {a : Γ(X, U)} {k : ℕ} (v : Γ(L.tensorPow k, ⊤))
    (hv : (L.tensorPow k).presheaf.map (homOfLE le_top).op v = a • tensorPowSectionOne σ k U)
    {l : ℕ} (hkl : k ≤ l) :
    ∃ v' : Γ(L.tensorPow l, ⊤),
      (L.tensorPow l).presheaf.map (homOfLE le_top).op v' = a • tensorPowSectionOne σ l U := by
  induction l, hkl using Nat.le_induction with
  | base => exact ⟨v, hv⟩
  | succ l _ ih =>
    obtain ⟨v', hv'⟩ := ih
    refine ⟨tmulSection (σ.app ⊤ (unitSectionsEquiv ⊤ 1)) v', (tmulSection_map le_top _ _).trans ?_⟩
    rw [hv', ← Hom.app_presheaf_map, presheaf_map_unitSectionsEquiv, map_one, tmulSection_smul,
      tensorPowSectionOne_succ]

/-- **Clearing denominators for functions.** Let `X` be quasi-compact and separated over an
affine scheme, `ℒ` invertible and `σ` a global section of `ℒ`. Every function `a` on the
non-vanishing locus `X_σ` becomes, after multiplication by a power `σ^{⊗ k}`, the restriction of
a global section of `ℒ^{⊗ k}`. -/
lemma Scheme.Modules.exists_restrict_eq_smul_tensorPowSectionOne {S : Scheme.{u}} (f : X ⟶ S)
    [IsSeparated f] [IsAffine S] [CompactSpace X] (L : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u} L] (σ : 𝟙_ X.Modules ⟶ L)
    (a : Γ(X, (Hom.zeroLocus σ).support.compl)) :
    ∃ (k : ℕ) (v : Γ(L.tensorPow k, ⊤)),
      (L.tensorPow k).presheaf.map (homOfLE (le_top : (Hom.zeroLocus σ).support.compl ≤ ⊤)).op
        v = a • tensorPowSectionOne σ k (Hom.zeroLocus σ).support.compl := by
  have : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) (𝟙_ X.Modules) :=
    SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
  obtain ⟨k, u, hu⟩ :=
    exists_tensorPowSection_eq_restrict f L σ (𝟙_ X.Modules) (unitSectionsEquiv _ a)
  refine ⟨k, (λ_ (L.tensorPow k)).hom.app ⊤ u, ?_⟩
  rw [← Hom.app_presheaf_map, hu, rightUnitor_inv_comp_whiskerLeft_app,
    leftUnitor_hom_app_tmulSection]

/-- Variant of `exists_finite_subring_closure_divBasicOpen_eq_top`: generation by quotients with
denominator `1` transports to generation by quotients with any denominator `b = 1`. -/
private lemma subring_closure_divBasicOpen_eq_top_of_eq_one {V S : Scheme.{u}} (g : V ⟶ S)
    (W : S.Opens) {b : Γ(V, ⊤)} (hb : b = 1) {m : Type*} (t : m → Γ(V, ⊤))
    (hle : V.basicOpen b ≤ g ⁻¹ᵁ W) (hle₁ : V.basicOpen (1 : Γ(V, ⊤)) ≤ g ⁻¹ᵁ W)
    (h : Subring.closure (Set.range (g.resLE W (V.basicOpen 1) hle₁).appTop ∪
      Set.range fun μ ↦ V.divBasicOpen (t μ) 1) = ⊤) :
    Subring.closure (Set.range (g.resLE W (V.basicOpen b) hle).appTop ∪
      Set.range fun μ ↦ V.divBasicOpen (t μ) b) = ⊤ := by
  subst hb
  exact h

end Auxiliary

/-- **An ample family of sections gives an immersion into projective space.** Let `X` be
separated and locally of finite type over an affine scheme `S`, let `ℒ` be an invertible
`𝒪_X`-module and let `s i`, for `i` in a finite type `ι`, be global sections of `ℒ` whose
non-vanishing loci `X_{s i}` are affine and cover `X`. Then there is an immersion
`X ⟶ ℙ(n; S)` over `S` into a projective space with finitely many homogeneous coordinates
(compare Stacks 01VS). -/
theorem exists_isImmersion_projectiveSpace_of_isAffineOpen {X S : Scheme.{u}} (f : X ⟶ S)
    [IsAffine S] [IsSeparated f] [LocallyOfFiniteType f] (L : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u} L] {ι : Type u} [Finite ι]
    (s : ι → (𝟙_ X.Modules ⟶ L))
    (hs : ∀ i, IsAffineOpen (Hom.zeroLocus (s i)).support.compl)
    (hcov : ⨆ i, (Hom.zeroLocus (s i)).support.compl = ⊤) :
    ∃ (n : Type u) (_ : Finite n) (j : X ⟶ ℙ(n; S)), IsImmersion j ∧ j ≫ ℙ(n; S) ↘ S = f := by
  classical
  set U : ι → X.Opens := fun i ↦ (Hom.zeroLocus (s i)).support.compl
  have hUa (i : ι) : IsAffine (U i).toScheme := hs i
  have : CompactSpace X := by
    refine ⟨?_⟩
    have h := isCompact_iUnion fun i ↦ (hs i).isCompact
    rwa [← TopologicalSpace.Opens.coe_iSup, hcov, TopologicalSpace.Opens.coe_top] at h
  -- generators of `Γ(X_{s i}, 𝒪_X)` over `Γ(S, 𝒪_S)`
  choose m hm t ht using fun i ↦ exists_finite_subring_closure_divBasicOpen_eq_top
    ((U i).ι ≫ f) 1 ⊤ (isAffineOpen_top S) fun _ _ ↦ trivial
  have : ∀ i, Finite (m i) := hm
  -- clearing denominators with a common exponent `N + 1`
  choose k v hv using fun p : Σ i, m i ↦
    exists_restrict_eq_smul_tensorPowSectionOne f L (s p.1) ((U p.1).topIso.hom (t p.1 p.2))
  obtain ⟨N, hN⟩ := Finite.exists_le k
  choose w hw using fun p : Σ i, m i ↦
    exists_restrict_eq_smul_tensorPowSectionOne_of_le (s p.1) (v p) (hv p)
      ((hN p).trans N.le_succ)
  set n : Type u := ι ⊕ Σ i, m i
  set s' : n → Γ(L.tensorPow (N + 1), ⊤) :=
    Sum.elim (fun i ↦ tensorPowSectionOne (s i) (N + 1) ⊤) w
  set U' : n → X.Opens := Sum.elim U fun _ ↦ ⊥
  have hs' (j : n) : IsFreeGenerator
      ((L.tensorPow (N + 1)).presheaf.map (homOfLE (le_top : U' j ≤ ⊤)).op (s' j)) := by
    rcases j with i | p
    · simp only [s', U', Sum.elim_inl]
      rw [presheaf_map_tensorPowSectionOne]
      exact isFreeGenerator_tensorPowSectionOne _ (isFreeGenerator_app_one_of_le _ le_rfl) _
    · exact isFreeGenerator_bot _
  have hU' : ⨆ j, U' j = ⊤ :=
    eq_top_iff.mpr (hcov.ge.trans (iSup_le fun i ↦ le_iSup U' (Sum.inl i)))
  set φ := ProjectiveSpace.homOfIsFreeGenerator s' U' hs' f hU'
  have hpre (i : ι) : φ ⁻¹ᵁ ProjectiveSpace.standardOpen n S (Sum.inl i) = U i := by
    refine le_antisymm (le_compl_support_zeroLocus_of_isFreeGenerator (s i) N.succ_ne_zero ?_)
      (ProjectiveSpace.le_preimage_standardOpen s' U' hs' f hU' (Sum.inl i))
    have h := ProjectiveSpace.isFreeGenerator_of_twistRestrict_iso
      (ProjectiveSpace.twistRestrictHom s' U' hs' f hU')
      (ProjectiveSpace.twistRestrictHom_app_pullbackSection s' U' hs' f hU') (Sum.inl i)
    simp only [s', Sum.elim_inl] at h
    rwa [presheaf_map_tensorPowSectionOne] at h
  refine ⟨n, inferInstance, φ, ?_, ProjectiveSpace.homOfIsFreeGenerator_over s' U' hs' f hU'⟩
  refine IsZariskiLocalAtTarget.of_range_subset_iSup
    (fun i : ι ↦ ProjectiveSpace.standardOpen n S (Sum.inl i)) ?_ fun i ↦ ?_
  · rintro _ ⟨x, rfl⟩
    have hx : x ∈ ⨆ i, U i := by rw [hcov]; trivial
    obtain ⟨i, hxi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact SetLike.mem_coe.mpr (TopologicalSpace.Opens.mem_iSup.mpr ⟨i, (hpre i).ge hxi⟩)
  -- on `X_{s i}`, `φ` is the immersion classified by the generators `t i μ`
  set s'' := ProjectiveSpace.localSections s' U' hs' (Sum.inl i)
  have h₁ : s'' (Sum.inl i) = 1 := by
    simp [s'', ProjectiveSpace.localSections]
  have ht' (μ : m i) : s'' (Sum.inr ⟨i, μ⟩) = t i μ := by
    have h : ProjectiveSpace.sectionRatio s' U' hs' (Sum.inl i) (Sum.inr ⟨i, μ⟩) =
        (U i).topIso.hom (t i μ) := by
      refine ((hs' (Sum.inl i)).coeff_eq_iff _ _).mpr ?_
      simp only [s', U', Sum.elim_inl, Sum.elim_inr]
      rw [presheaf_map_tensorPowSectionOne]
      exact (hw ⟨i, μ⟩).symm
    simp only [s'', ProjectiveSpace.localSections, h]
    exact Iso.hom_inv_id_apply _ _
  set B := (U i).toScheme.basicOpen (s'' (Sum.inl i))
  have : IsIso B.ι := Scheme.Opens.isIso_ι_of_eq_top (by simp [B, h₁])
  have key : B.ι ≫ φ.resLE (ProjectiveSpace.standardOpen n S (Sum.inl i)) (U i) (hpre i).ge =
      (ProjectiveSpace.homOfSections ((U i).ι ≫ f) s''
        (ProjectiveSpace.span_range_localSections s' U' hs' (Sum.inl i))).resLE
        (ProjectiveSpace.standardOpen n S (Sum.inl i)) B
        (ProjectiveSpace.homOfSections_preimage_standardOpen _ _ _ _).ge := by
    rw [← cancel_mono (ProjectiveSpace.standardOpen n S (Sum.inl i)).ι, Category.assoc,
      Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι]
    exact congrArg (B.ι ≫ ·) (ProjectiveSpace.ι_homOfIsFreeGenerator s' U' hs' f hU' (Sum.inl i))
  rw [← Scheme.Hom.resLE_eq_morphismRestrict,
    Scheme.Hom.resLE_congr φ (U := ProjectiveSpace.standardOpen n S (Sum.inl i)) le_rfl rfl
      (hpre i) @IsImmersion,
    ← MorphismProperty.cancel_left_of_respectsIso @IsImmersion B.ι, key,
    ← MorphismProperty.cancel_right_of_respectsIso @IsImmersion _
      (ProjectiveSpace.standardOpenIso n S (Sum.inl i)).hom,
    ProjectiveSpace.homOfSections_resLE_standardOpenIso_hom]
  refine isImmersion_homOfVector_divBasicOpen ((U i).ι ≫ f) s'' (Sum.inl i) ⊤
    (isAffineOpen_top S) (fun _ _ ↦ trivial) (eq_top_iff.mpr
      ((subring_closure_divBasicOpen_eq_top_of_eq_one _ _ h₁ (t i) _ _ (ht i)).ge.trans
        (Subring.closure_mono (Set.union_subset_union_right _ ?_))))
  rintro _ ⟨μ, rfl⟩
  exact ⟨⟨Sum.inr ⟨i, μ⟩, Sum.inr_ne_inl⟩,
    congrArg (fun x ↦ (U i).toScheme.divBasicOpen x (s'' (Sum.inl i))) (ht' μ)⟩

section Pullback

variable {X Y : Scheme.{u}}

/-- The non-vanishing locus of the pullback `g^* s` of a section `s : 𝒪_Y ⟶ L` of an invertible
module is the preimage of the non-vanishing locus of `s`. -/
lemma Scheme.Modules.compl_support_zeroLocus_pullback (g : X ⟶ Y) {L : Y.Modules}
    [SheafOfModules.IsInvertible.{u, u, u} L] (s : 𝟙_ Y.Modules ⟶ L) :
    (Hom.zeroLocus ((pullbackObjUnitIso g).inv ≫ (pullback g).map s)).support.compl =
      g ⁻¹ᵁ (Hom.zeroLocus s).support.compl := by
  have : SheafOfModules.IsInvertible.{u, u, u} ((pullback g).obj L) := .pullback inferInstance
  have : SheafOfModules.IsInvertible.{u, u, u} (𝟙_ Y.Modules) :=
    IsInvertible.sheafOfModules_isInvertible (𝟙_ Y.Modules)
  have : SheafOfModules.IsInvertible.{u, u, u} (𝟙_ X.Modules) :=
    IsInvertible.sheafOfModules_isInvertible (𝟙_ X.Modules)
  have : SheafOfModules.IsInvertible.{u, u, u} ((pullback g).obj (𝟙_ Y.Modules)) :=
    .pullback inferInstance
  have h := Hom.zeroLocus_eq_of_arrowIso ((pullbackObjUnitIso g).inv ≫ (pullback g).map s)
    ((pullback g).map s) (Arrow.isoMk (pullbackObjUnitIso g).symm (Iso.refl _))
  rw [h, ← Hom.comap_zeroLocus]
  ext x
  simp [Scheme.IdealSheafData.support_comap]

/-- **Ample families pull back along affine morphisms.** Let `g : X ⟶ Y` be an affine
morphism and `s i` global sections of an invertible module `L` on `Y` whose non-vanishing loci
are affine and cover `Y`. Then the pullbacks `g^* s i` of the sections to `g^* L` have affine
non-vanishing loci covering `X`. -/
theorem Scheme.Modules.exists_isAffineOpen_compl_support_zeroLocus_of_isAffineHom (g : X ⟶ Y)
    [IsAffineHom g] (L : Y.Modules) [SheafOfModules.IsInvertible.{u, u, u} L] {ι : Type u}
    (s : ι → (𝟙_ Y.Modules ⟶ L)) (hs : ∀ i, IsAffineOpen (Hom.zeroLocus (s i)).support.compl)
    (hcov : ⨆ i, (Hom.zeroLocus (s i)).support.compl = ⊤) :
    ∃ (L' : X.Modules) (_ : SheafOfModules.IsInvertible.{u, u, u} L')
      (s' : ι → (𝟙_ X.Modules ⟶ L')),
      (∀ i, IsAffineOpen (Hom.zeroLocus (s' i)).support.compl) ∧
        ⨆ i, (Hom.zeroLocus (s' i)).support.compl = ⊤ := by
  refine ⟨(pullback g).obj L, .pullback inferInstance,
    fun i ↦ (pullbackObjUnitIso g).inv ≫ (pullback g).map (s i), fun i ↦ ?_, ?_⟩
  · rw [compl_support_zeroLocus_pullback]
    exact (hs i).preimage g
  · simp_rw [compl_support_zeroLocus_pullback]
    rw [← Scheme.Hom.preimage_iSup, hcov, Scheme.Hom.preimage_top]

end Pullback

end AlgebraicGeometry
