/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.CechBaseChange
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.CechExact
public import WeilConjectures.AlgebraicGeometry.Modules.InvertibleFibre
public import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
public import WeilConjectures.AlgebraicGeometry.Picard.Representability
public import WeilConjectures.Mathlib.RingTheory.Flat.Equalizer
public import WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Sections of `F`-classes do not vanish on fibres

Let `f : X ⟶ Spec k` be flat, proper and of finite presentation, and let `ℒ ∈ Pic(X_T)` satisfy
`AlgebraicGeometry.IsInvertibleDirectImage`, i.e. `R f_{T,*} ℒ` is an invertible module placed in
degree `0`. If `s` is a free generator of `f_{T,*} ℒ` over an affine open `V ⊆ T`, then the
pullback of `s` to the fibre `X_t` over every point `t ∈ V` is nonzero
(`AlgebraicGeometry.pullbackSection_baseChangeMap_ne_zero`).

This is the degree `0` part of cohomology and base change. Over `A = Γ(T, V)`, the sections of
`ℒ` over `f_T⁻¹ V` are the kernel of the first differential of the Čech complex `Č` of a
finite affine cover trivializing `ℒ`, whose terms are flat over `A`. For every `A`-algebra `B`
the base change `B ⊗[A] Č` is the Čech complex of the pullback of `ℒ` to `X_B`
(`AlgebraicGeometry.Scheme.Modules.cechBaseChange_bijective`), which is exact in degree `1`
since `ℒ_B` still satisfies the condition. Taking `B = A ⊕ M` a square-zero extension, `M ⊗[A] Č`
is exact in degree `1` for every `A`-module `M`; hence `Γ(f_T⁻¹ V, ℒ) ⊗[A] B ⟶ B ⊗[A] Č⁰` is
injective (`Module.Flat.lTensor_injective_ker_subtype`), and for `B = κ(t)` this sends
`s ⊗ 1 ≠ 0` to the family of pullbacks of `s`.
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct Opposite TopCat.Presheaf

namespace AlgebraicGeometry

open Scheme Modules

/-- **Finite trivializing affine covers.** A quasi-compact open `W` of a scheme is covered by
finitely many affine opens contained in `W` on which a given invertible module has free
generators. -/
lemma Scheme.Modules.exists_finite_cover_isFreeGenerator {Y : Scheme.{u}} (ℒ : Y.Modules)
    [SheafOfModules.IsInvertible.{u, u, u} ℒ] {W : Y.Opens} (hW : IsCompact (W : Set Y)) :
    ∃ (ι : Type u) (_ : Finite ι) (U : ι → Y.Opens), (∀ i, IsAffineOpen (U i)) ∧
      (∀ i, U i ≤ W) ∧ ⨆ i, U i = W ∧ ∀ i, ∃ e : Γ(ℒ, U i), IsFreeGenerator e := by
  choose U hxU hUW he using fun x : W ↦ exists_isFreeGenerator ℒ x.2
  obtain ⟨s, hs⟩ := hW.elim_finite_subcover (fun x : W ↦ ((U x).1 : Set Y))
    (fun x ↦ (U x).1.isOpen) (fun x hx ↦ Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxU _⟩)
  refine ⟨s, inferInstance, fun x ↦ (U x).1, fun x ↦ (U x).2, fun x ↦ hUW x, ?_,
    fun x ↦ he x⟩
  refine le_antisymm (iSup_le fun x ↦ hUW x) fun x hx ↦ ?_
  obtain ⟨y, hys, hxy⟩ := Set.mem_iUnion₂.mp (hs hx)
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨y, hys⟩, hxy⟩

/-- Finite intersections of affine opens lying over an affine open of the target of a
separated morphism are affine. -/
lemma isAffineOpen_iInf_of_isSeparated {Y T : Scheme.{u}} (p : Y ⟶ T) [IsSeparated p]
    {V : T.Opens} (hV : IsAffineOpen V) {ι : Type u} (U : ι → Y.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hUV : ∀ i, U i ≤ p ⁻¹ᵁ V) {k : ℕ} (y : Fin (k + 1) → ι) :
    IsAffineOpen (⨅ l, U (y l)) := by
  have H := isAffineHom_diagonal_iff.mp (inferInstance : IsAffineHom (pullback.diagonal p)) V hV
  have key : ∀ (s : Finset (Fin (k + 1))), s.Nonempty →
      IsAffineOpen (⨅ l ∈ s, U (y l)) ∧ ⨅ l ∈ s, U (y l) ≤ p ⁻¹ᵁ V := by
    intro s hs
    induction hs using Finset.Nonempty.cons_induction with
    | singleton a => simpa using ⟨hU (y a), hUV (y a)⟩
    | cons a s ha hs ih =>
      rw [Finset.cons_eq_insert, Finset.iInf_insert]
      exact ⟨H _ (hUV _) _ ih.2 (hU _) ih.1, inf_le_left.trans (hUV _)⟩
  simpa using (key Finset.univ Finset.univ_nonempty).1



/-- Functions on an affine open `V` pulled back along `Spec R ⟶ Spec Γ(T, V) ⟶ T` are their
images under `φ : Γ(T, V) ⟶ R`. -/
lemma ΓSpecIso_hom_appLE_SpecMap_comp_fromSpec {T : Scheme.{u}} {V : T.Opens}
    (hV : IsAffineOpen V) {R : CommRingCat.{u}} (φ : Γ(T, V) ⟶ R)
    (h : ⊤ ≤ (Spec.map φ ≫ hV.fromSpec) ⁻¹ᵁ V) (a : Γ(T, V)) :
    (Scheme.ΓSpecIso R).hom ((Spec.map φ ≫ hV.fromSpec).appLE V ⊤ h a) = φ a := by
  have : (Spec.map φ ≫ hV.fromSpec).appLE V ⊤ h ≫ (Scheme.ΓSpecIso R).hom = φ := by
    have e₁ : hV.fromSpec.appLE V ⊤ hV.fromSpec_preimage_self.ge = (Scheme.ΓSpecIso _).inv := by
      rw [Scheme.Hom.appLE, hV.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
      convert Category.comp_id _
      exact (Spec Γ(T, V)).presheaf.map_id _
    rw [← Scheme.Hom.appLE_comp_appLE _ _ _ ⊤ _ hV.fromSpec_preimage_self.ge (by simp), e₁,
      Category.assoc, Scheme.Hom.appLE_top_top_eq_appTop, Scheme.ΓSpecIso_naturality,
      Iso.inv_hom_id_assoc]
  exact congr($this a)

section Core

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Flat f] [IsProper f]
  [LocallyOfFinitePresentation f]
  [∀ T : Over (Spec (.of k)), HasInjectiveResolutions (Limits.pullback f T.hom).Modules]

-- the proof assembles the Čech complex, its base changes and their exactness in one context
/-- **Pullbacks of generators of `f_{T,*} ℒ` to fibres are nonzero.** Let `ℒ ∈ Pic(X_T)` satisfy
`IsInvertibleDirectImage`, let `s` be a free generator of `f_{T,*} ℒ` on an affine open `V ⊆ T`
and let `i : T' ⟶ T` be a morphism from an affine scheme with nonzero ring of functions, landing
in `V`. Then the pullback of `s` to `X_{T'}` is nonzero.

This is the degree `0` part of cohomology and base change: see the module documentation. -/
theorem pullbackSection_baseChangeMap_ne_zero {T : Over (Spec (.of k))}
    {L : (Limits.pullback f T.hom).Pic} (hL : IsInvertibleDirectImage f T L)
    {V : T.left.Opens} (hV : IsAffineOpen V)
    {s : Γ((pushforward (Limits.pullback.snd f T.hom)).obj ((fromSkeleton _).obj L.val), V)}
    (hs : IsFreeGenerator s) {T' : Over (Spec (.of k))} (i : T' ⟶ T) [IsAffine T'.left]
    [Nontrivial Γ(T'.left, ⊤)] (hi : ⊤ ≤ i.left ⁻¹ᵁ V) :
    pullbackSection (baseChangeMap f i)
      (show Γ((fromSkeleton _).obj L.val, Limits.pullback.snd f T.hom ⁻¹ᵁ V) from s) ≠ 0 := by
  classical
  let sT := Limits.pullback.snd f T.hom
  let ℒ := (fromSkeleton _).obj L.val
  have : SheafOfModules.IsInvertible.{u, u, u} ℒ := L.isInvertible
  have : ℒ.IsInvertible := IsInvertible.of_sheafOfModules _
  have hW := sT.isCompact_preimage hV.isCompact
  obtain ⟨ι, _, U, hUa, hUV, hUsup, he⟩ := exists_finite_cover_isFreeGenerator ℒ hW
  have := Fintype.ofFinite ι
  let instC : ∀ (k : ℕ) (y : Fin (k + 1) → ι), Module Γ(T.left, V) Γ(ℒ, ⨅ l, U (y l)) :=
    fun k y ↦ Module.compHom _ (sT.appLE V _ (iInf_le_preimage_of_forall_le U hUV y)).hom
  have hU : ∀ (k : ℕ) (y : Fin (k + 1) → ι) (a : Γ(T.left, V)) (x : Γ(ℒ, ⨅ l, U (y l))),
      a • x = sT.appLE V _ (iInf_le_preimage_of_forall_le U hUV y) a • x :=
    fun _ _ _ _ ↦ rfl
  have hUa' (k : ℕ) (y : Fin (k + 1) → ι) : IsAffineOpen (⨅ l, U (y l)) :=
    isAffineOpen_iInf_of_isSeparated sT hV U hUa hUV y
  have he' (k : ℕ) (y : Fin (k + 1) → ι) : ∃ e : Γ(ℒ, ⨅ l, U (y l)), IsFreeGenerator e := by
    obtain ⟨e, he⟩ := he (y 0)
    exact ⟨_, he.map (iInf_le _ 0)⟩
  -- the Čech complex stays exact in degree `1` after base change to affine `T''` over `V`
  have hexB : ∀ (T'' : Over (Spec (.of k))) (j : T'' ⟶ T) [IsAffine T''.left]
      (hj : ⊤ ≤ j.left ⁻¹ᵁ V),
      letI := (j.left.appLE V ⊤ hj).hom.toAlgebra
      Function.Exact ((cechDifferential ℒ U hUV hU 0).lTensor Γ(T''.left, ⊤))
        ((cechDifferential ℒ U hUV hU 1).lTensor Γ(T''.left, ⊤)) := by
    intro T'' j _ hj
    let := (j.left.appLE V ⊤ hj).hom.toAlgebra
    have H := isPullback_baseChangeMap f j
    have hL'' := IsInvertibleDirectImage.map_of_isProper f j hL
    have : ((Modules.pullback (baseChangeMap f j)).obj ℒ).IsInvertible :=
      IsInvertible.pullback ..
    have hZ : IsZero ((higherDirectImage (Limits.pullback.snd f T''.hom) 1).obj
        ((Modules.pullback (baseChangeMap f j)).obj ℒ)) :=
      (hL''.2 1 one_pos).of_iso ((higherDirectImage _ 1).mapIso (fromSkeletonToSkeletonIso _).symm)
    have hsup : ⨆ i, baseChangeMap f j ⁻¹ᵁ U i = ⊤ := by
      rw [← Scheme.Hom.preimage_iSup, hUsup, ← Scheme.Hom.comp_preimage, H.w,
        Scheme.Hom.comp_preimage, eq_top_iff]
      exact (Scheme.Hom.preimage_top _).ge.trans (Scheme.Hom.preimage_mono _ hj)
    exact exact_lTensor_cechDifferential hj ℒ U hUV rfl hU H hV hUa' he'
      (exactAt_cechComplex_of_isZero_higherDirectImage (Limits.pullback.snd f T''.hom) _
        (fun i ↦ isAffineOpen_preimage_of_isPullback H hV hj (hUV i) (hUa i)) hsup _ 1 hZ)
  -- hence `Č` stays exact in degree `1` after tensoring with any module, via `A ⊕ M`
  have hexM : ∀ (M : Type u) [AddCommGroup M] [Module Γ(T.left, V) M],
      Function.Exact ((cechDifferential ℒ U hUV hU 0).lTensor M)
        ((cechDifferential ℒ U hUV hU 1).lTensor M) := by
    intro M _ _
    let : Module Γ(T.left, V)ᵐᵒᵖ M :=
      Module.compHom M ((RingHom.id Γ(T.left, V)).fromOpposite fun _ _ ↦ mul_comm _ _)
    have : IsCentralScalar Γ(T.left, V) M := ⟨fun _ _ ↦ rfl⟩
    let R := CommRingCat.of (TrivSqZeroExt Γ(T.left, V) M)
    let φ : Γ(T.left, V) ⟶ R := CommRingCat.ofHom (algebraMap _ _)
    let T'' : Over (Spec (.of k)) := Over.mk (Spec.map φ ≫ hV.fromSpec ≫ T.hom)
    let j : T'' ⟶ T := Over.homMk (Spec.map φ ≫ hV.fromSpec) (by simp [T''])
    have hj : ⊤ ≤ j.left ⁻¹ᵁ V := by
      change ⊤ ≤ (Spec.map φ ≫ hV.fromSpec) ⁻¹ᵁ V
      rw [Scheme.Hom.comp_preimage, hV.fromSpec_preimage_self, Scheme.Hom.preimage_top]
    have : IsAffine T''.left := inferInstanceAs (IsAffine (Spec R))
    have h := hexB T'' j hj
    let := (j.left.appLE V ⊤ hj).hom.toAlgebra
    have key (a : Γ(T.left, V)) (x : Γ(T''.left, ⊤)) :
        (Scheme.ΓSpecIso R).hom (a • x) =
          TrivSqZeroExt.inl a * (Scheme.ΓSpecIso R).hom x := by
      rw [Algebra.smul_def, map_mul]
      congr 1
      exact ΓSpecIso_hom_appLE_SpecMap_comp_fromSpec hV φ hj a
    let r : Γ(T''.left, ⊤) →ₗ[Γ(T.left, V)] M :=
      { toFun x := ((Scheme.ΓSpecIso R).hom x).snd
        map_add' x x' := by rw [map_add, TrivSqZeroExt.snd_add]
        map_smul' a x := by
          rw [key, TrivSqZeroExt.inl_mul_eq_smul, RingHom.id_apply]
          exact TrivSqZeroExt.snd_smul a _ }
    let ι' : M →ₗ[Γ(T.left, V)] Γ(T''.left, ⊤) :=
      { toFun m := (Scheme.ΓSpecIso R).inv (TrivSqZeroExt.inr m)
        map_add' m m' := by simp
        map_smul' a m := by
          apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).hom).1
          rw [RingHom.id_apply, key, Iso.inv_hom_id_apply, Iso.inv_hom_id_apply,
            TrivSqZeroExt.inl_mul_inr] }
    exact Function.Exact.rTensor_of_retract ι' r (LinearMap.ext fun m ↦ by simp [r, ι']) h
  -- the terms of `Č` are flat over `A`
  have hflat (k : ℕ) : Module.Flat Γ(T.left, V) (CechCochain U ℒ.presheaf k) := by
    have (y : Fin (k + 1) → ι) : Module.Flat Γ(T.left, V) Γ(ℒ, ⨅ l, U (y l)) := by
      obtain ⟨e, he⟩ := he' k y
      let := (sT.appLE V _ (iInf_le_preimage_of_forall_le U hUV y)).hom.toAlgebra
      have : Module.Flat Γ(T.left, V) Γ(Limits.pullback f T.hom, ⨅ l, U (y l)) :=
        HasRingHomProperty.appLE @Flat sT inferInstance ⟨V, hV⟩ ⟨_, hUa' k y⟩ _
      let ψ : Γ(Limits.pullback f T.hom, ⨅ l, U (y l)) →ₗ[Γ(T.left, V)] Γ(ℒ, ⨅ l, U (y l)) :=
        { toFun r := r • e
          map_add' r r' := add_smul r r' e
          map_smul' a r := by
            rw [RingHom.id_apply, hU, Algebra.smul_def, mul_smul]
            rfl }
      exact Module.Flat.of_linearEquiv (LinearEquiv.ofBijective ψ he.bijective).symm
    exact Module.Flat.of_linearEquiv (DFinsupp.linearEquivFunOnFintype (R := Γ(T.left, V))
      (M := fun y : Fin (k + 1) → ι ↦ Γ(ℒ, ⨅ l, U (y l)))).symm
  -- base change to `T'`: the kernel of `d⁰` stays a submodule of `Č⁰`
  let := (i.left.appLE V ⊤ hi).hom.toAlgebra
  have : Module.Flat Γ(T.left, V) (CechCochain U ℒ.presheaf (0 + 1)) := hflat _
  have : Module.Flat Γ(T.left, V) (CechCochain U ℒ.presheaf (1 + 1)) := hflat _
  have hinj := Module.Flat.lTensor_injective_ker_subtype (cechDifferential ℒ U hUV hU 0)
    (cechDifferential ℒ U hUV hU 1) (cechDifferential_comp ℒ U hUV hU 0) hexM Γ(T'.left, ⊤)
  -- the sections over `f_T⁻¹ V` are the kernel of `d⁰`
  let ρ₀ : Γ((pushforward sT).obj ℒ, V) →ₗ[Γ(T.left, V)] CechCochain U ℒ.presheaf 0 :=
    { toFun x z := ℒ.presheaf.map (homOfLE (iInf_le_of_iSup_eq U hUsup z)).op x
      map_add' x x' := by funext z; exact map_add _ _ _
      map_smul' a x := by
        funext z
        change ℒ.presheaf.map (homOfLE (iInf_le_of_iSup_eq U hUsup z)).op
            ((sT.app V a) • (show Γ(ℒ, sT ⁻¹ᵁ V) from x)) =
          (sT.appLE V _ (iInf_le_preimage_of_forall_le U hUV z) a) •
            ℒ.presheaf.map (homOfLE (iInf_le_of_iSup_eq U hUsup z)).op x
        rw [Scheme.Modules.map_smul, Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply,
          Scheme.Hom.appLE_map] }
  have hρ₀ (x : Γ((pushforward sT).obj ℒ, V)) : ρ₀ x ∈ LinearMap.ker
      (cechDifferential ℒ U hUV hU 0) :=
    cechComplex_d_zero_restrict U ℒ.presheaf x (iInf_le_of_iSup_eq U hUsup)
  let ρ : Γ((pushforward sT).obj ℒ, V) ≃ₗ[Γ(T.left, V)]
      LinearMap.ker (cechDifferential ℒ U hUV hU 0) :=
    LinearEquiv.ofBijective (ρ₀.codRestrict _ hρ₀)
      ⟨fun x x' hxx' ↦ eq_of_forall_presheaf_map_eq ℒ U hUsup x x' fun z ↦
        congr_fun (congrArg Subtype.val hxx') z, fun c ↦ by
        obtain ⟨x, hx⟩ := exists_presheaf_map_eq_of_cechComplex_d_eq_zero ℒ U hUsup c.1 c.2
        exact ⟨x, Subtype.ext (funext hx)⟩⟩
  -- `1 ⊗ s ≠ 0`
  let σ : Γ(T.left, V) ≃ₗ[Γ(T.left, V)] Γ((pushforward sT).obj ℒ, V) :=
    LinearEquiv.ofBijective
      { toFun a := a • s, map_add' a a' := add_smul a a' s, map_smul' a a' := mul_smul a a' s }
      hs.bijective
  have hne : ((1 : Γ(T'.left, ⊤)) ⊗ₜ[Γ(T.left, V)] ρ₀ s) ≠ 0 := by
    intro h0
    have h1 : ((LinearMap.ker (cechDifferential ℒ U hUV hU 0)).subtype.lTensor Γ(T'.left, ⊤))
        ((1 : Γ(T'.left, ⊤)) ⊗ₜ ρ s) = 0 := h0
    have h2 := hinj (h1.trans (map_zero _).symm)
    have h3 := congrArg (TensorProduct.rid Γ(T.left, V) Γ(T'.left, ⊤))
      (congrArg ((LinearEquiv.lTensor Γ(T'.left, ⊤) (σ.trans ρ)).symm) h2)
    have h4 : (σ.trans ρ) 1 = ρ s := by
      change ρ ((1 : Γ(T.left, V)) • s) = ρ s
      rw [one_smul]
    rw [map_zero, map_zero, ← h4, LinearEquiv.symm_lTensor, LinearEquiv.lTensor_tmul,
      LinearEquiv.symm_apply_apply, TensorProduct.rid_tmul, one_smul] at h3
    exact one_ne_zero h3
  -- its image is the family of pullbacks of `s`
  have H := isPullback_baseChangeMap f i
  intro hzero
  apply hne
  refine (cechBaseChange_bijective hi ℒ U hUV rfl hU H hV hUa' he' 0).1 ?_
  rw [map_zero]
  funext z
  rw [cechBaseChange_tmul]
  have : ρ₀ s z = ℒ.presheaf.map (homOfLE (iInf_le_of_iSup_eq U hUsup z)).op s := rfl
  rw [this, pullbackSection_map, map_one, one_smul]
  erw [hzero]
  rw [map_zero, map_zero]
  rfl


/-- Pullback of sections is natural in the module. -/
lemma Scheme.Modules.pullbackSection_app {Y Z : Scheme.{u}} (g : Z ⟶ Y) {M N : Y.Modules}
    (φ : M ⟶ N) {U : Y.Opens} (m : Γ(M, U)) :
    pullbackSection g (φ.app U m) = ((Modules.pullback g).map φ).app (g ⁻¹ᵁ U)
      (pullbackSection g m) :=
  congr($(congrArg (fun ψ ↦ Hom.app ψ U)
    ((pullbackPushforwardAdjunction g).unit.naturality φ)) m)

/-- **The adjunction morphism of an `F`-class does not vanish on fibres.** For `ℒ` satisfying
`IsInvertibleDirectImage` and `q : T₀ ⟶ T` from an affine scheme with nonzero ring of functions,
landing in an affine open over which `f_{T,*} ℒ` has a free generator, the pullback along
`X_{T₀} ⟶ X_T` of the adjunction morphism `f_T^* f_{T,*} ℒ ⟶ ℒ` is nonzero: by the triangle
identity it sends the pullback of the generator to the pullback of the generator, which is
nonzero (`AlgebraicGeometry.pullbackSection_baseChangeMap_ne_zero`). -/
theorem pullback_baseChangeMap_map_counit_ne_zero {T : Over (Spec (.of k))}
    {L : (Limits.pullback f T.hom).Pic} (hL : IsInvertibleDirectImage f T L)
    {V : T.left.Opens} (hV : IsAffineOpen V)
    {s : Γ((pushforward (Limits.pullback.snd f T.hom)).obj ((fromSkeleton _).obj L.val), V)}
    (hs : IsFreeGenerator s) {T₀ : Over (Spec (.of k))} (q : T₀ ⟶ T) [IsAffine T₀.left]
    [Nontrivial Γ(T₀.left, ⊤)] (hq : ⊤ ≤ q.left ⁻¹ᵁ V) :
    (Modules.pullback (baseChangeMap f q)).map
      ((pullbackPushforwardAdjunction (Limits.pullback.snd f T.hom)).counit.app
        ((fromSkeleton _).obj L.val)) ≠ 0 := by
  intro h0
  apply pullbackSection_baseChangeMap_ne_zero f hL hV hs q hq
  let adj := pullbackPushforwardAdjunction (Limits.pullback.snd f T.hom)
  have tri := adj.right_triangle_components ((fromSkeleton _).obj L.val)
  have hs' : (adj.counit.app ((fromSkeleton _).obj L.val)).app _
      ((adj.unit.app ((pushforward (Limits.pullback.snd f T.hom)).obj
        ((fromSkeleton _).obj L.val))).app V s) = s :=
    congr($(congrArg (fun ψ ↦ Hom.app ψ V) tri) s)
  have key := pullbackSection_app (baseChangeMap f q) (adj.counit.app _)
    ((adj.unit.app ((pushforward (Limits.pullback.snd f T.hom)).obj
      ((fromSkeleton _).obj L.val))).app V s)
  erw [h0, hs'] at key
  exact key

end Core

end AlgebraicGeometry
