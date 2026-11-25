/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.GlobalSections
public import WeilConjectures.Topology.Sheaves.CechCriterion
public import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme

/-!
# Čech complexes of invertible modules under affine base change

Consider a cartesian square of schemes
```
Y --g--> X
|        |
iY       iX
v        v
T --f--> S
```
with `T` affine, and an affine open `V ⊆ S` containing the image of `T`; write `A = Γ(S, V)` and
`B = Γ(T, ⊤)`. For an `𝒪_X`-module `ℱ` and an affine open `W ⊆ iX⁻¹ V` on which `ℱ` has a free
generator, the map `B ⊗[A] Γ(ℱ, W) ⟶ Γ(g^* ℱ, g⁻¹ W)`, `b ⊗ x ↦ iY^♯ b • g^* x`, is bijective
(`AlgebraicGeometry.Scheme.Modules.sectionsBaseChange_bijective`): this is the base change of the
ring of functions of the affine `W`.

Consequently, for a finite cover `U` of `iX⁻¹ V` by such opens, all of whose finite intersections
are affine, the Čech complex of `g^* ℱ` for the cover `g⁻¹ U` of `Y` is the base change
`B ⊗[A] Č(U, ℱ)` of the Čech complex of `ℱ`
(`AlgebraicGeometry.Scheme.Modules.cechBaseChange_bijective`,
`AlgebraicGeometry.Scheme.Modules.cechBaseChange_d`).

The `A`-module structures on the sections of `ℱ` are not instances: the statements take them as
instance arguments together with the hypothesis that they are restriction of scalars along
`iX^♯ : Γ(S, V) ⟶ Γ(X, W)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y S T : Scheme.{u}} {g : Y ⟶ X} {iY : Y ⟶ T} {iX : X ⟶ S} {f : T ⟶ S}


/-- In a cartesian square with `T` affine mapping into an affine open `V`, the preimage
`g⁻¹ W = W ×_V T` of an affine open `W ⊆ iX⁻¹ V` is affine. -/
lemma isAffineOpen_preimage_of_isPullback (H : IsPullback g iY iX f) {V : S.Opens}
    (hV : IsAffineOpen V) [IsAffine T] (hfV : ⊤ ≤ f ⁻¹ᵁ V) {W : X.Opens} (hWV : W ≤ iX ⁻¹ᵁ V)
    (hW : IsAffineOpen W) : IsAffineOpen (g ⁻¹ᵁ W) := by
  have hUY : g ⁻¹ᵁ W = g ⁻¹ᵁ W ⊓ iY ⁻¹ᵁ ⊤ := by simp
  have : IsAffine V.toScheme := hV
  have : IsAffine (⊤ : T.Opens).toScheme := isAffineOpen_top T
  have : IsAffine W.toScheme := hW
  exact .of_isIso (Scheme.Hom.isPullback_resLE H hfV hWV hUY).isoPullback.hom

section Sections

variable (w : g ≫ iX = iY ≫ f) {V : S.Opens} (hfV : ⊤ ≤ f ⁻¹ᵁ V) (ℱ : X.Modules)
  {W : X.Opens} (hWV : W ≤ iX ⁻¹ᵁ V)
  [Algebra Γ(S, V) Γ(T, ⊤)] (hf : algebraMap Γ(S, V) Γ(T, ⊤) = (f.appLE V ⊤ hfV).hom)
  [Module Γ(S, V) Γ(ℱ, W)] (hW : ∀ (a : Γ(S, V)) (x : Γ(ℱ, W)), a • x = iX.appLE V W hWV a • x)

omit [Algebra Γ(S, V) Γ(T, ⊤)] in
include w in
lemma appLE_comp_eq_app_appLE (a : Γ(S, V)) :
    iY.appLE ⊤ (g ⁻¹ᵁ W) (le_top.trans iY.preimage_top.ge) (f.appLE V ⊤ hfV a) =
      g.app W (iX.appLE V W hWV a) := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.app_eq_appLE,
    ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  congr 1
  simp only [w]

include w hf hW in
/-- **Base change of sections.** The map `B ⊗[A] Γ(ℱ, W) ⟶ Γ(g^* ℱ, g⁻¹ W)`,
`b ⊗ x ↦ iY^♯ b • g^* x`, for `A = Γ(S, V)` and `B = Γ(T, ⊤)`. -/
noncomputable def sectionsBaseChange :
    Γ(T, ⊤) ⊗[Γ(S, V)] Γ(ℱ, W) →+ Γ((pullback g).obj ℱ, g ⁻¹ᵁ W) :=
  TensorProduct.liftAddHom
    { toFun b :=
        { toFun x := iY.appLE ⊤ (g ⁻¹ᵁ W) (le_top.trans iY.preimage_top.ge) b • pullbackSection g x
          map_zero' := by simp only [pullbackSection, map_zero, smul_zero]
          map_add' x x' := by rw [pullbackSection_add, smul_add] }
      map_zero' := by ext x; simp
      map_add' b b' := by ext x; simp [add_smul] }
    (fun a b x ↦ by
      simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      rw [hW, pullbackSection_smul, smul_smul, Algebra.smul_def, hf, map_mul,
        appLE_comp_eq_app_appLE w hfV hWV, mul_comm])

lemma sectionsBaseChange_tmul (b : Γ(T, ⊤)) (x : Γ(ℱ, W)) :
    sectionsBaseChange w hfV ℱ hWV hf hW (b ⊗ₜ x) =
      iY.appLE ⊤ (g ⁻¹ᵁ W) (le_top.trans iY.preimage_top.ge) b • pullbackSection g x :=
  rfl


/-- **Base change of sections over an affine open with a free generator.** If `T` and `V` are
affine and `ℱ` has a free generator `e` on the affine open `W ⊆ iX⁻¹ V`, the map
`B ⊗[A] Γ(ℱ, W) ⟶ Γ(g^* ℱ, g⁻¹ W)` is bijective: through `e` and its pullback `g^* e`, which is a
free generator of `g^* ℱ` on `g⁻¹ W`, it is the identification of `B ⊗[A] Γ(X, W)` with the ring
of functions `Γ(Y, g⁻¹ W)` of the affine `g⁻¹ W = W ×_S T`. -/
theorem sectionsBaseChange_bijective (H : IsPullback g iY iX f) (hV : IsAffineOpen V)
    [IsAffine T] (hWa : IsAffineOpen W) {e : Γ(ℱ, W)} (he : IsFreeGenerator e) :
    Function.Bijective (sectionsBaseChange H.w hfV ℱ hWV hf hW) := by
  let : Algebra Γ(S, V) Γ(X, W) := (iX.appLE V W hWV).hom.toAlgebra
  let ψ : Γ(X, W) →ₗ[Γ(S, V)] Γ(ℱ, W) :=
    { toFun r := r • e
      map_add' r r' := add_smul r r' e
      map_smul' a r := by
        rw [RingHom.id_apply, hW, Algebra.smul_def, mul_smul]
        rfl }
  have hψ : Function.Bijective ψ := he.bijective
  have hUY : g ⁻¹ᵁ W = g ⁻¹ᵁ W ⊓ iY ⁻¹ᵁ ⊤ := by simp
  have hpush := (isIso_pushoutSection_iff H hfV hWV hUY).mp
    (isIso_pushoutSection_of_isAffineOpen H hfV hWV hUY hV (isAffineOpen_top T) hWa)
  have hα : CommRingCat.ofHom (algebraMap Γ(S, V) Γ(T, ⊤)) = f.appLE V ⊤ hfV := by
    rw [hf]
    rfl
  let ε := hpush.tensorEquiv hα rfl
  have he' : IsFreeGenerator (pullbackSection g e) := he.pullback_unit_app g
  have key : ⇑(sectionsBaseChange H.w hfV ℱ hWV hf hW) ∘ ⇑(ψ.lTensor Γ(T, ⊤)) =
      (fun s : Γ(Y, g ⁻¹ᵁ W) ↦ s • pullbackSection g e) ∘ ⇑ε := by
    funext z
    induction z using TensorProduct.inductionOn with
    | tmul b r =>
      simp only [Function.comp_apply, LinearMap.lTensor_tmul, sectionsBaseChange_tmul]
      rw [IsPushout.tensorEquiv_tmul]
      change _ • pullbackSection g (r • e) = _
      rw [pullbackSection_smul, smul_smul, Scheme.Hom.app_eq_appLE]
    | add z z' hz hz' =>
      simp only [Function.comp_apply, map_add, add_smul] at hz hz' ⊢
      rw [hz, hz']
  have hlt : Function.Bijective (ψ.lTensor Γ(T, ⊤)) :=
    (LinearEquiv.lTensor Γ(T, ⊤) (LinearEquiv.ofBijective ψ hψ)).bijective
  refine (Function.Bijective.of_comp_iff _ hlt).mp ?_
  rw [key]
  exact he'.bijective.comp ε.bijective

end Sections

section Cech

open TopCat.Presheaf

variable {V : S.Opens} (hfV : ⊤ ≤ f ⁻¹ᵁ V) (ℱ : X.Modules) {ι : Type u} (U : ι → X.Opens)
  (hUV : ∀ i, U i ≤ iX ⁻¹ᵁ V)

include hUV in
lemma iInf_le_preimage_of_forall_le {k : ℕ} (y : Fin (k + 1) → ι) :
    ⨅ l, U (y l) ≤ iX ⁻¹ᵁ V :=
  (iInf_le _ 0).trans (hUV _)

variable (g) in
lemma iInf_preimage_eq_preimage_iInf {k : ℕ} (y : Fin (k + 1) → ι) :
    ⨅ l, g ⁻¹ᵁ U (y l) = g ⁻¹ᵁ ⨅ l, U (y l) :=
  (g.preimage_iInf _).symm

variable [Algebra Γ(S, V) Γ(T, ⊤)] (hf : algebraMap Γ(S, V) Γ(T, ⊤) = (f.appLE V ⊤ hfV).hom)
  [∀ (k : ℕ) (y : Fin (k + 1) → ι), Module Γ(S, V) Γ(ℱ, ⨅ l, U (y l))]
  (hU : ∀ (k : ℕ) (y : Fin (k + 1) → ι) (a : Γ(S, V)) (x : Γ(ℱ, ⨅ l, U (y l))),
    a • x = iX.appLE V _ (iInf_le_preimage_of_forall_le U hUV y) a • x)

include hU in
/-- The Čech differential `Č^k(U, ℱ) ⟶ Č^{k+1}(U, ℱ)` is `Γ(S, V)`-linear. -/
lemma cechComplex_d_smul (k : ℕ) (a : Γ(S, V)) (c : CechCochain U ℱ.presheaf k) :
    ((cechComplex U).obj ℱ.presheaf).d k (k + 1) (a • c : CechCochain U ℱ.presheaf k) =
      a • (show CechCochain U ℱ.presheaf (k + 1) from
        ((cechComplex U).obj ℱ.presheaf).d k (k + 1) c) := by
  funext y
  rw [cechComplex_d_apply, Pi.smul_apply, cechComplex_d_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [smul_comm, Pi.smul_apply, hU, hU, Scheme.Modules.map_smul]
  congr 2
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

/-- The Čech differential `Č^k(U, ℱ) ⟶ Č^{k+1}(U, ℱ)` as a `Γ(S, V)`-linear map. -/
noncomputable def cechDifferential (k : ℕ) :
    CechCochain U ℱ.presheaf k →ₗ[Γ(S, V)] CechCochain U ℱ.presheaf (k + 1) where
  toFun := ((cechComplex U).obj ℱ.presheaf).d k (k + 1)
  map_add' := map_add _
  map_smul' a c := cechComplex_d_smul ℱ U hUV hU k a c

lemma cechDifferential_apply (k : ℕ) (c : CechCochain U ℱ.presheaf k) :
    cechDifferential ℱ U hUV hU k c = ((cechComplex U).obj ℱ.presheaf).d k (k + 1) c :=
  rfl

lemma cechDifferential_comp (k : ℕ) :
    cechDifferential ℱ U hUV hU (k + 1) ∘ₗ cechDifferential ℱ U hUV hU k = 0 := by
  refine LinearMap.ext fun c ↦ ?_
  exact congr($(((cechComplex U).obj ℱ.presheaf).d_comp_d k (k + 1) (k + 2)) c)

variable (w : g ≫ iX = iY ≫ f) [Fintype ι] [DecidableEq ι]

include w hf hU in
/-- **Base change of Čech cochains.** The map `B ⊗[A] Č^k(U, ℱ) ⟶ Č^k(g⁻¹ U, g^* ℱ)`,
`b ⊗ c ↦ (y ↦ iY^♯ b • g^* (c y))`. -/
noncomputable def cechBaseChange (k : ℕ) :
    Γ(T, ⊤) ⊗[Γ(S, V)] CechCochain U ℱ.presheaf k →+
      CechCochain (fun i ↦ g ⁻¹ᵁ U i) ((pullback g).obj ℱ).presheaf k :=
  AddMonoidHom.pi fun y ↦
    (((pullback g).obj ℱ).presheaf.map
      (eqToHom (iInf_preimage_eq_preimage_iInf g U y)).op).hom.comp
      ((sectionsBaseChange w hfV ℱ (iInf_le_preimage_of_forall_le U hUV y) hf (hU k y)).comp
        ((Pi.evalAddMonoidHom _ y).comp (TensorProduct.piRight Γ(S, V) Γ(S, V) Γ(T, ⊤)
          (fun y : Fin (k + 1) → ι ↦ Γ(ℱ, ⨅ l, U (y l)))).toLinearMap.toAddMonoidHom))

lemma cechBaseChange_tmul (k : ℕ) (b : Γ(T, ⊤)) (c : CechCochain U ℱ.presheaf k)
    (y : Fin (k + 1) → ι) :
    cechBaseChange hfV ℱ U hUV hf hU w k (b ⊗ₜ c) y =
      ((pullback g).obj ℱ).presheaf.map (eqToHom (iInf_preimage_eq_preimage_iInf g U y)).op
        (iY.appLE ⊤ (g ⁻¹ᵁ ⨅ l, U (y l)) (le_top.trans iY.preimage_top.ge) b •
          pullbackSection g (c y)) := by
  simp [cechBaseChange, TensorProduct.piRight_apply, sectionsBaseChange_tmul]


omit [Fintype ι] [DecidableEq ι] in
/-- Restriction commutes with multiplication by the image of a function on `T`. -/
lemma presheaf_map_appLE_smul (P : Y.Modules) {V₁ V₂ : Y.Opens} (h : V₂ ≤ V₁) (b : Γ(T, ⊤))
    (m : Γ(P, V₁)) :
    P.presheaf.map (homOfLE h).op (iY.appLE ⊤ V₁ (le_top.trans iY.preimage_top.ge) b • m) =
      iY.appLE ⊤ V₂ (le_top.trans iY.preimage_top.ge) b • P.presheaf.map (homOfLE h).op m := by
  rw [Scheme.Modules.map_smul, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

/-- **Base change of Čech cochains is bijective** when all finite intersections of the cover are
affine opens on which `ℱ` has a free generator, and `T`, `V` are affine. -/
theorem cechBaseChange_bijective (H : IsPullback g iY iX f) (hV : IsAffineOpen V) [IsAffine T]
    (hUa : ∀ (k : ℕ) (y : Fin (k + 1) → ι), IsAffineOpen (⨅ l, U (y l)))
    (he : ∀ (k : ℕ) (y : Fin (k + 1) → ι), ∃ e : Γ(ℱ, ⨅ l, U (y l)), IsFreeGenerator e)
    (k : ℕ) : Function.Bijective (cechBaseChange hfV ℱ U hUV hf hU H.w k) := by
  let φ : ∀ y : Fin (k + 1) → ι, Γ(T, ⊤) ⊗[Γ(S, V)] Γ(ℱ, ⨅ l, U (y l)) →
      Γ((pullback g).obj ℱ, ⨅ l, g ⁻¹ᵁ U (y l)) := fun y ↦
    (((pullback g).obj ℱ).presheaf.map
      (eqToHom (iInf_preimage_eq_preimage_iInf g U y)).op).hom ∘
      sectionsBaseChange H.w hfV ℱ (iInf_le_preimage_of_forall_le U hUV y) hf (hU k y)
  have hφ (y : Fin (k + 1) → ι) : Function.Bijective (φ y) := by
    obtain ⟨e, he⟩ := he k y
    refine (ConcreteCategory.bijective_of_isIso _).comp ?_
    exact sectionsBaseChange_bijective hfV ℱ _ hf (hU k y) H hV (hUa k y) he
  have key : ⇑(cechBaseChange hfV ℱ U hUV hf hU H.w k) =
      (fun z y ↦ φ y (z y)) ∘ ⇑(TensorProduct.piRight Γ(S, V) Γ(S, V) Γ(T, ⊤)
        (fun y : Fin (k + 1) → ι ↦ Γ(ℱ, ⨅ l, U (y l)))) := rfl
  rw [key]
  refine Function.Bijective.comp ?_ (LinearEquiv.bijective _)
  refine ⟨fun z z' hzz' ↦ funext fun y ↦ (hφ y).1 (congr_fun hzz' y), fun c ↦ ?_⟩
  choose z hz using fun y ↦ (hφ y).2 (c y)
  exact ⟨z, funext hz⟩


omit [Fintype ι] [DecidableEq ι] in
lemma presheaf_map_eqToHom_eq_homOfLE (P : Y.Modules) {V₁ V₂ : Y.Opens} (h : V₂ = V₁)
    (m : Γ(P, V₁)) : P.presheaf.map (eqToHom h).op m = P.presheaf.map (homOfLE h.le).op m :=
  rfl

/-- **Base change of Čech cochains commutes with the differentials.** -/
theorem cechBaseChange_d (k : ℕ) (z : Γ(T, ⊤) ⊗[Γ(S, V)] CechCochain U ℱ.presheaf k) :
    cechBaseChange hfV ℱ U hUV hf hU w (k + 1)
        ((cechDifferential ℱ U hUV hU k).lTensor Γ(T, ⊤) z) =
      ((cechComplex (fun i ↦ g ⁻¹ᵁ U i)).obj ((pullback g).obj ℱ).presheaf).d k (k + 1)
        (cechBaseChange hfV ℱ U hUV hf hU w k z) := by
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simp only [map_add, hz, hz']
  | tmul b c =>
    funext y
    rw [LinearMap.lTensor_tmul, cechBaseChange_tmul, cechDifferential_apply,
      cechComplex_d_apply, cechComplex_d_apply]
    simp only [pullbackSection, map_sum, map_zsmul, Finset.smul_sum, smul_comm _ ((-1 : ℤ) ^ _)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    congr 1
    rw [cechBaseChange_tmul]
    change ((pullback g).obj ℱ).presheaf.map _ (_ • pullbackSection g
      (ℱ.presheaf.map (homOfLE _).op _)) = ((pullback g).obj ℱ).presheaf.map _
        (((pullback g).obj ℱ).presheaf.map _ (_ • pullbackSection g _))
    rw [pullbackSection_map, presheaf_map_eqToHom_eq_homOfLE, presheaf_map_eqToHom_eq_homOfLE,
      presheaf_map_appLE_smul, presheaf_map_appLE_smul, presheaf_map_appLE_smul,
      TopCat.Presheaf.map_homOfLE_map_homOfLE_apply, TopCat.Presheaf.map_homOfLE_map_homOfLE_apply]


omit [Fintype ι] [DecidableEq ι] in
include hf in
/-- **Exactness of the base-changed Čech complex.** If the Čech complex of `g^* ℱ` for the cover
`g⁻¹ U` is exact in degree `1`, then so is `B ⊗[A] Č(U, ℱ)`. -/
theorem exact_lTensor_cechDifferential [Finite ι] (H : IsPullback g iY iX f)
    (hV : IsAffineOpen V) [IsAffine T]
    (hUa : ∀ (k : ℕ) (y : Fin (k + 1) → ι), IsAffineOpen (⨅ l, U (y l)))
    (he : ∀ (k : ℕ) (y : Fin (k + 1) → ι), ∃ e : Γ(ℱ, ⨅ l, U (y l)), IsFreeGenerator e)
    (hex : ((cechComplex (fun i ↦ g ⁻¹ᵁ U i)).obj ((pullback g).obj ℱ).presheaf).ExactAt 1) :
    Function.Exact ((cechDifferential ℱ U hUV hU 0).lTensor Γ(T, ⊤))
      ((cechDifferential ℱ U hUV hU 1).lTensor Γ(T, ⊤)) := by
  classical
  have := Fintype.ofFinite ι
  rw [exactAt_cechComplex_iff] at hex
  have hb (k : ℕ) := cechBaseChange_bijective hfV ℱ U hUV hf hU H hV hUa he k
  intro z
  constructor
  · intro hz
    have h1 := cechBaseChange_d hfV ℱ U hUV hf hU H.w 1 z
    rw [hz, map_zero] at h1
    obtain ⟨c, hc⟩ := hex _ h1.symm
    obtain ⟨z₀, rfl⟩ := (hb 0).2 c
    refine ⟨z₀, (hb 1).1 ?_⟩
    rw [cechBaseChange_d]
    exact hc
  · rintro ⟨z₀, rfl⟩
    refine (hb 2).1 ?_
    rw [cechBaseChange_d, cechBaseChange_d, map_zero]
    exact congr($(((cechComplex (fun i ↦ g ⁻¹ᵁ U i)).obj
      ((pullback g).obj ℱ).presheaf).d_comp_d 0 1 2) _)

end Cech

section Sheaf

open TopCat.Presheaf

variable (ℱ : X.Modules) {ι : Type u} (U : ι → X.Opens) {W₀ : X.Opens} (hU : ⨆ i, U i = W₀)

include hU in
lemma iInf_le_of_iSup_eq (z : Fin 1 → ι) : ⨅ l, U (z l) ≤ W₀ :=
  (iInf_le _ 0).trans (hU ▸ le_iSup U (z 0))

include hU in
/-- The Čech `0`-cochains of a section are determined by the section: two sections over the
union of a cover with the same restrictions to its members agree. -/
lemma eq_of_forall_presheaf_map_eq (s t : Γ(ℱ, W₀))
    (h : ∀ z : Fin 1 → ι, ℱ.presheaf.map (homOfLE (iInf_le_of_iSup_eq U hU z)).op s =
      ℱ.presheaf.map (homOfLE (iInf_le_of_iSup_eq U hU z)).op t) : s = t :=
  TopCat.Sheaf.eq_of_locally_eq' ⟨ℱ.presheaf, ℱ.isSheaf⟩ (fun z : Fin 1 → ι ↦ ⨅ l, U (z l)) W₀
    (fun z ↦ homOfLE (iInf_le_of_iSup_eq U hU z))
    (fun x hx ↦ by
      rw [← hU] at hx
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨fun _ ↦ i, by simpa using hi⟩) s t h

include hU in
/-- **Čech `0`-cocycles glue.** A Čech `0`-cocycle of a cover of `W₀` is the family of
restrictions of a section over `W₀`. -/
lemma exists_presheaf_map_eq_of_cechComplex_d_eq_zero (c : CechCochain U ℱ.presheaf 0)
    (hc : ((cechComplex U).obj ℱ.presheaf).d 0 1 c = 0) :
    ∃ s : Γ(ℱ, W₀), ∀ z : Fin 1 → ι,
      ℱ.presheaf.map (homOfLE (iInf_le_of_iSup_eq U hU z)).op s = c z := by
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' ⟨ℱ.presheaf, ℱ.isSheaf⟩
    (fun z : Fin 1 → ι ↦ ⨅ l, U (z l)) W₀ (fun z ↦ homOfLE (iInf_le_of_iSup_eq U hU z))
    (fun x hx ↦ by
      rw [← hU] at hx
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨fun _ ↦ i, by simpa using hi⟩) c
    (fun z z' ↦ map_inf_eq_of_cechComplex_d_zero U ℱ.presheaf c hc z z')
  exact ⟨s, hs⟩

end Sheaf

end AlgebraicGeometry.Scheme.Modules
