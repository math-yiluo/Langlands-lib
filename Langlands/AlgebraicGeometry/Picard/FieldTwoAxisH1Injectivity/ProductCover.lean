import Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof

/-!
# Sections of a fibre product over products of affine opens

Let `P` be a fibre product of `X ⟶ Spec R` and `Y ⟶ Spec R` with projections `p₁`, `p₂`. For
opens `U` of `X` and `V` of `Y`, the map `a ⊗ b ↦ p₁^♯ a * p₂^♯ b` from
`Γ(X, U) ⊗[R] Γ(Y, V)` to `Γ(P, p₁⁻¹ U ⊓ p₂⁻¹ V)` is bijective when `U` and `V` are affine. For
finite families of affine opens `U a` and `V b`, the induced map
`(∏ Γ(X, U a)) ⊗[R] (∏ Γ(Y, V b)) → ∏ Γ(P, p₁⁻¹ U a ⊓ p₂⁻¹ V b)` is bijective as well.

The file also records the compatibility of these maps with restriction in either factor and
with pulling back along a section through a rational point, and that a Čech `0`-cocycle of the
structure sheaf is a constant when global functions are constants.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.Picard.FieldTwoAxisH1Injectivity

open Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof

section Restriction

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (p : X ⟶ Spec R)
  [∀ W : X.Opens, Algebra R Γ(X, W)]
  (halg : ∀ W : X.Opens, algebraMap R Γ(X, W) = (secHom p W).hom)

/-- Restriction of families of sections along a reindexing `σ` with `U' a' ≤ U (σ a')`. -/
noncomputable def resPi {α α' : Type*} (U : α → X.Opens) (U' : α' → X.Opens) (σ : α' → α)
    (hσ : ∀ a', U' a' ≤ U (σ a')) : (∀ a, Γ(X, U a)) →ₗ[R] ∀ a', Γ(X, U' a') :=
  LinearMap.pi fun a' ↦ (resAlgHom p halg (hσ a')).toLinearMap ∘ₗ LinearMap.proj (σ a')

lemma resPi_apply {α α' : Type*} (U : α → X.Opens) (U' : α' → X.Opens) (σ : α' → α)
    (hσ : ∀ a', U' a' ≤ U (σ a')) (x : ∀ a, Γ(X, U a)) (a' : α') :
    resPi p halg U U' σ hσ x a' = (X.presheaf.map (homOfLE (hσ a')).op).hom (x (σ a')) :=
  rfl

/-- The Čech differential `∏ Γ(X, U a) → ∏ Γ(X, U a ⊓ U a')`, `x ↦ x a' - x a`. -/
noncomputable def cechD {α : Type*} (U : α → X.Opens) :
    (∀ a, Γ(X, U a)) →ₗ[R] ∀ aa : α × α, Γ(X, U aa.1 ⊓ U aa.2) :=
  resPi p halg U (fun aa ↦ U aa.1 ⊓ U aa.2) Prod.snd (fun _ ↦ inf_le_right) -
    resPi p halg U (fun aa ↦ U aa.1 ⊓ U aa.2) Prod.fst (fun _ ↦ inf_le_left)

lemma cechD_apply {α : Type*} (U : α → X.Opens) (x : ∀ a, Γ(X, U a)) (aa : α × α) :
    cechD p halg U x aa = (X.presheaf.map (homOfLE inf_le_right).op).hom (x aa.2) -
      (X.presheaf.map (homOfLE inf_le_left).op).hom (x aa.1) :=
  rfl

lemma cechD_one {α : Type*} (U : α → X.Opens) : cechD p halg U 1 = 0 := by
  funext aa
  rw [cechD_apply]
  simp

/-- A Čech `0`-cocycle of the structure sheaf on an open cover is a constant, provided every
global function comes from `R`. -/
lemma exists_eq_smul_one_of_cechD_eq_zero {α : Type*} (U : α → X.Opens) (hcov : ⊤ ≤ iSup U)
    (hglob : Function.Surjective (secHom p ⊤).hom) (x : ∀ a, Γ(X, U a))
    (hx : cechD p halg U x = 0) : ∃ r : R, x = r • 1 := by
  have hc : TopCat.Presheaf.IsCompatible X.sheaf.1 U x := by
    intro a a'
    have e := congr_fun hx (a, a')
    rw [cechD_apply, Pi.zero_apply, sub_eq_zero] at e
    exact e.symm
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' U ⊤ (fun _ ↦ homOfLE le_top) hcov x hc
  obtain ⟨r, rfl⟩ := hglob s
  refine ⟨r, funext fun a ↦ ?_⟩
  rw [← hs a, Pi.smul_apply, Pi.one_apply, ← Algebra.algebraMap_eq_smul_one, halg]
  change (secHom p ⊤ ≫ X.presheaf.map (homOfLE le_top).op).hom r = _
  rw [secHom_map]

end Restriction

variable {R : CommRingCat.{u}} {X Y P : Scheme.{u}} {πX : X ⟶ Spec R} {πY : Y ⟶ Spec R}
  {p₁ : P ⟶ X} {p₂ : P ⟶ Y}

variable (p₁ p₂) in
/-- The open `p₁⁻¹ U ⊓ p₂⁻¹ V` of the fibre product. -/
abbrev prodOpen (U : X.Opens) (V : Y.Opens) : P.Opens :=
  p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ V

section Pair

lemma secHom_comp_fst (U : X.Opens) (V : Y.Opens) :
    secHom πX U ≫ p₁.appLE U (prodOpen p₁ p₂ U V) inf_le_left =
      secHom (p₁ ≫ πX) (prodOpen p₁ p₂ U V) := by
  rw [secHom, secHom, Category.assoc, Scheme.Hom.appLE_comp_appLE]

lemma secHom_comp_snd (U : X.Opens) (V : Y.Opens) :
    secHom πY V ≫ p₂.appLE V (prodOpen p₁ p₂ U V) inf_le_right =
      secHom (p₂ ≫ πY) (prodOpen p₁ p₂ U V) := by
  rw [secHom, secHom, Category.assoc, Scheme.Hom.appLE_comp_appLE]

lemma isAffineOpen_prodOpen (hP : IsPullback p₁ p₂ πX πY) {U : X.Opens} {V : Y.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) : IsAffineOpen (prodOpen p₁ p₂ U V) := by
  have : IsAffine _ := isAffineOpen_top (Spec R)
  have : IsAffine _ := hU
  have : IsAffine _ := hV
  exact .of_isIso (Scheme.Hom.isPullback_resLE hP (US := ⊤)
    (le_top.trans_eq (Scheme.Hom.preimage_top _).symm)
    (le_top.trans_eq (Scheme.Hom.preimage_top _).symm) rfl).isoPullback.hom

lemma iSup_prodOpen_eq_top {α β : Type*} {U : α → X.Opens} {V : β → Y.Opens}
    (hU : ⊤ ≤ iSup U) (hV : ⊤ ≤ iSup V) :
    ⊤ ≤ ⨆ ab : α × β, prodOpen p₁ p₂ (U ab.1) (V ab.2) := by
  intro z _
  obtain ⟨a, ha⟩ := Opens.mem_iSup.mp (hU (Set.mem_univ (p₁ z)))
  obtain ⟨b, hb⟩ := Opens.mem_iSup.mp (hV (Set.mem_univ (p₂ z)))
  exact Opens.mem_iSup.mpr ⟨(a, b), ha, hb⟩

set_option backward.isDefEq.respectTransparency false in
/-- Over affine opens `U` and `V`, the square of section rings of the fibre square is a
pushout. -/
lemma isPushout_appLE (hP : IsPullback p₁ p₂ πX πY) {U : X.Opens} {V : Y.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    IsPushout (secHom πX U) (secHom πY V) (p₁.appLE U (prodOpen p₁ p₂ U V) inf_le_left)
      (p₂.appLE V (prodOpen p₁ p₂ U V) inf_le_right) := by
  have h3 := (isIso_pushoutSection_iff hP (US := ⊤) (UT := V) (UX := U)
    (le_top.trans_eq (Scheme.Hom.preimage_top _).symm)
    (le_top.trans_eq (Scheme.Hom.preimage_top _).symm) rfl).mp
    (isIso_pushoutSection_of_isAffineOpen hP _ _ rfl (isAffineOpen_top _) hV hU)
  refine h3.of_iso' (Scheme.ΓSpecIso R).symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp [secHom]
  · simp [secHom]
  · simp
  · simp

variable [∀ W : X.Opens, Algebra R Γ(X, W)]
  (halgX : ∀ W : X.Opens, algebraMap R Γ(X, W) = (secHom πX W).hom)
  [∀ W : Y.Opens, Algebra R Γ(Y, W)]
  (halgY : ∀ W : Y.Opens, algebraMap R Γ(Y, W) = (secHom πY W).hom)

include halgX in
lemma ofHom_algebraMap_eq_X (U : X.Opens) :
    CommRingCat.ofHom (algebraMap R Γ(X, U)) = secHom πX U := by
  rw [halgX]; rfl

include halgY in
lemma ofHom_algebraMap_eq_Y (V : Y.Opens) :
    CommRingCat.ofHom (algebraMap R Γ(Y, V)) = secHom πY V := by
  rw [halgY]; rfl

/-- The canonical ring map `Γ(X, U) ⊗[R] Γ(Y, V) → Γ(P, p₁⁻¹ U ⊓ p₂⁻¹ V)`. -/
noncomputable def tensorSec (hP : IsPullback p₁ p₂ πX πY) (U : X.Opens) (V : Y.Opens) :
    CommRingCat.of (Γ(X, U) ⊗[R] Γ(Y, V)) ⟶ Γ(P, prodOpen p₁ p₂ U V) :=
  (CommRingCat.isPushout_tensorProduct R Γ(X, U) Γ(Y, V)).desc
    (p₁.appLE U _ inf_le_left) (p₂.appLE V _ inf_le_right) (by
      rw [ofHom_algebraMap_eq_X halgX, ofHom_algebraMap_eq_Y halgY]
      exact (secHom_comp_fst U V).trans ((congrArg (fun q ↦ secHom q _) hP.w).trans
        (secHom_comp_snd U V).symm))

lemma tensorSec_tmul (hP : IsPullback p₁ p₂ πX πY) (U : X.Opens) (V : Y.Opens) (a : Γ(X, U))
    (b : Γ(Y, V)) :
    (tensorSec halgX halgY hP U V).hom (a ⊗ₜ b) =
      (p₁.appLE U (prodOpen p₁ p₂ U V) inf_le_left).hom a *
        (p₂.appLE V (prodOpen p₁ p₂ U V) inf_le_right).hom b := by
  have e : (a ⊗ₜ[R] b : Γ(X, U) ⊗[R] Γ(Y, V)) =
      Algebra.TensorProduct.includeLeftRingHom a * Algebra.TensorProduct.includeRight b := by
    simp
  rw [e, map_mul]
  congr 1
  · exact congr($((CommRingCat.isPushout_tensorProduct R Γ(X, U) Γ(Y, V)).inl_desc _ _ _).hom a)
  · exact congr($((CommRingCat.isPushout_tensorProduct R Γ(X, U) Γ(Y, V)).inr_desc _ _ _).hom b)

lemma tensorSec_bijective (hP : IsPullback p₁ p₂ πX πY) {U : X.Opens} {V : Y.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    Function.Bijective (tensorSec halgX halgY hP U V).hom := by
  have h : IsPushout (CommRingCat.ofHom (algebraMap R Γ(X, U)))
      (CommRingCat.ofHom (algebraMap R Γ(Y, V))) (p₁.appLE U (prodOpen p₁ p₂ U V) inf_le_left)
      (p₂.appLE V (prodOpen p₁ p₂ U V) inf_le_right) := by
    rw [ofHom_algebraMap_eq_X halgX, ofHom_algebraMap_eq_Y halgY]
    exact isPushout_appLE hP hU hV
  have h1 := CommRingCat.isPushout_tensorProduct R Γ(X, U) Γ(Y, V)
  have : (h1.isoIsPushout _ _ h).hom = tensorSec halgX halgY hP U V :=
    h1.hom_ext (by simp [tensorSec]) (by simp [tensorSec])
  rw [← this]
  exact (h1.isoIsPushout _ _ h).commRingCatIsoToRingEquiv.bijective

end Pair

section Family

variable [∀ W : X.Opens, Algebra R Γ(X, W)]
  (halgX : ∀ W : X.Opens, algebraMap R Γ(X, W) = (secHom πX W).hom)
  [∀ W : Y.Opens, Algebra R Γ(Y, W)]
  (halgY : ∀ W : Y.Opens, algebraMap R Γ(Y, W) = (secHom πY W).hom)
  (hP : IsPullback p₁ p₂ πX πY) {α β : Type*} (U : α → X.Opens) (V : β → Y.Opens)

/-- The map `(∏ Γ(X, U a)) ⊗[R] (∏ Γ(Y, V b)) → ∏ Γ(P, p₁⁻¹ U a ⊓ p₂⁻¹ V b)`. -/
noncomputable def tensorFam :
    (∀ a, Γ(X, U a)) ⊗[R] (∀ b, Γ(Y, V b)) →+ ∀ a b, Γ(P, prodOpen p₁ p₂ (U a) (V b)) :=
  AddMonoidHom.pi fun a ↦ AddMonoidHom.pi fun b ↦
    (tensorSec halgX halgY hP (U a) (V b)).hom.toAddMonoidHom.comp
      (TensorProduct.map (LinearMap.proj a) (LinearMap.proj b)).toAddMonoidHom

lemma tensorFam_apply (t : (∀ a, Γ(X, U a)) ⊗[R] (∀ b, Γ(Y, V b))) (a : α) (b : β) :
    tensorFam halgX halgY hP U V t a b = (tensorSec halgX halgY hP (U a) (V b)).hom
      (TensorProduct.map (LinearMap.proj a) (LinearMap.proj b) t) :=
  rfl

lemma tensorFam_tmul (x : ∀ a, Γ(X, U a)) (y : ∀ b, Γ(Y, V b)) (a : α) (b : β) :
    tensorFam halgX halgY hP U V (x ⊗ₜ y) a b =
      (p₁.appLE (U a) (prodOpen p₁ p₂ (U a) (V b)) inf_le_left).hom (x a) *
        (p₂.appLE (V b) (prodOpen p₁ p₂ (U a) (V b)) inf_le_right).hom (y b) := by
  rw [tensorFam_apply, TensorProduct.map_tmul, tensorSec_tmul]
  rfl

lemma tensorFam_bijective [Finite α] [Finite β] (hU : ∀ a, IsAffineOpen (U a))
    (hV : ∀ b, IsAffineOpen (V b)) : Function.Bijective (tensorFam halgX halgY hP U V) := by
  classical
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  let ψ := TensorProduct.piLeft (R := R) (N := ∀ b, Γ(Y, V b)) (fun a ↦ Γ(X, U a)) ≪≫ₗ
    LinearEquiv.piCongrRight fun a ↦
      TensorProduct.piRight (R := R) (S := R) (N := Γ(X, U a)) (fun b ↦ Γ(Y, V b))
  have hψ : ∀ t a b, ψ t a b = TensorProduct.map (LinearMap.proj a) (LinearMap.proj b) t := by
    intro t a b
    induction t with
    | tmul x y => simp [ψ]
    | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  have e : ⇑(tensorFam halgX halgY hP U V) =
      (fun F a b ↦ (tensorSec halgX halgY hP (U a) (V b)).hom (F a b)) ∘ ψ := by
    funext t a b
    simp only [Function.comp_apply, hψ]
    rfl
  rw [e]
  exact (Function.Bijective.piMap fun a ↦ Function.Bijective.piMap fun b ↦
    tensorSec_bijective halgX halgY hP (hU a) (hV b)).comp ψ.bijective

/-- Restriction in the second factor. -/
lemma tensorFam_lTensor_resPi {β' : Type*} (V' : β' → Y.Opens) (σ : β' → β)
    (hσ : ∀ b', V' b' ≤ V (σ b')) (t : (∀ a, Γ(X, U a)) ⊗[R] (∀ b, Γ(Y, V b))) (a : α)
    (b' : β') :
    tensorFam halgX halgY hP U V' ((resPi πY halgY V V' σ hσ).lTensor _ t) a b' =
      (P.presheaf.map (homOfLE (inf_le_inf_left _ (Scheme.Hom.preimage_mono _ (hσ b')))).op).hom
        (tensorFam halgX halgY hP U V t a (σ b')) := by
  induction t with
  | tmul x y =>
    rw [LinearMap.lTensor_tmul, tensorFam_tmul, tensorFam_tmul, map_mul, resPi_apply]
    congr 1
    · rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
    · rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map,
        Scheme.Hom.map_appLE]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

/-- Restriction in the first factor. -/
lemma tensorFam_rTensor_resPi {α' : Type*} (U' : α' → X.Opens) (σ : α' → α)
    (hσ : ∀ a', U' a' ≤ U (σ a')) (t : (∀ a, Γ(X, U a)) ⊗[R] (∀ b, Γ(Y, V b))) (a' : α')
    (b : β) :
    tensorFam halgX halgY hP U' V ((resPi πX halgX U U' σ hσ).rTensor _ t) a' b =
      (P.presheaf.map (homOfLE (inf_le_inf_right _ (Scheme.Hom.preimage_mono _ (hσ a')))).op).hom
        (tensorFam halgX halgY hP U V t (σ a') b) := by
  induction t with
  | tmul x y =>
    rw [LinearMap.rTensor_tmul, tensorFam_tmul, tensorFam_tmul, map_mul, resPi_apply]
    congr 1
    · rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map,
        Scheme.Hom.map_appLE]
    · rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

end Family

section Axis

lemma id_appLE_apply {Z : Scheme.{u}} (W : Z.Opens) (e : W ≤ (𝟙 Z) ⁻¹ᵁ W) (x : Γ(Z, W)) :
    (Scheme.Hom.appLE (𝟙 Z) W W e).hom x = x := by
  change (𝟙 Γ(Z, W) ≫ Z.presheaf.map (𝟙 (op W))).hom x = x
  rw [Category.id_comp, Z.presheaf.map_id]
  rfl

variable [∀ W : X.Opens, Algebra R Γ(X, W)]
  (halgX : ∀ W : X.Opens, algebraMap R Γ(X, W) = (secHom πX W).hom)
  [∀ W : Y.Opens, Algebra R Γ(Y, W)]
  (halgY : ∀ W : Y.Opens, algebraMap R Γ(Y, W) = (secHom πY W).hom)

include halgX in
lemma appLE_secHom_of_section (x₀ : Spec R ⟶ X) (hx₀ : x₀ ≫ πX = 𝟙 _) (W : X.Opens)
    (hW : ⊤ ≤ x₀ ⁻¹ᵁ W) (r : R) :
    ((x₀.appLE W ⊤ hW).hom (algebraMap R Γ(X, W) r)) = (Scheme.ΓSpecIso R).inv.hom r := by
  rw [halgX, secHom, ← CommRingCat.comp_apply, Category.assoc, Scheme.Hom.appLE_comp_appLE,
    appLE_congr_hom hx₀, CommRingCat.comp_apply, id_appLE_apply]

/-- Evaluation of sections over `W` at an `R`-point `x₀` of `X` lying in `W`, as an `R`-algebra
map `Γ(X, W) → R`. -/
noncomputable def evalSec (x₀ : Spec R ⟶ X) (hx₀ : x₀ ≫ πX = 𝟙 _) (W : X.Opens)
    (hW : ⊤ ≤ x₀ ⁻¹ᵁ W) : Γ(X, W) →ₐ[R] R where
  toRingHom := (x₀.appLE W ⊤ hW ≫ (Scheme.ΓSpecIso R).hom).hom
  commutes' r := by
    change (Scheme.ΓSpecIso R).hom.hom ((x₀.appLE W ⊤ hW).hom (algebraMap R Γ(X, W) r)) = r
    rw [appLE_secHom_of_section halgX x₀ hx₀ W hW, Iso.inv_hom_id_apply]

lemma evalSec_apply (x₀ : Spec R ⟶ X) (hx₀ : x₀ ≫ πX = 𝟙 _) (W : X.Opens)
    (hW : ⊤ ≤ x₀ ⁻¹ᵁ W) (s : Γ(X, W)) :
    evalSec halgX x₀ hx₀ W hW s = (Scheme.ΓSpecIso R).hom.hom ((x₀.appLE W ⊤ hW).hom s) :=
  rfl

include halgY in
/-- Pulling back a section from the point `x₀` to `Y` along `πY` is the scalar given by
`evalSec`. -/
lemma appLE_comp_section (x₀ : Spec R ⟶ X) (hx₀ : x₀ ≫ πX = 𝟙 _) (W : X.Opens)
    (hW : ⊤ ≤ x₀ ⁻¹ᵁ W) (V : Y.Opens) (e : V ≤ (πY ≫ x₀) ⁻¹ᵁ W) (s : Γ(X, W)) :
    ((πY ≫ x₀).appLE W V e).hom s = algebraMap R Γ(Y, V) (evalSec halgX x₀ hx₀ W hW s) := by
  rw [← Scheme.Hom.appLE_comp_appLE πY x₀ W ⊤ V hW (le_top.trans_eq πY.preimage_top.symm),
    CommRingCat.comp_apply, halgY, evalSec_apply, secHom, CommRingCat.comp_apply,
    Iso.hom_inv_id_apply]

omit [∀ W : X.Opens, Algebra R Γ(X, W)] [∀ W : Y.Opens, Algebra R Γ(Y, W)] in
lemma le_preimage_axis₂ (x₀ : Spec R ⟶ X) (i₂ : Y ⟶ P)
    (h₁ : i₂ ≫ p₁ = πY ≫ x₀) (h₂ : i₂ ≫ p₂ = 𝟙 Y) (U : X.Opens) (hU : ⊤ ≤ x₀ ⁻¹ᵁ U)
    (V : Y.Opens) : V ≤ i₂ ⁻¹ᵁ prodOpen p₁ p₂ U V := by
  intro y hy
  refine ⟨?_, ?_⟩
  · change p₁ (i₂ y) ∈ U
    rw [← Scheme.Hom.comp_apply, h₁, Scheme.Hom.comp_apply]
    exact hU (Set.mem_univ _)
  · change p₂ (i₂ y) ∈ V
    rw [← Scheme.Hom.comp_apply, h₂]
    exact hy

omit [∀ W : X.Opens, Algebra R Γ(X, W)] [∀ W : Y.Opens, Algebra R Γ(Y, W)] in
lemma le_preimage_axis₁ (y₀ : Spec R ⟶ Y) (i₁ : X ⟶ P)
    (h₁ : i₁ ≫ p₁ = 𝟙 X) (h₂ : i₁ ≫ p₂ = πX ≫ y₀) (U : X.Opens) (V : Y.Opens)
    (hV : ⊤ ≤ y₀ ⁻¹ᵁ V) : U ≤ i₁ ⁻¹ᵁ prodOpen p₁ p₂ U V := by
  intro x hx
  refine ⟨?_, ?_⟩
  · change p₁ (i₁ x) ∈ U
    rw [← Scheme.Hom.comp_apply, h₁]
    exact hx
  · change p₂ (i₁ x) ∈ V
    rw [← Scheme.Hom.comp_apply, h₂, Scheme.Hom.comp_apply]
    exact hV (Set.mem_univ _)

variable (hP : IsPullback p₁ p₂ πX πY) {α β : Type*} (U : α → X.Opens) (V : β → Y.Opens)

/-- Restriction of the tensor map along the axis `i₂ = (x₀ ∘ πY, id) : Y ⟶ P` is evaluation at
`x₀` in the first factor. -/
lemma appLE_axis₂_tensorFam (x₀ : Spec R ⟶ X) (hx₀ : x₀ ≫ πX = 𝟙 _) (i₂ : Y ⟶ P)
    (h₁ : i₂ ≫ p₁ = πY ≫ x₀) (h₂ : i₂ ≫ p₂ = 𝟙 Y) (a₀ : α) (hU : ⊤ ≤ x₀ ⁻¹ᵁ U a₀)
    (t : (∀ a, Γ(X, U a)) ⊗[R] (∀ b, Γ(Y, V b))) (b : β) :
    (i₂.appLE (prodOpen p₁ p₂ (U a₀) (V b)) (V b)
        (le_preimage_axis₂ x₀ i₂ h₁ h₂ (U a₀) hU (V b))).hom
      (tensorFam halgX halgY hP U V t a₀ b) =
    TensorProduct.lid R _
      (((evalSec halgX x₀ hx₀ (U a₀) hU).toLinearMap ∘ₗ LinearMap.proj a₀).rTensor _ t) b := by
  induction t with
  | tmul x y =>
    rw [tensorFam_tmul, map_mul, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
      Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE, appLE_congr_hom h₁,
      appLE_congr_hom h₂, id_appLE_apply, appLE_comp_section halgX halgY x₀ hx₀ (U a₀) hU,
      LinearMap.rTensor_tmul, TensorProduct.lid_tmul, Pi.smul_apply, Algebra.smul_def]
    rfl
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

/-- Restriction of the tensor map along the axis `i₁ = (id, y₀ ∘ πX) : X ⟶ P` is evaluation at
`y₀` in the second factor. -/
lemma appLE_axis₁_tensorFam (y₀ : Spec R ⟶ Y) (hy₀ : y₀ ≫ πY = 𝟙 _) (i₁ : X ⟶ P)
    (h₁ : i₁ ≫ p₁ = 𝟙 X) (h₂ : i₁ ≫ p₂ = πX ≫ y₀) (b₀ : β) (hV : ⊤ ≤ y₀ ⁻¹ᵁ V b₀)
    (t : (∀ a, Γ(X, U a)) ⊗[R] (∀ b, Γ(Y, V b))) (a : α) :
    (i₁.appLE (prodOpen p₁ p₂ (U a) (V b₀)) (U a)
        (le_preimage_axis₁ y₀ i₁ h₁ h₂ (U a) (V b₀) hV)).hom
      (tensorFam halgX halgY hP U V t a b₀) =
    TensorProduct.rid R _
      (((evalSec halgY y₀ hy₀ (V b₀) hV).toLinearMap ∘ₗ LinearMap.proj b₀).lTensor _ t) a := by
  induction t with
  | tmul x y =>
    rw [tensorFam_tmul, map_mul, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
      Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE, appLE_congr_hom h₁,
      appLE_congr_hom h₂, id_appLE_apply, appLE_comp_section halgY halgX y₀ hy₀ (V b₀) hV,
      LinearMap.lTensor_tmul, TensorProduct.rid_tmul, Pi.smul_apply, Algebra.smul_def, mul_comm]
    rfl
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

end Axis

end Langlands.AlgebraicGeometry.Picard.FieldTwoAxisH1Injectivity
