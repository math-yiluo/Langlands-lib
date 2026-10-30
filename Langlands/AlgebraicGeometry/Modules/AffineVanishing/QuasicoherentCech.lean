import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.RingTheory.Ideal.Operations
import Langlands.Cohomology.CechCochains

/-!
# Čech exactness of quasi-coherent modules on standard affine covers

For a quasi-coherent `𝒪_X`-module `M`, an affine open `W` of a scheme `X` and finitely many
`g i ∈ Γ(X, W)` generating the unit ideal, the ordered Čech complex of `M` for the basic opens
`D(g i)` is exact in every positive degree. The localization facts on affine opens are
transported from Mathlib's description of quasi-coherent modules on `Spec R`.
-/

universe u

open CategoryTheory Opposite TopologicalSpace Filter AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules.AffineVanishing

open Langlands.Cohomology

section Spec

variable {R : CommRingCat.{u}} (N : (Spec R).Modules) [N.IsQuasicoherent]

lemma spec_exists_pow_smul_eq_map (f : R) {D : (Spec R).Opens}
    (hD : PrimeSpectrum.basicOpen f = D) (s : Γ(N, D)) :
    ∃ (n : ℕ) (y : Γ(N, ⊤)), N.presheaf.map (homOfLE le_top : D ⟶ ⊤).op y = f ^ n • s := by
  subst hD
  have h := ((isIso_fromTildeΓ_iff_isLocalizing N).1 inferInstance) f
  obtain ⟨⟨y, _, n, rfl⟩, hy⟩ := h.surj s
  exact ⟨n, y, hy.symm⟩

lemma spec_exists_pow_smul_eq_zero (f : R) {D : (Spec R).Opens}
    (hD : PrimeSpectrum.basicOpen f = D) (t : Γ(N, ⊤))
    (ht : N.presheaf.map (homOfLE le_top : D ⟶ ⊤).op t = 0) :
    ∃ n : ℕ, f ^ n • t = 0 := by
  subst hD
  have h := ((isIso_fromTildeΓ_iff_isLocalizing N).1 inferInstance) f
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := h.exists_of_eq (x₁ := t) (x₂ := 0) (ht.trans (map_zero _).symm)
  exact ⟨n, hn.trans (smul_zero _)⟩

end Spec

variable {X : Scheme.{u}}

/-- Restriction of functions along an inclusion of opens. -/
def rres {U V : X.Opens} (h : U ≤ V) : Γ(X, V) →+* Γ(X, U) :=
  (X.presheaf.map (homOfLE h).op).hom

@[simp]
lemma rres_rres {U V W : X.Opens} (h₁ : U ≤ V) (h₂ : V ≤ W) (r : Γ(X, W)) :
    rres h₁ (rres h₂ r) = rres (h₁.trans h₂) r := by
  simp only [rres, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

@[simp]
lemma rres_self {U : X.Opens} (h : U ≤ U) (r : Γ(X, U)) : rres h r = r := by
  simp only [rres]
  change (X.presheaf.map (𝟙 (op U))).hom r = r
  rw [X.presheaf.map_id]
  rfl

lemma basicOpen_rres {U V : X.Opens} (h : U ≤ V) (r : Γ(X, V)) :
    X.basicOpen (rres h r) = U ⊓ X.basicOpen r :=
  Scheme.basicOpen_res X r (homOfLE h).op

lemma res_smul (M : X.Modules) {U V : X.Opens} (h : U ≤ V) (r : Γ(X, V)) (x : Γ(M, V)) :
    Cech.res (P := M.presheaf) h (r • x) = rres h r • Cech.res h x :=
  M.map_smul (homOfLE h) r x

section Affine

variable {V : X.Opens} (hV : IsAffineOpen V)

lemma image_fromSpec_le (U : (Spec Γ(X, V)).Opens) : hV.fromSpec ''ᵁ U ≤ V :=
  (hV.fromSpec.image_le_opensRange U).trans hV.opensRange_fromSpec.le

lemma image_fromSpec_top : hV.fromSpec ''ᵁ ⊤ = V :=
  hV.fromSpec.image_top_eq_opensRange.trans hV.opensRange_fromSpec

lemma ΓSpecIso_inv_map_appIso_inv (U : (Spec Γ(X, V)).Opens) :
    (Scheme.ΓSpecIso Γ(X, V)).inv ≫ (Spec Γ(X, V)).presheaf.map U.leTop.op ≫
      (hV.fromSpec.appIso U).inv = X.presheaf.map (homOfLE (image_fromSpec_le hV U)).op := by
  rw [← cancel_mono (hV.fromSpec.appIso U).hom, Category.assoc, Category.assoc, Iso.inv_hom_id,
    Category.comp_id, Scheme.Hom.appIso_hom, Scheme.Hom.naturality_assoc,
    hV.fromSpec_app_self, Category.assoc]
  simp only [← Functor.map_comp]
  rfl

lemma appIso_inv_map_ΓSpecIso_inv (U : (Spec Γ(X, V)).Opens) (r : Γ(X, V)) :
    (hV.fromSpec.appIso U).inv ((Spec Γ(X, V)).presheaf.map U.leTop.op
      ((Scheme.ΓSpecIso Γ(X, V)).inv r)) = rres (image_fromSpec_le hV U) r := by
  rw [rres, ← ΓSpecIso_inv_map_appIso_inv hV U]
  rfl

variable (M : X.Modules)

lemma restrictAppIso_hom_smul (U : (Spec Γ(X, V)).Opens) (r : Γ(X, V))
    (x : Γ(M.restrict hV.fromSpec, U)) :
    (M.restrictAppIso hV.fromSpec U).hom (r • x) =
      rres (image_fromSpec_le hV U) r • (M.restrictAppIso hV.fromSpec U).hom x := by
  rw [← appIso_inv_map_ΓSpecIso_inv]
  rfl

variable [M.IsQuasicoherent]

include hV

lemma exists_pow_smul_eq_res_aux (h : Γ(X, V)) (s : Γ(M, X.basicOpen h)) :
    ∃ (n : ℕ) (t : Γ(M, V)),
      Cech.res (X.basicOpen_le h) t = rres (X.basicOpen_le h) h ^ n • s := by
  let D' : (Spec Γ(X, V)).Opens := PrimeSpectrum.basicOpen h
  have e₁ : hV.fromSpec ''ᵁ D' = X.basicOpen h := hV.fromSpec_image_basicOpen h
  have e₂ : hV.fromSpec ''ᵁ ⊤ = V := image_fromSpec_top hV
  obtain ⟨n, x, hx⟩ := spec_exists_pow_smul_eq_map (M.restrict hV.fromSpec) h (D := D') rfl
    ((M.restrictAppIso hV.fromSpec D').inv (Cech.res e₁.le s))
  refine ⟨n, Cech.res e₂.ge ((M.restrictAppIso hV.fromSpec ⊤).hom x), ?_⟩
  have hx' : Cech.res (P := M.presheaf) (Scheme.Hom.image_mono _ le_top :
      hV.fromSpec ''ᵁ D' ≤ hV.fromSpec ''ᵁ ⊤) ((M.restrictAppIso hV.fromSpec ⊤).hom x) =
      rres (image_fromSpec_le hV D') (h ^ n) • Cech.res e₁.le s := by
    have := congrArg (M.restrictAppIso hV.fromSpec D').hom hx
    rw [restrictAppIso_hom_smul, Iso.inv_hom_id_apply] at this
    exact this
  calc Cech.res (X.basicOpen_le h) (Cech.res e₂.ge ((M.restrictAppIso hV.fromSpec ⊤).hom x))
      = Cech.res e₁.ge (Cech.res (Scheme.Hom.image_mono _ le_top)
          ((M.restrictAppIso hV.fromSpec ⊤).hom x)) := by
        rw [Cech.res_res, Cech.res_res]
    _ = Cech.res e₁.ge (rres (image_fromSpec_le hV D') (h ^ n) • Cech.res e₁.le s) := by
        rw [hx']
    _ = rres (X.basicOpen_le h) h ^ n • s := by
        rw [res_smul, rres_rres, Cech.res_res, Cech.res_self, ← map_pow]

lemma exists_pow_smul_eq_zero_aux (h : Γ(X, V)) (t : Γ(M, V))
    (ht : Cech.res (X.basicOpen_le h) t = 0) : ∃ n : ℕ, h ^ n • t = 0 := by
  let D' : (Spec Γ(X, V)).Opens := PrimeSpectrum.basicOpen h
  have e₁ : hV.fromSpec ''ᵁ D' = X.basicOpen h := hV.fromSpec_image_basicOpen h
  have e₂ : hV.fromSpec ''ᵁ ⊤ = V := image_fromSpec_top hV
  have h₀ : Cech.res (P := M.presheaf) (Scheme.Hom.image_mono _ le_top :
      hV.fromSpec ''ᵁ D' ≤ hV.fromSpec ''ᵁ ⊤) (Cech.res e₂.le t) = 0 := by
    rw [Cech.res_res, ← Cech.res_res e₁.le (X.basicOpen_le h), ht, map_zero]
  obtain ⟨n, hn⟩ := spec_exists_pow_smul_eq_zero (M.restrict hV.fromSpec) h (D := D') rfl
    ((M.restrictAppIso hV.fromSpec ⊤).inv (Cech.res e₂.le t)) h₀
  refine ⟨n, ?_⟩
  have h₁ := congrArg (fun x => Cech.res (P := M.presheaf) e₂.ge
    ((M.restrictAppIso hV.fromSpec ⊤).hom x)) hn
  simp only [restrictAppIso_hom_smul, Iso.inv_hom_id_apply, map_zero, res_smul, rres_rres,
    rres_self, Cech.res_res, Cech.res_self] at h₁
  exact h₁

omit hV [M.IsQuasicoherent] in
lemma eventually_exists_res_eq_pow_smul_of_exists (h : Γ(X, V)) {D : X.Opens}
    (hD : X.basicOpen h = D) (hDV : D ≤ V) (s : Γ(M, D))
    (hex : ∀ s : Γ(M, X.basicOpen h), ∃ (n : ℕ) (t : Γ(M, V)),
      Cech.res (X.basicOpen_le h) t = rres (X.basicOpen_le h) h ^ n • s) :
    ∀ᶠ m in atTop, ∃ t : Γ(M, V), Cech.res hDV t = rres hDV h ^ m • s := by
  subst hD
  obtain ⟨n, t, ht⟩ := hex s
  refine eventually_atTop.2 ⟨n, fun m hm => ⟨h ^ (m - n) • t, ?_⟩⟩
  rw [res_smul, ht, smul_smul, map_pow, ← pow_add, Nat.sub_add_cancel hm]

/-- Sections over a basic open `D(h)` of an affine open `V` extend to `V` after multiplication
by a high power of `h`. -/
lemma eventually_exists_res_eq_pow_smul (h : Γ(X, V)) {D : X.Opens}
    (hD : X.basicOpen h = D) (hDV : D ≤ V) (s : Γ(M, D)) :
    ∀ᶠ m in atTop, ∃ t : Γ(M, V), Cech.res hDV t = rres hDV h ^ m • s :=
  eventually_exists_res_eq_pow_smul_of_exists M h hD hDV s (exists_pow_smul_eq_res_aux hV M h)

/-- Sections over an affine open `V` vanishing on a basic open `D(h)` are killed by a high power
of `h`. -/
lemma eventually_pow_smul_eq_zero (h : Γ(X, V)) {D : X.Opens} (hD : X.basicOpen h = D)
    (hDV : D ≤ V) (t : Γ(M, V)) (ht : Cech.res hDV t = 0) :
    ∀ᶠ m in atTop, h ^ m • t = 0 := by
  subst hD
  obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_aux hV M h t ht
  refine eventually_atTop.2 ⟨n, fun m hm => ?_⟩
  rw [← Nat.sub_add_cancel hm, pow_add, mul_smul, hn, smul_zero]

end Affine

section Cover

variable {W : X.Opens} {ι : Type*} (g : ι → Γ(X, W))

/-- The basic opens `D(g i)` of `X` attached to a family of functions on `W`. -/
abbrev cover (i : ι) : X.Opens := X.basicOpen (g i)

lemma inter_le {n : ℕ} (σ : Fin (n + 1) → ι) : Cech.inter (cover g) σ ≤ W :=
  (Cech.inter_le_apply σ 0).trans (X.basicOpen_le (g (σ 0)))

lemma inter_cons_le (k : ι) {n : ℕ} (σ : Fin n → ι) :
    Cech.inter (cover g) (Fin.cons k σ : Fin (n + 1) → ι) ≤ Cech.inter (cover g) σ :=
  (Cech.inter_cons _ k σ).le.trans inf_le_right

lemma basicOpen_inter (k : ι) {n : ℕ} (σ : Fin (n + 1) → ι) :
    X.basicOpen (rres (inter_le g σ) (g k)) = cover g k ⊓ Cech.inter (cover g) σ :=
  (basicOpen_rres _ _).trans (inf_comm _ _)

lemma basicOpen_inter_cons (k : ι) {n : ℕ} (σ : Fin (n + 1) → ι) :
    X.basicOpen (rres (inter_le g σ) (g k)) =
      Cech.inter (cover g) (Fin.cons k σ : Fin (n + 2) → ι) :=
  (basicOpen_inter g k σ).trans (Cech.inter_cons _ k σ).symm

lemma isAffineOpen_inter (hW : IsAffineOpen W) {n : ℕ} (σ : Fin (n + 1) → ι) :
    IsAffineOpen (Cech.inter (cover g) σ) := by
  induction n with
  | zero =>
    have h : Cech.inter (cover g) σ = X.basicOpen (g (σ 0)) :=
      le_antisymm (Cech.inter_le_apply σ 0)
        (le_iInf fun a => by rw [show a = 0 from Fin.fin_one_eq_zero a])
    rw [h]
    exact hW.basicOpen _
  | succ n ih =>
    have h := (ih (Fin.tail σ)).basicOpen (rres (inter_le g (Fin.tail σ)) (g (σ 0)))
    rw [basicOpen_inter_cons, Fin.cons_self_tail] at h
    exact h

variable (M : X.Modules)

/-- Multiplication of Čech cochains for the cover `D(g i)` by a function on `W`. -/
noncomputable def csmul {p : ℕ} (r : Γ(X, W)) (c : Cech.C M.presheaf (cover g) p) :
    Cech.C M.presheaf (cover g) p :=
  fun σ => rres (inter_le g σ) r • c σ

lemma d_csmul {p : ℕ} (r : Γ(X, W)) (c : Cech.C M.presheaf (cover g) p) :
    Cech.d M.presheaf (cover g) p (csmul g M r c) =
      csmul g M r (Cech.d M.presheaf (cover g) p c) := by
  funext τ
  simp only [Cech.d_apply, csmul, res_smul, rres_rres, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact smul_comm _ _ _

variable [M.IsQuasicoherent]

/-- The ordered Čech complex of a quasi-coherent module for the cover of an affine open `W` by
the basic opens `D(g i)`, where the `g i` generate the unit ideal, is exact in every positive
degree. -/
theorem exactAt_cover (hW : IsAffineOpen W) [Finite ι] (hg : Ideal.span (Set.range g) = ⊤)
    (p : ℕ) : Cech.ExactAt M.presheaf (cover g) p := by
  classical
  cases nonempty_fintype ι
  intro z hz
  have h₁ : ∀ᶠ m in atTop, ∀ (k : ι) (σ : Fin (p + 1) → ι),
      ∃ t : Γ(M, Cech.inter (cover g) σ), Cech.res (inter_cons_le g k σ) t =
        rres (inter_cons_le g k σ) (rres (inter_le g σ) (g k)) ^ m • z (Fin.cons k σ) :=
    eventually_all.2 fun k => eventually_all.2 fun σ =>
      eventually_exists_res_eq_pow_smul (isAffineOpen_inter g hW σ) M _
        (basicOpen_inter_cons g k σ) (inter_cons_le g k σ) (z (Fin.cons k σ))
  obtain ⟨N, hN⟩ := h₁.exists
  choose t ht using hN
  simp only [rres_rres, ← map_pow] at ht
  let e : ι → Cech.C M.presheaf (cover g) (p + 1) := fun k τ =>
    Cech.d M.presheaf (cover g) p (t k) τ - rres (inter_le g τ) (g k ^ N) • z τ
  have hvan : ∀ (k : ι) (τ : Fin (p + 2) → ι),
      Cech.res (inf_le_right : cover g k ⊓ Cech.inter (cover g) τ ≤ _) (e k τ) = 0 := by
    intro k τ
    have hO : cover g k ⊓ Cech.inter (cover g) τ ≤ cover g k ⊓ Cech.inter (cover g) τ := le_rfl
    simp only [e, map_sub, res_smul, rres_rres, Cech.d_apply, map_sum, map_zsmul, Cech.res_res]
    rw [sub_eq_zero, Cech.res_eq_sum_of_d_eq_zero hz k τ hO, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Cech.res_res (Cech.le_inter_cons_comp k τ j hO) (inter_cons_le g k (τ ∘ j.succAbove)),
      ht, res_smul, rres_rres]
    exact smul_comm _ _ _
  have h₂ : ∀ᶠ m in atTop, ∀ (k : ι) (τ : Fin (p + 2) → ι),
      rres (inter_le g τ) (g k) ^ m • e k τ = 0 :=
    eventually_all.2 fun k => eventually_all.2 fun τ =>
      eventually_pow_smul_eq_zero (isAffineOpen_inter g hW τ) M _ (basicOpen_inter g k τ)
        inf_le_right (e k τ) (hvan k τ)
  obtain ⟨N', hN'⟩ := h₂.exists
  have hspan : Ideal.span (Set.range fun k => g k ^ (N + N')) = ⊤ := by
    have h := Ideal.span_pow_eq_top _ hg (N + N')
    rwa [← Set.range_comp] at h
  have h1 : (1 : Γ(X, W)) ∈ Ideal.span (Set.range fun k => g k ^ (N + N')) :=
    hspan.symm ▸ Submodule.mem_top
  obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.1 h1
  refine ⟨∑ k, csmul g M (a k * g k ^ N') (t k), ?_⟩
  rw [map_sum]
  simp only [d_csmul]
  funext τ
  have hterm : ∀ k, rres (inter_le g τ) (a k * g k ^ N') • Cech.d M.presheaf (cover g) p (t k) τ =
      rres (inter_le g τ) (a k * g k ^ (N + N')) • z τ := by
    intro k
    have hd : Cech.d M.presheaf (cover g) p (t k) τ =
        e k τ + rres (inter_le g τ) (g k ^ N) • z τ := (sub_add_cancel _ _).symm
    rw [hd, map_mul, map_mul, map_pow, map_pow, map_pow, smul_add, mul_smul, hN' k τ, smul_zero,
      zero_add, smul_smul, mul_assoc, ← pow_add, add_comm N' N]
  rw [Finset.sum_apply]
  simp only [csmul]
  rw [Finset.sum_congr rfl fun k _ => hterm k, ← Finset.sum_smul, ← map_sum, ha, map_one, one_smul]

end Cover

end Langlands.AlgebraicGeometry.Modules.AffineVanishing
