import Langlands.AlgebraicGeometry.CechSlant

/-!
# Left-axis cup and shuffle slant

For a fibre product `P` of `X` and `Y` over `Spec R`, finite affine covers `U` of `X` and `V`
of `Y`, and an arbitrary functional `l` on one-cochains of `U`, this file computes the shuffle
slant `L` of a cup `p₁^* x ∪ e` with a first-factor one-cocycle `x`
(`L_cup_pull_left`). It also records the anticommutation of `L` with the Čech differentials
for an unnormalized functional (`L_d_col`) and identifies the column slant by evaluation at a
rational point with the pullback along the corresponding axis (`colSlant_evalCol`).
Together these give `L_cup_pull_left_eq`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe w w' u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open scoped TensorProduct

namespace Langlands.Cohomology.Cech.KunnethDetection

open Langlands.AlgebraicGeometry.Picard.FieldTwoAxisH1Injectivity
open Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof

section FamilySlant

variable {R : CommRingCat.{u}} {X Y P : Scheme.{u}} {πX : X ⟶ Spec R} {πY : Y ⟶ Spec R}
  {p₁ : P ⟶ X} {p₂ : P ⟶ Y} (hP : IsPullback p₁ p₂ πX πY)
  [∀ W : X.Opens, Algebra R Γ(X, W)]
  (halgX : ∀ W : X.Opens, algebraMap R Γ(X, W) = (secHom πX W).hom)
  [∀ W : Y.Opens, Algebra R Γ(Y, W)]
  (halgY : ∀ W : Y.Opens, algebraMap R Γ(Y, W) = (secHom πY W).hom)
  {μ : Type w} [Finite μ] (O : μ → X.Opens) (hO : ∀ a, IsAffineOpen (O a))

/-- The bijection `(∏ₐ Γ(X, O a)) ⊗[R] (∏_{Unit} Γ(Y, W)) ≃ ∏ₐ Γ(P, p₁⁻¹ O a ⊓ p₂⁻¹ W)` for
a finite family `O` of affine opens and an affine open `W`. -/
noncomputable def tensorEquivFam (W : Y.Opens) (hW : IsAffineOpen W) :
    (∀ a, Γ(X, O a)) ⊗[R] (∀ _ : Unit, Γ(Y, W)) ≃+
      ∀ (a : μ) (_ : Unit), Γ(P, prodOpen p₁ p₂ (O a) W) :=
  AddEquiv.ofBijective (tensorFam halgX halgY hP O (fun _ : Unit => W))
    (tensorFam_bijective halgX halgY hP _ _ hO fun _ => hW)

/-- The slant product with an arbitrary functional `f` on a finite family of affine sections:
it sends `p₁^* x * p₂^* y` to `f x • y`. -/
noncomputable def slantFam (f : (∀ a, Γ(X, O a)) →ₗ[R] R) (W : Y.Opens)
    (hW : IsAffineOpen W) : (∀ a, Γ(P, prodOpen p₁ p₂ (O a) W)) →+ Γ(Y, W) where
  toFun F := TensorProduct.lid R Γ(Y, W) (TensorProduct.map f (LinearMap.proj ())
    ((tensorEquivFam hP halgX halgY O hO W hW).symm fun a _ => F a))
  map_zero' := by
    rw [show (fun (a : μ) (_ : Unit) =>
      (0 : ∀ a, Γ(P, prodOpen p₁ p₂ (O a) W)) a) = 0 from rfl,
      map_zero, map_zero, map_zero]
  map_add' F G := by
    rw [show (fun a (_ : Unit) => (F + G) a) = (fun a _ => F a) + (fun a _ => G a) from rfl,
      map_add, map_add, map_add]

lemma slantFam_tensorFam (f : (∀ a, Γ(X, O a)) →ₗ[R] R) (W : Y.Opens) (hW : IsAffineOpen W)
    (t : (∀ a, Γ(X, O a)) ⊗[R] (∀ _ : Unit, Γ(Y, W))) :
    slantFam hP halgX halgY O hO f W hW (fun a => tensorFam halgX halgY hP O
        (fun _ : Unit => W) t a ()) =
      TensorProduct.lid R Γ(Y, W) (TensorProduct.map f (LinearMap.proj ()) t) := by
  change TensorProduct.lid R Γ(Y, W) (TensorProduct.map f (LinearMap.proj ())
    ((tensorEquivFam hP halgX halgY O hO W hW).symm
      (tensorEquivFam hP halgX halgY O hO W hW t))) = _
  rw [AddEquiv.symm_apply_apply]

include hO in
lemma exists_tensorFam_eq (W : Y.Opens) (hW : IsAffineOpen W)
    (F : ∀ a, Γ(P, prodOpen p₁ p₂ (O a) W)) :
    ∃ t : (∀ a, Γ(X, O a)) ⊗[R] (∀ _ : Unit, Γ(Y, W)),
      F = fun a => tensorFam halgX halgY hP O (fun _ : Unit => W) t a () := by
  obtain ⟨t, ht⟩ := (tensorEquivFam hP halgX halgY O hO W hW).surjective fun a _ => F a
  exact ⟨t, funext fun a => (congrFun (congrFun ht a) ()).symm⟩

lemma slantFam_mul (f : (∀ a, Γ(X, O a)) →ₗ[R] R) (W : Y.Opens) (hW : IsAffineOpen W)
    (x : ∀ a, Γ(X, O a)) (y : Γ(Y, W)) :
    slantFam hP halgX halgY O hO f W hW (fun a =>
      (p₁.appLE (O a) (prodOpen p₁ p₂ (O a) W) inf_le_left).hom (x a) *
        (p₂.appLE W (prodOpen p₁ p₂ (O a) W) inf_le_right).hom y) = f x • y := by
  have h := slantFam_tensorFam hP halgX halgY O hO f W hW (x ⊗ₜ fun _ => y)
  simp only [tensorFam_tmul, TensorProduct.map_tmul, TensorProduct.lid_tmul,
    LinearMap.proj_apply] at h
  exact h

lemma slantFam_add_left (f g : (∀ a, Γ(X, O a)) →ₗ[R] R) (W : Y.Opens) (hW : IsAffineOpen W)
    (F : ∀ a, Γ(P, prodOpen p₁ p₂ (O a) W)) :
    slantFam hP halgX halgY O hO (f + g) W hW F =
      slantFam hP halgX halgY O hO f W hW F + slantFam hP halgX halgY O hO g W hW F := by
  obtain ⟨t, rfl⟩ := exists_tensorFam_eq hP halgX halgY O hO W hW F
  rw [slantFam_tensorFam, slantFam_tensorFam, slantFam_tensorFam, TensorProduct.map_add_left,
    LinearMap.add_apply, map_add]

lemma slantFam_smul_left (r : R) (f : (∀ a, Γ(X, O a)) →ₗ[R] R) (W : Y.Opens)
    (hW : IsAffineOpen W) (F : ∀ a, Γ(P, prodOpen p₁ p₂ (O a) W)) :
    slantFam hP halgX halgY O hO (r • f) W hW F = r • slantFam hP halgX halgY O hO f W hW F := by
  obtain ⟨t, rfl⟩ := exists_tensorFam_eq hP halgX halgY O hO W hW F
  rw [slantFam_tensorFam, slantFam_tensorFam, TensorProduct.map_smul_left,
    LinearMap.smul_apply, map_smul]

/-- Naturality of the family slant: an additive map `Φ` of section families that acts on
decomposable sections through a linear map `φ` of the first factor turns slant by `f` into
slant by `f ∘ φ`. -/
lemma slantFam_map {μ' : Type w'} [Finite μ'] (O' : μ' → X.Opens)
    (hO' : ∀ a, IsAffineOpen (O' a)) (W : Y.Opens) (hW : IsAffineOpen W)
    (φ : (∀ a, Γ(X, O a)) →ₗ[R] ∀ a', Γ(X, O' a'))
    (Φ : (∀ a, Γ(P, prodOpen p₁ p₂ (O a) W)) →+ ∀ a', Γ(P, prodOpen p₁ p₂ (O' a') W))
    (hΦ : ∀ (x : ∀ a, Γ(X, O a)) (y : ∀ _ : Unit, Γ(Y, W)),
      Φ (fun a => tensorFam halgX halgY hP O (fun _ : Unit => W) (x ⊗ₜ y) a ()) =
        fun a' => tensorFam halgX halgY hP O' (fun _ : Unit => W) (φ x ⊗ₜ y) a' ())
    (f : (∀ a', Γ(X, O' a')) →ₗ[R] R) (F : ∀ a, Γ(P, prodOpen p₁ p₂ (O a) W)) :
    slantFam hP halgX halgY O' hO' f W hW (Φ F) =
      slantFam hP halgX halgY O hO (f ∘ₗ φ) W hW F := by
  obtain ⟨t, rfl⟩ := exists_tensorFam_eq hP halgX halgY O hO W hW F
  have key : Φ (fun a => tensorFam halgX halgY hP O (fun _ : Unit => W) t a ()) =
      fun a' => tensorFam halgX halgY hP O' (fun _ : Unit => W) (φ.rTensor _ t) a' () := by
    induction t with
    | tmul x y => rw [hΦ, LinearMap.rTensor_tmul]
    | add x y hx hy =>
      rw [show (fun a => tensorFam halgX halgY hP O (fun _ : Unit => W) (x + y) a ()) =
          (fun a => tensorFam halgX halgY hP O (fun _ : Unit => W) x a ()) +
            (fun a => tensorFam halgX halgY hP O (fun _ : Unit => W) y a ()) by
          funext a
          rw [map_add]
          rfl,
        map_add, hx, hy, map_add]
      funext a'
      rw [map_add]
      rfl
  rw [key, slantFam_tensorFam, slantFam_tensorFam, ← LinearMap.comp_apply (TensorProduct.map _ _),
    LinearMap.map_comp_rTensor]

end FamilySlant

section Column

variable {R : CommRingCat.{u}} {X Y P : Scheme.{u}} {πX : X ⟶ Spec R} {πY : Y ⟶ Spec R}
  {p₁ : P ⟶ X} {p₂ : P ⟶ Y} (hP : IsPullback p₁ p₂ πX πY)
  [∀ W : X.Opens, Algebra R Γ(X, W)]
  (halgX : ∀ W : X.Opens, algebraMap R Γ(X, W) = (secHom πX W).hom)
  [∀ W : Y.Opens, Algebra R Γ(Y, W)]
  (halgY : ∀ W : Y.Opens, algebraMap R Γ(Y, W) = (secHom πY W).hom)
  {ι : Type w} [Finite ι] {κ : Type w'} (U : ι → X.Opens) (V : κ → Y.Opens)
  (hU : ∀ σ : Fin 2 → ι, IsAffineOpen (inter U σ))
  (hV : ∀ (m : ℕ) (τ : Fin (m + 1) → κ), IsAffineOpen (inter V τ))
  (l : (∀ σ : Fin 2 → ι, Γ(X, inter U σ)) →ₗ[R] R)

lemma slant_eq_slantFam (W : Y.Opens) (hW : IsAffineOpen W) :
    slant hP halgX halgY U hU l W hW =
      slantFam hP halgX halgY (fun σ : Fin 2 → ι => inter U σ) hU l W hW :=
  rfl

/-- The `R`-linear Čech differential from zero-cochains to one-cochains. -/
noncomputable def dZeroLin :
    (∀ τ : Fin 1 → ι, Γ(X, inter U τ)) →ₗ[R] ∀ σ : Fin 2 → ι, Γ(X, inter U σ) :=
  resPi πX halgX (fun τ : Fin 1 → ι => inter U τ) (fun σ : Fin 2 → ι => inter U σ)
      (fun σ => σ ∘ (0 : Fin 2).succAbove) (fun σ => inter_le_comp σ _) -
    resPi πX halgX (fun τ : Fin 1 → ι => inter U τ) (fun σ : Fin 2 → ι => inter U σ)
      (fun σ => σ ∘ (1 : Fin 2).succAbove) (fun σ => inter_le_comp σ _)

omit [Finite ι] in
lemma dZeroLin_apply (x : C (ab X.presheaf) U 0) :
    dZeroLin halgX U x = d (ab X.presheaf) U 0 x := by
  funext σ
  change resPi πX halgX (fun τ : Fin 1 → ι => inter U τ) (fun σ : Fin 2 → ι => inter U σ)
      (fun σ => σ ∘ (0 : Fin 2).succAbove) (fun σ => inter_le_comp σ _) x σ -
    resPi πX halgX (fun τ : Fin 1 → ι => inter U τ) (fun σ : Fin 2 → ι => inter U σ)
      (fun σ => σ ∘ (1 : Fin 2).succAbove) (fun σ => inter_le_comp σ _) x σ = _
  rw [d_apply, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul,
    ← sub_eq_add_neg]
  rfl

/-- The column of a cochain on the product cover at `b`: its values at the tuples
`(i, b 0), …, (i, b m)`, restricted to `p₁⁻¹ U i ⊓ p₂⁻¹ V_b`. -/
def colSec {m : ℕ} (c : C (ab P.presheaf) (prodCover p₁ p₂ U V) m) (b : Fin (m + 1) → κ) :
    ∀ τ : Fin 1 → ι, Γ(P, prodOpen p₁ p₂ (inter U τ) (inter V b)) := fun τ =>
  res (P := ab P.presheaf) (le_inter_prodCover U V τ b (fun _ => 0) id) (c fun j => (τ 0, b j))

/-- The slant of the columns of a cochain by a functional on zero-cochains. -/
def colSlant (f : (∀ τ : Fin 1 → ι, Γ(X, inter U τ)) →ₗ[R] R) {m : ℕ}
    (c : C (ab P.presheaf) (prodCover p₁ p₂ U V) m) : C (ab Y.presheaf) V m := fun b =>
  slantFam hP halgX halgY (fun τ : Fin 1 → ι => inter U τ) (isAffineOpen_inter_one U hU) f
    (inter V b) (hV m b) (colSec U V c b)

/-- The slant of the Čech differential of a family over `Fin 1 → ι` is the slant of the
family by `l ∘ d`. -/
lemma slant_dZero (W : Y.Opens) (hW : IsAffineOpen W)
    (G : ∀ τ : Fin 1 → ι, Γ(P, prodOpen p₁ p₂ (inter U τ) W)) :
    slant hP halgX halgY U hU l W hW (fun σ =>
      res (P := ab P.presheaf) (prodOpen_mono (inter_le_comp σ (Fin.succAbove 0)) le_rfl)
          (G (σ ∘ Fin.succAbove 0)) -
        res (P := ab P.presheaf) (prodOpen_mono (inter_le_comp σ (Fin.succAbove 1)) le_rfl)
          (G (σ ∘ Fin.succAbove 1))) =
      slantFam hP halgX halgY (fun τ : Fin 1 → ι => inter U τ) (isAffineOpen_inter_one U hU)
        (l ∘ₗ dZeroLin halgX U) W hW G := by
  let Φ : (∀ τ : Fin 1 → ι, Γ(P, prodOpen p₁ p₂ (inter U τ) W)) →+
      ∀ σ : Fin 2 → ι, Γ(P, prodOpen p₁ p₂ (inter U σ) W) :=
    { toFun := fun G σ =>
        res (P := ab P.presheaf) (prodOpen_mono (inter_le_comp σ (Fin.succAbove 0)) le_rfl)
            (G (σ ∘ Fin.succAbove 0)) -
          res (P := ab P.presheaf) (prodOpen_mono (inter_le_comp σ (Fin.succAbove 1)) le_rfl)
            (G (σ ∘ Fin.succAbove 1))
      map_zero' := by
        funext σ
        simp only [Pi.zero_apply, map_zero, sub_zero]
      map_add' := by
        intro G G'
        funext σ
        simp only [Pi.add_apply, map_add]
        abel }
  rw [slant_eq_slantFam]
  refine slantFam_map hP halgX halgY _ (isAffineOpen_inter_one U hU) _ hU W hW
    (dZeroLin halgX U) Φ ?_ l G
  intro x y
  funext σ
  change _ - _ = tensorFam halgX halgY hP (fun σ : Fin 2 → ι => inter U σ) (fun _ : Unit => W)
    ((resPi πX halgX (fun τ : Fin 1 → ι => inter U τ) (fun σ : Fin 2 → ι => inter U σ)
      (fun σ => σ ∘ (0 : Fin 2).succAbove) (fun σ => inter_le_comp σ _) x -
    resPi πX halgX (fun τ : Fin 1 → ι => inter U τ) (fun σ : Fin 2 → ι => inter U σ)
      (fun σ => σ ∘ (1 : Fin 2).succAbove) (fun σ => inter_le_comp σ _) x) ⊗ₜ y) σ ()
  rw [TensorProduct.sub_tmul, map_sub, Pi.sub_apply, Pi.sub_apply,
    ← LinearMap.rTensor_tmul, ← LinearMap.rTensor_tmul, tensorFam_rTensor_resPi,
    tensorFam_rTensor_resPi]
  rfl

/-- **Shuffle slant and the Čech differential, without normalization of the functional.**
For an arbitrary functional `l`, the anticommutation of `L` with the differentials holds up to
the column slant by `l ∘ d`. -/
lemma L_d_col (n : ℕ) (c : C (ab P.presheaf) (prodCover p₁ p₂ U V) (n + 1)) :
    L hP halgX halgY U V hU hV l (n + 1) (d (ab P.presheaf) _ (n + 1) c) =
      colSlant hP halgX halgY U V hU hV (l ∘ₗ dZeroLin halgX U) c -
        d (ab Y.presheaf) V n (L hP halgX halgY U V hU hV l n c) := by
  funext b
  have lhs : L hP halgX halgY U V hU hV l (n + 1) (d (ab P.presheaf) _ (n + 1) c) b =
      ∑ s ∈ Finset.range (n + 1 + 1), ∑ k ∈ Finset.range (n + 1 + 2), (-1 : ℤ) ^ (s + k) •
        ev hP halgX halgY U V hU hV l c b (step (s + 1) ∘ skip k) (degen s ∘ skip k) := by
    rw [L_apply, Finset.sum_range]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [ev_d, Finset.sum_range, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_smul, ← pow_add, succAbove_eq_skip]
  have rhs : d (ab Y.presheaf) V n (L hP halgX halgY U V hU hV l n c) b =
      ∑ t ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1 + 1), (-1 : ℤ) ^ (t + j) •
        ev hP halgX halgY U V hU hV l c b (step (t + 1)) (skip j ∘ degen t) := by
    rw [d_apply, Finset.sum_comm, Finset.sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [L_apply, map_sum, Finset.sum_range, Finset.smul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [map_zsmul, ev_res, smul_smul, ← pow_add, add_comm (j : ℕ), succAbove_eq_skip]
  have h₁ : ∀ s k, k < s → s ≤ n + 1 →
      ev hP halgX halgY U V hU hV l c b (step (s + 1) ∘ skip k) (degen s ∘ skip k) =
        ev hP halgX halgY U V hU hV l c b (step (s - 1 + 1)) (skip k ∘ degen (s - 1)) := by
    intro s k hk hs
    rw [step_comp_skip_of_le hk.le, degen_comp_skip_of_lt hk hs, Nat.sub_add_cancel (by omega)]
  have h₂ : ∀ s, s ≤ n + 1 →
      ev hP halgX halgY U V hU hV l c b (step (s + 1) ∘ skip s) (degen s ∘ skip s) =
        ev hP halgX halgY U V hU hV l c b (step s) id := by
    intro s _
    rw [step_comp_skip_of_le le_rfl, degen_comp_skip_self]
  have h₃ : ∀ s, s ≤ n + 1 →
      ev hP halgX halgY U V hU hV l c b (step (s + 1) ∘ skip (s + 1)) (degen s ∘ skip (s + 1)) =
        ev hP halgX halgY U V hU hV l c b (step (s + 1)) id := by
    intro s _
    rw [step_comp_skip_succ, degen_comp_skip_succ]
  have h₄ : ∀ s k, s + 1 < k → k ≤ n + 1 + 1 →
      ev hP halgX halgY U V hU hV l c b (step (s + 1) ∘ skip k) (degen s ∘ skip k) =
        ev hP halgX halgY U V hU hV l c b (step (s + 1)) (skip (k - 1) ∘ degen s) := by
    intro s k hk hk'
    rw [step_comp_skip_of_lt hk, degen_comp_skip_of_gt hk hk']
  have e₀ : (step 0 : Fin (n + 2) → Fin 2) = fun _ => 1 := by
    funext j
    apply Fin.ext
    rw [val_step]
    simp
  have e₁ : (step (n + 1 + 1) : Fin (n + 2) → Fin 2) = fun _ => 0 := by
    funext j
    apply Fin.ext
    rw [val_step]
    simp [j.isLt]
  have hQ : ev hP halgX halgY U V hU hV l c b (step 0) id -
      ev hP halgX halgY U V hU hV l c b (step (n + 1 + 1)) id =
        colSlant hP halgX halgY U V hU hV (l ∘ₗ dZeroLin halgX U) c b := by
    rw [e₀, e₁, ev, ev, ← map_sub]
    refine Eq.trans ?_ (slant_dZero hP halgX halgY U hU l (inter V b) (hV (n + 1) b)
      (colSec U V c b))
    congr 1
    funext σ
    rw [Pi.sub_apply, colSec, colSec, res_res, res_res]
    rfl
  rw [Pi.sub_apply, lhs, rhs, shuffle_sum
    (fun s k => ev hP halgX halgY U V hU hV l c b (step (s + 1) ∘ skip k) (degen s ∘ skip k))
    (fun t j => ev hP halgX halgY U V hU hV l c b (step (t + 1)) (skip j ∘ degen t))
    (fun s => ev hP halgX halgY U V hU hV l c b (step s) id) (n + 1) h₁ h₂ h₃ h₄, hQ]

end Column

section LeftCup

variable {R : CommRingCat.{u}} {X Y P : Scheme.{u}} {πX : X ⟶ Spec R} {πY : Y ⟶ Spec R}
  {p₁ : P ⟶ X} {p₂ : P ⟶ Y} (hP : IsPullback p₁ p₂ πX πY)
  [∀ W : X.Opens, Algebra R Γ(X, W)]
  (halgX : ∀ W : X.Opens, algebraMap R Γ(X, W) = (secHom πX W).hom)
  [∀ W : Y.Opens, Algebra R Γ(Y, W)]
  (halgY : ∀ W : Y.Opens, algebraMap R Γ(Y, W) = (secHom πY W).hom)
  {ι : Type w} [Finite ι] {κ : Type w'} (U : ι → X.Opens) (V : κ → Y.Opens)
  (hU : ∀ σ : Fin 2 → ι, IsAffineOpen (inter U σ))
  (hV : ∀ (m : ℕ) (τ : Fin (m + 1) → κ), IsAffineOpen (inter V τ))
  (l : (∀ σ : Fin 2 → ι, Γ(X, inter U σ)) →ₗ[R] R)

lemma edge_zero_fin_one : (edge (0 : Fin 1) : Fin 2 → Fin 2) = id :=
  fin_two_funext rfl rfl

omit [Finite ι] in
/-- Cup with a fixed one-cochain, as an `R`-linear map from zero-cochains to one-cochains. -/
noncomputable def cupZeroLin (x : C (ab X.presheaf) U 1) :
    (∀ τ : Fin 1 → ι, Γ(X, inter U τ)) →ₗ[R] ∀ σ : Fin 2 → ι, Γ(X, inter U σ) where
  toFun f := cup₁ X.presheaf U x f
  map_add' f f' := cup₁_add_right x f f'
  map_smul' r f := by
    funext σ
    change ((face x σ (edge 0) : Γ(X, inter U σ)) * face (r • f) σ Fin.succ : Γ(X, inter U σ)) =
      r • ((face x σ (edge 0) : Γ(X, inter U σ)) * face f σ Fin.succ : Γ(X, inter U σ))
    rw [← mul_smul_comm]
    congr 1
    exact (resAlgHom πX halgX (inter_le_comp σ Fin.succ)).toLinearMap.map_smul r _

omit [Finite ι] in
lemma cupZeroLin_apply (x : C (ab X.presheaf) U 1) (f : C (ab X.presheaf) U 0)
    (σ : Fin 2 → ι) :
    cupZeroLin halgX U x f σ = x σ * face f σ Fin.succ := by
  change face x σ (edge 0) * face f σ Fin.succ = _
  rw [face_congr x σ edge_zero_fin_one, face_id]

omit [Finite ι] in
lemma res_face_pull_fst (z : C (ab X.presheaf) U 1) {m : ℕ} {τ : Fin m → ι × κ}
    {θ : Fin 2 → Fin m} {O : P.Opens} {h : O ≤ inter (prodCover p₁ p₂ U V) τ}
    (f₁ : Fin 2 → ι) (h₁ : Prod.fst ∘ (τ ∘ θ) = f₁) (e₁ : O ≤ p₁ ⁻¹ᵁ inter U f₁) :
    res (P := ab P.presheaf) h
      (face (pull p₁ U (prodCover p₁ p₂ U V) Prod.fst (fun _ => inf_le_left) 1 z) τ θ) =
      (p₁.appLE (inter U f₁) O e₁).hom (z f₁) := by
  subst h₁
  rw [face, res_res, pull_apply, res_appLE]

lemma step_one_comp_edge_zero {m : ℕ} :
    (step 1 : Fin (m + 2) → Fin 2) ∘ edge (0 : Fin (m + 1)) = id := by
  refine fin_two_funext (Fin.ext ?_) (Fin.ext ?_) <;>
    simp only [Function.comp_apply, edge_zero, edge_one, val_step, Fin.val_castSucc,
      Fin.val_succ, Fin.val_zero, id_eq, Fin.val_one] <;>
    split_ifs <;> omega

lemma step_succ_succ_comp_edge_zero {m : ℕ} (s : ℕ) :
    (step (s + 2) : Fin (m + 2) → Fin 2) ∘ edge (0 : Fin (m + 1)) = fun _ => 0 := by
  refine fin_two_funext (Fin.ext ?_) (Fin.ext ?_) <;>
    simp only [Function.comp_apply, edge_zero, edge_one, val_step, Fin.val_castSucc,
      Fin.val_succ, Fin.val_zero] <;>
    split_ifs <;> omega

/-- Left multiplication of a column family by a degree-one cochain of the first factor. -/
noncomputable def leftMulCol (x : C (ab X.presheaf) U 1) (W : Y.Opens) :
    (∀ τ : Fin 1 → ι, Γ(P, prodOpen p₁ p₂ (inter U τ) W)) →+
      ∀ σ : Fin 2 → ι, Γ(P, prodOpen p₁ p₂ (inter U σ) W) where
  toFun G σ := (p₁.appLE (inter U σ) (prodOpen p₁ p₂ (inter U σ) W) inf_le_left).hom (x σ) *
    (P.presheaf.map (homOfLE (prodOpen_mono (p₂ := p₂) (inter_le_comp σ Fin.succ)
      (le_refl W))).op).hom (G (σ ∘ Fin.succ))
  map_zero' := by
    funext σ
    simp only [Pi.zero_apply, map_zero, mul_zero]
  map_add' G G' := by
    funext σ
    simp only [Pi.add_apply, map_add, mul_add]

omit [Finite ι] in
lemma leftMulCol_apply (x : C (ab X.presheaf) U 1) (W : Y.Opens)
    (G : ∀ τ : Fin 1 → ι, Γ(P, prodOpen p₁ p₂ (inter U τ) W)) (σ : Fin 2 → ι) :
    leftMulCol U x W G σ =
      HMul.hMul (α := (ab P.presheaf).obj (op (prodOpen p₁ p₂ (inter U σ) W)))
        (β := (ab P.presheaf).obj (op (prodOpen p₁ p₂ (inter U σ) W)))
        ((p₁.appLE (inter U σ) (prodOpen p₁ p₂ (inter U σ) W) inf_le_left).hom (x σ))
        (res (P := ab P.presheaf) (prodOpen_mono (inter_le_comp σ Fin.succ) le_rfl)
          (G (σ ∘ Fin.succ))) :=
  rfl

include hU in
lemma slant_leftMulCol (x : C (ab X.presheaf) U 1) (W : Y.Opens) (hW : IsAffineOpen W)
    (G : ∀ τ : Fin 1 → ι, Γ(P, prodOpen p₁ p₂ (inter U τ) W)) :
    slant hP halgX halgY U hU l W hW (leftMulCol U x W G) =
      slantFam hP halgX halgY (fun τ : Fin 1 → ι => inter U τ) (isAffineOpen_inter_one U hU)
        (l ∘ₗ cupZeroLin halgX U x) W hW G := by
  rw [slant_eq_slantFam]
  refine slantFam_map hP halgX halgY _ (isAffineOpen_inter_one U hU) _ hU W hW
    (cupZeroLin halgX U x) (leftMulCol U x W) ?_ l G
  intro f y
  funext σ
  change (p₁.appLE (inter U σ) (prodOpen p₁ p₂ (inter U σ) W) inf_le_left).hom (x σ) *
      (P.presheaf.map (homOfLE (prodOpen_mono (p₂ := p₂) (inter_le_comp σ Fin.succ)
        (le_refl W))).op).hom
        (tensorFam halgX halgY hP (fun τ : Fin 1 → ι => inter U τ) (fun _ : Unit => W)
          (f ⊗ₜ y) (σ ∘ Fin.succ) ()) = _
  rw [tensorFam_tmul, tensorFam_tmul, map_mul, ← CommRingCat.comp_apply,
    ← CommRingCat.comp_apply, Scheme.Hom.appLE_map, Scheme.Hom.appLE_map, cupZeroLin_apply]
  erw [map_mul]
  rw [face, appLE_res, ← mul_assoc]

include hU in
/-- **Slant of a left-axis cup.** For a one-cocycle `x` of the first factor and an arbitrary
cochain `e` on the product cover, the shuffle slant of `p₁^* x ∪ e` is the column slant of `e`
by the functional `f ↦ l (x ∪ f)` on zero-cochains. -/
lemma L_cup_pull_left {m : ℕ} (x : C (ab X.presheaf) U 1) (hx : d (ab X.presheaf) U 1 x = 0)
    (e : C (ab P.presheaf) (prodCover p₁ p₂ U V) m) :
    L hP halgX halgY U V hU hV l m
        (cup₁ P.presheaf (prodCover p₁ p₂ U V)
          (pull p₁ U (prodCover p₁ p₂ U V) Prod.fst (fun _ => inf_le_left) 1 x) e) =
      colSlant hP halgX halgY U V hU hV (l ∘ₗ cupZeroLin halgX U x) e := by
  funext b
  rw [L_apply, Fin.sum_univ_succ]
  have hs : ∀ s : Fin m, ev hP halgX halgY U V hU hV l
      (cup₁ P.presheaf (prodCover p₁ p₂ U V)
        (pull p₁ U (prodCover p₁ p₂ U V) Prod.fst (fun _ => inf_le_left) 1 x) e)
      b (step ((s.succ : ℕ) + 1)) (degen (s.succ : ℕ)) = 0 := by
    intro s
    unfold ev
    refine Eq.trans (congrArg _ (funext fun σ => ?_)) (map_zero _)
    rw [cup₁_apply, res_mul, res_face_pull_fst U V x (fun _ => σ 0) ?_
      (inf_le_left.trans (p₁.preimage_mono (inter_le_comp σ fun _ => 0))),
      appLE_cocycle_const hx (σ 0) rfl, zero_mul]
    · rfl
    · funext a
      exact congrArg σ (congrFun (step_succ_succ_comp_edge_zero (m := m) (s : ℕ)) a)
  simp only [hs, smul_zero, Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero, one_smul]
  unfold ev colSlant
  rw [← slant_leftMulCol hP halgX halgY U hU l x (inter V b) (hV m b)]
  congr 1
  funext σ
  rw [cup₁_apply, res_mul, res_face_pull_fst U V x σ ?_ inf_le_left, face, res_res,
    leftMulCol_apply, colSec, res_res]
  · congr 1
  · funext a
    exact congrArg σ (congrFun (step_one_comp_edge_zero (m := m)) a)

end LeftCup

section Axis

variable {R : CommRingCat.{u}} {X Y P : Scheme.{u}} {πX : X ⟶ Spec R} {πY : Y ⟶ Spec R}
  {p₁ : P ⟶ X} {p₂ : P ⟶ Y} (hP : IsPullback p₁ p₂ πX πY)
  [∀ W : X.Opens, Algebra R Γ(X, W)]
  (halgX : ∀ W : X.Opens, algebraMap R Γ(X, W) = (secHom πX W).hom)
  [∀ W : Y.Opens, Algebra R Γ(Y, W)]
  (halgY : ∀ W : Y.Opens, algebraMap R Γ(Y, W) = (secHom πY W).hom)
  {ι : Type w} [Finite ι] {κ : Type w'} (U : ι → X.Opens) (V : κ → Y.Opens)
  (hU : ∀ σ : Fin 2 → ι, IsAffineOpen (inter U σ))
  (hV : ∀ (m : ℕ) (τ : Fin (m + 1) → κ), IsAffineOpen (inter V τ))
  (l : (∀ σ : Fin 2 → ι, Γ(X, inter U σ)) →ₗ[R] R)
  (x₀ : Spec R ⟶ X) (hx₀ : x₀ ≫ πX = 𝟙 _) (i₂ : Y ⟶ P)
  (h₁ : i₂ ≫ p₁ = πY ≫ x₀) (h₂ : i₂ ≫ p₂ = 𝟙 Y) (i₀ : ι) (hi₀ : ⊤ ≤ x₀ ⁻¹ᵁ U i₀)

omit [Finite ι] [∀ W : X.Opens, Algebra R Γ(X, W)] in
include hi₀ in
lemma top_le_preimage_inter_const : ⊤ ≤ x₀ ⁻¹ᵁ inter U (fun _ : Fin 1 => i₀) :=
  hi₀.trans (x₀.preimage_mono (le_iInf fun _ => le_rfl))

/-- Evaluation of the `i₀`-component of a zero-cochain at the rational point `x₀`. -/
noncomputable def evalCol : (∀ τ : Fin 1 → ι, Γ(X, inter U τ)) →ₗ[R] R :=
  (evalSec halgX x₀ hx₀ (inter U (fun _ : Fin 1 => i₀))
    (top_le_preimage_inter_const U x₀ i₀ hi₀)).toLinearMap ∘ₗ
      LinearMap.proj (fun _ : Fin 1 => i₀)

omit [Finite ι] [∀ W : X.Opens, Algebra R Γ(X, W)] [∀ W : Y.Opens, Algebra R Γ(Y, W)] in
include h₁ h₂ hi₀ in
lemma axis_le_prodCover (k : κ) : V k ≤ i₂ ⁻¹ᵁ prodCover p₁ p₂ U V (i₀, k) :=
  le_preimage_axis₂ x₀ i₂ h₁ h₂ (U i₀) hi₀ (V k)

include hU in
/-- **Column slant by evaluation at a rational point is the pullback along the axis**
`i₂ = (x₀ ∘ πY, id) : Y ⟶ P`, computed with the index map `k ↦ (i₀, k)`. -/
lemma colSlant_evalCol {m : ℕ} (e : C (ab P.presheaf) (prodCover p₁ p₂ U V) m) :
    colSlant hP halgX halgY U V hU hV (evalCol halgX U x₀ hx₀ i₀ hi₀) e =
      pull i₂ (prodCover p₁ p₂ U V) V (fun k => (i₀, k))
        (axis_le_prodCover U V x₀ i₂ h₁ h₂ i₀ hi₀) m e := by
  funext b
  obtain ⟨t, ht⟩ := exists_tensorFam_eq hP halgX halgY (fun τ : Fin 1 → ι => inter U τ)
    (isAffineOpen_inter_one U hU) (inter V b) (hV m b) (colSec U V e b)
  have hcol : colSec U V e b (fun _ : Fin 1 => i₀) = tensorFam halgX halgY hP
      (fun τ : Fin 1 → ι => inter U τ) (fun _ : Unit => inter V b) t
        (fun _ : Fin 1 => i₀) () :=
    congrFun ht _
  have hax := appLE_axis₂_tensorFam halgX halgY hP
    (fun τ : Fin 1 → ι => inter U τ) (fun _ : Unit => inter V b) x₀ hx₀ i₂ h₁ h₂
    (fun _ : Fin 1 => i₀) (top_le_preimage_inter_const U x₀ i₀ hi₀) t ()
  rw [← hcol, colSec, appLE_res] at hax
  unfold colSlant
  rw [ht, slantFam_tensorFam, pull_apply]
  refine Eq.trans ?_ hax.symm
  clear hax hcol ht
  induction t with
  | tmul x y =>
    simp only [TensorProduct.map_tmul, LinearMap.rTensor_tmul, TensorProduct.lid_tmul,
      LinearMap.proj_apply, Pi.smul_apply]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy, Pi.add_apply]

end Axis

section Combined

variable {R : CommRingCat.{u}} {X Y P : Scheme.{u}} {πX : X ⟶ Spec R} {πY : Y ⟶ Spec R}
  {p₁ : P ⟶ X} {p₂ : P ⟶ Y} (hP : IsPullback p₁ p₂ πX πY)
  [∀ W : X.Opens, Algebra R Γ(X, W)]
  (halgX : ∀ W : X.Opens, algebraMap R Γ(X, W) = (secHom πX W).hom)
  [∀ W : Y.Opens, Algebra R Γ(Y, W)]
  (halgY : ∀ W : Y.Opens, algebraMap R Γ(Y, W) = (secHom πY W).hom)
  {ι : Type w} [Finite ι] {κ : Type w'} (U : ι → X.Opens) (V : κ → Y.Opens)
  (hU : ∀ σ : Fin 2 → ι, IsAffineOpen (inter U σ))
  (hV : ∀ (m : ℕ) (τ : Fin (m + 1) → κ), IsAffineOpen (inter V τ))
  (l : (∀ σ : Fin 2 → ι, Γ(X, inter U σ)) →ₗ[R] R)
  (x₀ : Spec R ⟶ X) (hx₀ : x₀ ≫ πX = 𝟙 _) (i₂ : Y ⟶ P)
  (h₁ : i₂ ≫ p₁ = πY ≫ x₀) (h₂ : i₂ ≫ p₂ = 𝟙 Y) (i₀ : ι) (hi₀ : ⊤ ≤ x₀ ⁻¹ᵁ U i₀)

lemma L_zero_cochain (m : ℕ) :
    L hP halgX halgY U V hU hV l m 0 = 0 := by
  funext b
  rw [L_apply]
  refine Finset.sum_eq_zero fun s _ => ?_
  unfold ev
  rw [show (fun σ : Fin 2 → ι => res (P := ab P.presheaf)
      (le_inter_prodCover U V σ b (step ((s : ℕ) + 1)) (degen (s : ℕ)))
      ((0 : C (ab P.presheaf) (prodCover p₁ p₂ U V) (m + 1))
        fun j => (σ (step ((s : ℕ) + 1) j), b (degen (s : ℕ) j)))) = 0 by
    funext σ
    exact map_zero _]
  rw [map_zero, smul_zero]

include hU in
/-- **The left-axis slant formula on cochains.** Let `x` be a one-cocycle of the first factor
and `e` a cocycle on the product cover. If `l (x ∪ f) = l x · f(x₀) + ν (d f)` for all
zero-cochains `f`, then the shuffle slant of `p₁^* x ∪ e` is `l x` times the pullback of `e`
along the axis `i₂`, plus the coboundary of the slant of `e` by `ν`. -/
theorem L_cup_pull_left_eq (n : ℕ) (x : C (ab X.presheaf) U 1)
    (hx : d (ab X.presheaf) U 1 x = 0)
    (e : C (ab P.presheaf) (prodCover p₁ p₂ U V) (n + 1))
    (he : d (ab P.presheaf) _ (n + 1) e = 0)
    (ν : (∀ σ : Fin 2 → ι, Γ(X, inter U σ)) →ₗ[R] R)
    (hν : l ∘ₗ cupZeroLin halgX U x =
      l x • evalCol halgX U x₀ hx₀ i₀ hi₀ + ν ∘ₗ dZeroLin halgX U) :
    L hP halgX halgY U V hU hV l (n + 1)
        (cup₁ P.presheaf (prodCover p₁ p₂ U V)
          (pull p₁ U (prodCover p₁ p₂ U V) Prod.fst (fun _ => inf_le_left) 1 x) e) =
      fun b => HAdd.hAdd (α := Γ(Y, inter V b)) (β := Γ(Y, inter V b))
        (HSMul.hSMul (α := R) (β := Γ(Y, inter V b)) (l x)
          (pull i₂ (prodCover p₁ p₂ U V) V (fun k => (i₀, k))
            (axis_le_prodCover U V x₀ i₂ h₁ h₂ i₀ hi₀) (n + 1) e b))
        (d (ab Y.presheaf) V n (L hP halgX halgY U V hU hV ν n e) b) := by
  rw [L_cup_pull_left hP halgX halgY U V hU hV l x hx e, hν]
  have hd := L_d_col hP halgX halgY U V hU hV ν n e
  rw [he, L_zero_cochain, eq_comm, sub_eq_zero] at hd
  have hev := colSlant_evalCol hP halgX halgY U V hU hV x₀ hx₀ i₂ h₁ h₂ i₀ hi₀ e
  funext b
  unfold colSlant at hd hev ⊢
  rw [slantFam_add_left, slantFam_smul_left, congrFun hev b, congrFun hd b]

end Combined

section FieldDual

variable {K : Type u} [Field K]

/-- Over a field, a functional vanishing on the kernel of a linear map factors through it. -/
lemma exists_comp_eq_of_ker_le {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W]
    [Module K W] (dd : V →ₗ[K] W) (g : V →ₗ[K] K) (h : LinearMap.ker dd ≤ LinearMap.ker g) :
    ∃ ν : W →ₗ[K] K, ν ∘ₗ dd = g := by
  obtain ⟨ν, hν⟩ := LinearMap.exists_extend
    (((LinearMap.ker dd).liftQ g h).comp dd.quotKerEquivRange.symm.toLinearMap)
  refine ⟨ν, LinearMap.ext fun v => ?_⟩
  have := congrArg (fun φ => φ ⟨dd v, LinearMap.mem_range_self dd v⟩) hν
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivRange_symm_apply_image] at this
  exact this

end FieldDual

section Constants

variable {R : CommRingCat.{u}} {X : Scheme.{u}} {πX : X ⟶ Spec R}
  [∀ W : X.Opens, Algebra R Γ(X, W)]
  (halgX : ∀ W : X.Opens, algebraMap R Γ(X, W) = (secHom πX W).hom)
  {ι : Type w} (U : ι → X.Opens)

lemma inter_pair_le (τ τ' : Fin 1 → ι) : inter U τ ⊓ inter U τ' ≤ inter U ![τ 0, τ' 0] :=
  le_iInf fun k => by
    fin_cases k
    · exact inf_le_left.trans (inter_le_apply τ 0)
    · exact inf_le_right.trans (inter_le_apply τ' 0)

/-- A zero-cochain of the structure sheaf with vanishing Čech differential is a constant,
provided `U` covers `X` and every global function comes from `R`. -/
lemma exists_eq_smul_one_of_dZeroLin_eq_zero (hcov : ⊤ ≤ iSup U)
    (hglob : Function.Surjective (secHom πX ⊤).hom) (f : ∀ τ : Fin 1 → ι, Γ(X, inter U τ))
    (hf : dZeroLin halgX U f = 0) : ∃ r : R, f = r • 1 := by
  refine exists_eq_smul_one_of_cechD_eq_zero πX halgX (fun τ : Fin 1 → ι => inter U τ) ?_
    hglob f ?_
  · exact hcov.trans (iSup_le fun i => (le_iInf fun _ => le_rfl).trans
      (le_iSup (fun τ : Fin 1 → ι => inter U τ) fun _ => i))
  · funext ττ
    obtain ⟨τ, τ'⟩ := ττ
    have h := congrArg (res (P := ab X.presheaf) (inter_pair_le U τ τ'))
      (congrFun hf ![τ 0, τ' 0])
    rw [Pi.zero_apply, map_zero] at h
    rw [cechD_apply, Pi.zero_apply]
    change res (P := ab X.presheaf) inf_le_right (f τ') -
      res (P := ab X.presheaf) inf_le_left (f τ) = 0
    refine Eq.trans ?_ h
    change _ = res (P := ab X.presheaf) (inter_pair_le U τ τ')
      (res (P := ab X.presheaf) (inter_le_comp ![τ 0, τ' 0] (0 : Fin 2).succAbove)
          (f (![τ 0, τ' 0] ∘ (0 : Fin 2).succAbove)) -
        res (P := ab X.presheaf) (inter_le_comp ![τ 0, τ' 0] (1 : Fin 2).succAbove)
          (f (![τ 0, τ' 0] ∘ (1 : Fin 2).succAbove)))
    rw [map_sub, res_res, res_res]
    congr 1
    · exact res_congr (ab X.presheaf) U (by funext j; fin_cases j; rfl) f _ _
    · exact res_congr (ab X.presheaf) U (by funext j; fin_cases j; rfl) f _ _

lemma cupZeroLin_one (x : C (ab X.presheaf) U 1) :
    cupZeroLin halgX U x 1 = x := by
  funext σ
  rw [cupZeroLin_apply]
  change x σ * res (P := ab X.presheaf) _ 1 = x σ
  rw [res_one, mul_one]

end Constants

section DualCorrection

variable {K : Type u} [Field K] {X : Scheme.{u}} {πX : X ⟶ Spec (CommRingCat.of K)}
  [∀ W : X.Opens, Algebra (CommRingCat.of K) Γ(X, W)]
  (halgX : ∀ W : X.Opens, algebraMap (CommRingCat.of K) Γ(X, W) = (secHom πX W).hom)
  {ι : Type w} (U : ι → X.Opens)
  (x₀ : Spec (CommRingCat.of K) ⟶ X) (hx₀ : x₀ ≫ πX = 𝟙 _) (i₀ : ι) (hi₀ : ⊤ ≤ x₀ ⁻¹ᵁ U i₀)

lemma evalCol_one : evalCol halgX U x₀ hx₀ i₀ hi₀ 1 = 1 := by
  simp only [evalCol, LinearMap.comp_apply, LinearMap.proj_apply, Pi.one_apply,
    AlgHom.toLinearMap_apply, map_one]

include hi₀ in
/-- Over a field whose global functions on `X` are constants, the functional `f ↦ l (x ∪ f)` on
zero-cochains differs from `l x` times evaluation at the rational point by a functional of the
Čech differential. -/
lemma exists_dual_correction (hcov : ⊤ ≤ iSup U)
    (hglob : Function.Surjective (secHom πX ⊤).hom)
    (l : (∀ σ : Fin 2 → ι, Γ(X, inter U σ)) →ₗ[CommRingCat.of K] CommRingCat.of K)
    (x : C (ab X.presheaf) U 1) :
    ∃ ν : (∀ σ : Fin 2 → ι, Γ(X, inter U σ)) →ₗ[CommRingCat.of K] CommRingCat.of K,
      l ∘ₗ cupZeroLin halgX U x =
        l x • evalCol halgX U x₀ hx₀ i₀ hi₀ + ν ∘ₗ dZeroLin halgX U := by
  have hker : LinearMap.ker (dZeroLin halgX U) ≤
      LinearMap.ker (l ∘ₗ cupZeroLin halgX U x - l x • evalCol halgX U x₀ hx₀ i₀ hi₀) := by
    intro f hf
    rw [LinearMap.mem_ker] at hf ⊢
    obtain ⟨r, rfl⟩ := exists_eq_smul_one_of_dZeroLin_eq_zero halgX U hcov hglob f hf
    rw [map_smul, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      cupZeroLin_one, evalCol_one, smul_eq_mul, smul_eq_mul, mul_one, sub_self, mul_zero]
  obtain ⟨ν, hν⟩ := exists_comp_eq_of_ker_le (K := K) (dZeroLin halgX U)
    (l ∘ₗ cupZeroLin halgX U x - l x • evalCol halgX U x₀ hx₀ i₀ hi₀) hker
  exact ⟨ν, by rw [hν, add_sub_cancel]⟩

end DualCorrection

end Langlands.Cohomology.Cech.KunnethDetection
