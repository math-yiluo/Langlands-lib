import Langlands.GroupScheme.SL2CentralExtension.Torus

/-! # The splitting on the open cell, translated and glued over `SL₂` -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SL2CentralExtension

variable {S : Scheme.{u}}

theorem Mat.yhx_add {R : Type*} [CommRing R] (a : R) (t : Rˣ) (b c : R) :
    Mat.yhx a t (b + c) = Mat.yhx a t b * Mat.x c := by
  rw [Mat.yhx, Mat.yhx, Mat.x_add]; simp only [mul_assoc]

theorem Mat.yhx_zero_one {R : Type*} [CommRing R] (c : R) : Mat.yhx 0 1 c = Mat.x c := by
  rw [Mat.yhx, Mat.y_zero, Mat.h_one, one_mul, one_mul]

/-- Fppf-locally a unipotent translate `x(r) m` of each of two matrices lies in the open cell,
for the same `r`. -/
theorem Loc.exists_cell₂ {T : Over S} (m m' : Mat.SL2 Γ(T.left, ⊤)) :
    Loc (fun V (k : V ⟶ T) => ∃ r : Γ(V.left, ⊤),
      Mat.cell (Mat.x r * res k m) ∧ Mat.cell (Mat.x r * res k m')) := by
  let f : Mat.SL2 Γ(T.left, ⊤) → Polynomial Γ(T.left, ⊤) := fun m =>
    Polynomial.C (m 0 0) + Polynomial.C (m 1 0) * Polynomial.X
  have hf : ∀ m, Nondeg (f m) := fun m =>
    Nondeg.of_coeff₂ 0 1 (m 1 1) (-m 0 1) (by
      simp [f]
      linear_combination Mat.col_unimodular m)
  have hev : ∀ (m : Mat.SL2 Γ(T.left, ⊤)) {V : Over S} (k : V ⟶ T) (r : Γ(V.left, ⊤)),
      ((f m).map (ring k)).eval r = (Mat.x r * res k m) 0 0 := by
    intro m V k r
    simp only [f, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      Mat.x_mul_00, Mat.map_apply']
    ring
  refine (Loc.exists_isUnit_eval _ ((hf m).mul (hf m'))).mono ?_
  rintro V k ⟨r, hr⟩
  rw [Polynomial.map_mul, Polynomial.eval_mul, IsUnit.mul_iff, hev, hev] at hr
  exact ⟨r, hr⟩

/-- Fppf-locally a unipotent translate `x(r) m` lies in the open cell. -/
theorem Loc.exists_cell {T : Over S} (m : Mat.SL2 Γ(T.left, ⊤)) :
    Loc (fun V (k : V ⟶ T) => ∃ r : Γ(V.left, ⊤), Mat.cell (Mat.x r * res k m)) :=
  (Loc.exists_cell₂ m m).mono fun _ _ ⟨r, h, _⟩ => ⟨r, h⟩

namespace Ext

variable (X : Ext S) {T : Over S}

/-! ### The lift `y'(a) h'(t) x'(b)` of the open cell -/

/-- The lift `y'(a) h'(t) x'(b)` of the point `y(a) h(t) x(b)` of the open cell. -/
def form (a : Γ(T.left, ⊤)) (t : Γ(T.left, ⊤)ˣ) (b : Γ(T.left, ⊤)) : T ⟶ X.E.X :=
  X.yl a * X.hl t * X.xl b

theorem Q_form (a : Γ(T.left, ⊤)) (t : Γ(T.left, ⊤)ˣ) (b : Γ(T.left, ⊤)) :
    X.Q T (X.form a t b) = Mat.yhx a t b := by
  rw [form, map_mul, map_mul, Q_yl, Q_hl, Q_xl, Mat.yhx]

theorem form_res {V : Over S} (g : V ⟶ T) (a : Γ(T.left, ⊤)) (t : Γ(T.left, ⊤)ˣ)
    (b : Γ(T.left, ⊤)) : g ≫ X.form a t b = X.form (ring g a) (umap g t) (ring g b) := by
  rw [form, form, MonObj.comp_mul, MonObj.comp_mul, yl_res, hl_res, xl_res]

theorem xl_eq_form (c : Γ(T.left, ⊤)) : X.xl c = X.form 0 1 c := by
  rw [form, yl_zero, hl_one, one_mul, one_mul]

theorem form_mul_xl (a : Γ(T.left, ⊤)) (t : Γ(T.left, ⊤)ˣ) (b c : Γ(T.left, ⊤)) :
    X.form a t b * X.xl c = X.form a t (b + c) := by
  rw [form, form, xl_add, mul_assoc]

variable {X}

/-- Products of lifts of points of the open cell are again of this form, when the product of
the matrices stays in the open cell. -/
theorem form_mul_exists (hD : X.DComm) (a₁ : Γ(T.left, ⊤)) (t₁ : Γ(T.left, ⊤)ˣ)
    (b₁ a₂ : Γ(T.left, ⊤)) (t₂ : Γ(T.left, ⊤)ˣ) (b₂ : Γ(T.left, ⊤)) (s : Γ(T.left, ⊤)ˣ)
    (hs : (s : Γ(T.left, ⊤)) = 1 + b₁ * a₂) :
    ∃ (a : Γ(T.left, ⊤)) (t : Γ(T.left, ⊤)ˣ) (b : Γ(T.left, ⊤)),
      X.form a₁ t₁ b₁ * X.form a₂ t₂ b₂ = X.form a t b := by
  refine ⟨a₁ + (↑t₁⁻¹ : Γ(T.left, ⊤)) * ↑t₁⁻¹ * (a₂ * ↑s⁻¹), t₁ * s * t₂,
    (↑t₂⁻¹ : Γ(T.left, ⊤)) * ↑t₂⁻¹ * (b₁ * ↑s⁻¹) + b₂, ?_⟩
  calc X.form a₁ t₁ b₁ * X.form a₂ t₂ b₂
      = X.yl a₁ * X.hl t₁ * (X.xl b₁ * X.yl a₂) * X.hl t₂ * X.xl b₂ := by
        simp only [form, mul_assoc]
    _ = X.yl a₁ * (X.hl t₁ * X.yl (a₂ * (↑s⁻¹ : Γ(T.left, ⊤)))) * X.hl s *
          (X.xl (b₁ * (↑s⁻¹ : Γ(T.left, ⊤))) * X.hl t₂) * X.xl b₂ := by
        rw [xl_yl hD b₁ a₂ s hs]; simp only [mul_assoc]
    _ = X.yl a₁ * (X.yl ((↑t₁⁻¹ : Γ(T.left, ⊤)) * ↑t₁⁻¹ * (a₂ * ↑s⁻¹)) * X.hl t₁) * X.hl s *
          (X.hl t₂ * X.xl ((↑t₂⁻¹ : Γ(T.left, ⊤)) * ↑t₂⁻¹ * (b₁ * ↑s⁻¹))) * X.xl b₂ := by
        rw [X.hl_yl t₁ (a₂ * (↑s⁻¹ : Γ(T.left, ⊤))), X.xl_hl t₂ (b₁ * (↑s⁻¹ : Γ(T.left, ⊤)))]
    _ = _ := by
        rw [form, yl_add, xl_add, hl_mul hD, hl_mul hD]; simp only [mul_assoc]

/-- The lift of a product of points of the open cell lying in the open cell. -/
theorem form_mul_eq (hD : X.DComm) {a₁ b₁ a₂ b₂ a b : Γ(T.left, ⊤)}
    {t₁ t₂ t : Γ(T.left, ⊤)ˣ} (h : Mat.yhx a₁ t₁ b₁ * Mat.yhx a₂ t₂ b₂ = Mat.yhx a t b) :
    X.form a₁ t₁ b₁ * X.form a₂ t₂ b₂ = X.form a t b := by
  have h00 := congrArg (fun g : Mat.SL2 Γ(T.left, ⊤) => g 0 0) h
  simp only [Mat.mul_00, Mat.yhx_00, Mat.yhx_01, Mat.yhx_10] at h00
  have hu1 : (t₁ : Γ(T.left, ⊤)) * ↑t₁⁻¹ = 1 := Units.mul_inv t₁
  have hu2 : (t₂ : Γ(T.left, ⊤)) * ↑t₂⁻¹ = 1 := Units.mul_inv t₂
  obtain ⟨s, hs⟩ : ∃ s : Γ(T.left, ⊤)ˣ, (s : Γ(T.left, ⊤)) = 1 + b₁ * a₂ := by
    refine ⟨t * t₁⁻¹ * t₂⁻¹, ?_⟩
    rw [Units.val_mul, Units.val_mul]
    linear_combination (-((↑t₁⁻¹ : Γ(T.left, ⊤)) * ↑t₂⁻¹)) * h00 +
      ((t₂ : Γ(T.left, ⊤)) * ↑t₂⁻¹ * (1 + b₁ * a₂)) * hu1 + (1 + b₁ * a₂) * hu2
  obtain ⟨a', τ, b', hab⟩ := form_mul_exists hD a₁ t₁ b₁ a₂ t₂ b₂ s hs
  rw [hab]
  have hQ := congrArg (X.Q T) hab
  rw [map_mul, Q_form, Q_form, Q_form, h] at hQ
  obtain ⟨rfl, rfl, rfl⟩ := Mat.yhx_injective hQ
  rfl

/-! ### Representatives `x'(-r) y'(a) h'(t) x'(b)` -/

variable (X)

/-- `e` is the lift `x'(-r) y'(a) h'(t) x'(b)` of `m`, where `x(r) m = y(a) h(t) x(b)`. -/
def CellRep (m : Mat.SL2 Γ(T.left, ⊤)) (e : T ⟶ X.E.X) : Prop :=
  ∃ (r a : Γ(T.left, ⊤)) (t : Γ(T.left, ⊤)ˣ) (b : Γ(T.left, ⊤)),
    Mat.x r * m = Mat.yhx a t b ∧ e = X.xl (-r) * X.form a t b

theorem exists_cellRep {m : Mat.SL2 Γ(T.left, ⊤)} {r : Γ(T.left, ⊤)}
    (hr : Mat.cell (Mat.x r * m)) : ∃ e, X.CellRep m e :=
  ⟨_, r, _, hr.unit, _, Mat.eq_yhx _ hr.unit (IsUnit.unit_spec hr), rfl⟩

theorem cellRep_res {V : Over S} (k : V ⟶ T) {m : Mat.SL2 Γ(T.left, ⊤)} {e : T ⟶ X.E.X}
    (he : X.CellRep m e) : X.CellRep (res k m) (k ≫ e) := by
  obtain ⟨r, a, t, b, hm, rfl⟩ := he
  refine ⟨ring k r, ring k a, umap k t, ring k b, ?_, ?_⟩
  · rw [← Mat.map_x, ← map_mul, hm, Mat.map_yhx]
  · rw [MonObj.comp_mul, xl_res, form_res, map_neg]

theorem Q_of_cellRep {m : Mat.SL2 Γ(T.left, ⊤)} {e : T ⟶ X.E.X} (he : X.CellRep m e) :
    X.Q T e = m := by
  obtain ⟨r, a, t, b, hm, rfl⟩ := he
  rw [map_mul, Q_xl, Q_form, ← hm, Mat.x_neg, inv_mul_cancel_left]

variable {X}

theorem cellRep_unique (hD : X.DComm) {m : Mat.SL2 Γ(T.left, ⊤)} {e e' : T ⟶ X.E.X}
    (he : X.CellRep m e) (he' : X.CellRep m e') : e = e' := by
  obtain ⟨r, a, t, b, h, rfl⟩ := he
  obtain ⟨r', a', t', b', h', rfl⟩ := he'
  have hm : Mat.yhx 0 1 (r' + -r) * Mat.yhx a t b = Mat.yhx a' t' b' := by
    rw [← h, ← h', Mat.yhx_zero_one, Mat.x_add, Mat.x_neg]; group
  have hf := form_mul_eq hD hm
  rw [← xl_eq_form] at hf
  rw [← hf, ← mul_assoc, ← xl_add, show -r' + (r' + -r) = -r by ring]

/-! ### The splitting -/

theorem exists_sigma (hD : X.DComm) (m : Mat.SL2 Γ(T.left, ⊤)) :
    ∃ e : T ⟶ X.E.X, ∀ ⦃V : Over S⦄ (k : V ⟶ T) (e' : V ⟶ X.E.X),
      X.CellRep (res k m) e' → k ≫ e = e' :=
  Loc.glue (fun V k e => X.CellRep (res k m) e)
    (fun V W g k x hx => by rw [res_comp]; exact X.cellRep_res k hx)
    (fun V g x y hx hy => cellRep_unique hD hx hy)
    ((Loc.exists_cell m).mono fun V k ⟨r, hr⟩ => X.exists_cellRep hr)

/-- The splitting on points, before checking that it is a homomorphism. -/
def sigmaFun (hD : X.DComm) (m : Mat.SL2 Γ(T.left, ⊤)) : T ⟶ X.E.X :=
  (exists_sigma hD m).choose

theorem sigmaFun_spec (hD : X.DComm) (m : Mat.SL2 Γ(T.left, ⊤)) ⦃V : Over S⦄ (k : V ⟶ T)
    (e' : V ⟶ X.E.X) (he' : X.CellRep (res k m) e') : k ≫ sigmaFun hD m = e' :=
  (exists_sigma hD m).choose_spec k e' he'

theorem sigmaFun_res (hD : X.DComm) {V : Over S} (k : V ⟶ T) (m : Mat.SL2 Γ(T.left, ⊤)) :
    k ≫ sigmaFun hD m = sigmaFun hD (res k m) := by
  apply Loc.ext
  refine (Loc.exists_cell (res k m)).mono ?_
  rintro W j ⟨r, hr⟩
  obtain ⟨e, he⟩ := X.exists_cellRep hr
  rw [← Category.assoc, sigmaFun_spec hD m (j ≫ k) e (by rwa [res_comp]),
    sigmaFun_spec hD (res k m) j e he]

theorem Q_sigmaFun (hD : X.DComm) (m : Mat.SL2 Γ(T.left, ⊤)) :
    X.Q T (sigmaFun hD m) = m := by
  apply X.sep
  refine (Loc.exists_cell m).mono ?_
  rintro V k ⟨r, hr⟩
  obtain ⟨e, he⟩ := X.exists_cellRep hr
  rw [← X.Q_nat, sigmaFun_spec hD m k e he, X.Q_of_cellRep he]

theorem sigmaFun_mul (hD : X.DComm) (m₁ m₂ : Mat.SL2 Γ(T.left, ⊤)) :
    sigmaFun hD (m₁ * m₂) = sigmaFun hD m₁ * sigmaFun hD m₂ := by
  apply Loc.ext
  refine ((Loc.exists_cell₂ m₁ (m₁ * m₂)).and (Loc.exists_cell m₂)).mono ?_
  rintro V k ⟨⟨r, hr₁, hr₁₂⟩, ⟨p, hp⟩⟩
  have ht₁ := Mat.eq_yhx _ hr₁.unit (IsUnit.unit_spec hr₁)
  have ht₂ := Mat.eq_yhx _ hp.unit (IsUnit.unit_spec hp)
  have ht := Mat.eq_yhx _ hr₁₂.unit (IsUnit.unit_spec hr₁₂)
  set a₁ := (Mat.x r * res k m₁) 1 0 * ↑hr₁.unit⁻¹
  set b₁ := ↑hr₁.unit⁻¹ * (Mat.x r * res k m₁) 0 1
  set a₂ := (Mat.x p * res k m₂) 1 0 * ↑hp.unit⁻¹
  set b₂ := ↑hp.unit⁻¹ * (Mat.x p * res k m₂) 0 1
  set a := (Mat.x r * res k (m₁ * m₂)) 1 0 * ↑hr₁₂.unit⁻¹
  set b := ↑hr₁₂.unit⁻¹ * (Mat.x r * res k (m₁ * m₂)) 0 1
  rw [MonObj.comp_mul, sigmaFun_spec hD (m₁ * m₂) k _ ⟨r, a, hr₁₂.unit, b, ht, rfl⟩,
    sigmaFun_spec hD m₁ k _ ⟨r, a₁, hr₁.unit, b₁, ht₁, rfl⟩,
    sigmaFun_spec hD m₂ k _ ⟨p, a₂, hp.unit, b₂, ht₂, rfl⟩]
  have hm : Mat.yhx a₁ hr₁.unit (b₁ + -p) * Mat.yhx a₂ hp.unit b₂ = Mat.yhx a hr₁₂.unit b := by
    rw [← ht, ← ht₂, Mat.yhx_add, ← ht₁, map_mul, Mat.x_neg]
    group
  rw [mul_assoc, ← mul_assoc (X.form _ _ _), X.form_mul_xl, form_mul_eq hD hm]

/-- The splitting on points: a homomorphism lifting the identity of `SL₂`. -/
def sigma (hD : X.DComm) (T : Over S) : Mat.SL2 Γ(T.left, ⊤) →* (T ⟶ X.E.X) where
  toFun := sigmaFun hD
  map_one' := by
    have h := sigmaFun_mul hD (1 : Mat.SL2 Γ(T.left, ⊤)) 1
    rw [mul_one] at h
    exact (mul_eq_left.mp h.symm)
  map_mul' := sigmaFun_mul hD

theorem sigma_apply (hD : X.DComm) (m : Mat.SL2 Γ(T.left, ⊤)) :
    sigma hD T m = sigmaFun hD m := rfl

theorem sigma_res (hD : X.DComm) {V : Over S} (k : V ⟶ T) (m : Mat.SL2 Γ(T.left, ⊤)) :
    k ≫ sigma hD T m = sigma hD V (res k m) :=
  sigmaFun_res hD k m

theorem Q_sigma (hD : X.DComm) (m : Mat.SL2 Γ(T.left, ⊤)) : X.Q T (sigma hD T m) = m :=
  Q_sigmaFun hD m

end Ext

end Langlands.GroupScheme.SL2CentralExtension
