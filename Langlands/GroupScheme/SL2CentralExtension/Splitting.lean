import Langlands.GroupScheme.SL2CentralExtension.Unipotent

/-! # Canonical lifts of the root groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SL2CentralExtension

variable {S : Scheme.{u}}

/-- Units restrict along morphisms of test schemes. -/
abbrev umap {V T : Over S} (g : V ⟶ T) : Γ(T.left, ⊤)ˣ →* Γ(V.left, ⊤)ˣ :=
  Units.map (ring g).toMonoidHom

theorem umap_coe {V T : Over S} (g : V ⟶ T) (t : Γ(T.left, ⊤)ˣ) :
    ((umap g t : Γ(V.left, ⊤)ˣ) : Γ(V.left, ⊤)) = ring g t :=
  rfl

theorem umap_hd {V T : Over S} (g : V ⟶ T) {t d : Γ(T.left, ⊤)ˣ}
    (hd : (d : Γ(T.left, ⊤)) = t * t - 1) :
    ((umap g d : Γ(V.left, ⊤)ˣ) : Γ(V.left, ⊤)) = umap g t * umap g t - 1 := by
  rw [umap_coe, umap_coe, hd, map_sub, map_mul, map_one]

/-- Fppf-locally there is a unit `t` such that `t² - 1` is a unit. -/
theorem Loc.exists_unit_sq_sub_one (T : Over S) :
    Loc (fun V (_ : V ⟶ T) => ∃ t d : Γ(V.left, ⊤)ˣ, (d : Γ(V.left, ⊤)) = t * t - 1) := by
  let p : Polynomial Γ(T.left, ⊤) := Polynomial.X * (Polynomial.X * Polynomial.X - 1)
  have hp : Nondeg p := Nondeg.monic (by simp only [p]; monicity!)
  refine (Loc.exists_isUnit_eval p hp).mono ?_
  rintro V g ⟨r, hr⟩
  simp only [p, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_one,
    Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one] at hr
  rw [IsUnit.mul_iff] at hr
  exact ⟨hr.1.unit, hr.2.unit, by rw [IsUnit.unit_spec, IsUnit.unit_spec]⟩

namespace Ext

variable (X : Ext S) (b : Bool)

/-! ### Local candidates `[λ_b(t), root_b((t² - 1)⁻¹ u)]` -/

/-- The commutator of local lifts of `λ_b(t)` and `root_b(d⁻¹ u)`. -/
def Xt {T : Over S} (t d : Γ(T.left, ⊤)ˣ) (u : Γ(T.left, ⊤)) : T ⟶ X.E.X :=
  X.comm (Mat.lam b t) (Mat.root b ((↑d⁻¹ : Γ(T.left, ⊤)) * u))

theorem Q_Xt {T : Over S} {t d : Γ(T.left, ⊤)ˣ} (hd : (d : Γ(T.left, ⊤)) = t * t - 1)
    (u : Γ(T.left, ⊤)) : X.Q T (X.Xt b t d u) = Mat.root b u := by
  rw [Xt, Q_comm, Mat.lam_root_commutator, ← hd, ← mul_assoc, Units.mul_inv, one_mul]

theorem Xt_res {V T : Over S} (g : V ⟶ T) (t d : Γ(T.left, ⊤)ˣ) (u : Γ(T.left, ⊤)) :
    g ≫ X.Xt b t d u = X.Xt b (umap g t) (umap g d) (ring g u) := by
  simp only [Xt]
  rw [comm_res, Mat.map_lam, Mat.map_root, map_mul]
  rfl

theorem Xt_add {T : Over S} (t d : Γ(T.left, ⊤)ˣ) (u u' : Γ(T.left, ⊤)) :
    X.Xt b t d (u + u') = X.Xt b t d u * X.Xt b t d u' := by
  apply Loc.ext
  refine (((X.lift (Mat.lam b t)).and (X.lift (Mat.root b ((↑d⁻¹ : Γ(T.left, ⊤)) * u)))).and
    (X.lift (Mat.root b ((↑d⁻¹ : Γ(T.left, ⊤)) * u')))).mono ?_
  rintro V g ⟨⟨⟨f, hf⟩, ⟨e, he⟩⟩, ⟨e', he'⟩⟩
  have hee' : X.Q V (e * e') = res g (Mat.root b ((↑d⁻¹ : Γ(T.left, ⊤)) * (u + u'))) := by
    rw [mul_add, Mat.root_add]; exact X.Q_mul_res g he he'
  rw [MonObj.comp_mul]
  simp only [Xt]
  rw [X.comm_spec _ _ g f _ hf hee', X.comm_spec _ _ g f e hf he, X.comm_spec _ _ g f e' hf he']
  have hc : Commute e (f * e' * f⁻¹ * e'⁻¹) := by
    have h1 : X.Q V e = Mat.root b (ring g ((↑d⁻¹ : Γ(T.left, ⊤)) * u)) := by
      rw [he, Mat.map_root]
    have h2 : X.Q V (f * e' * f⁻¹ * e'⁻¹) =
        Mat.root b (ring g (((t : Γ(T.left, ⊤)) * t - 1) * ((↑d⁻¹ : Γ(T.left, ⊤)) * u'))) := by
      rw [map_mul, X.Q_conj_res g hf he', X.Q_inv_res g he', ← map_mul,
        Mat.lam_root_commutator, Mat.map_root]
    exact X.commute_of_root b h1 h2
  calc f * (e * e') * f⁻¹ * (e * e')⁻¹
      = f * e * f⁻¹ * e⁻¹ * (e * (f * e' * f⁻¹ * e'⁻¹) * e⁻¹) := by group
    _ = f * e * f⁻¹ * e⁻¹ * (f * e' * f⁻¹ * e'⁻¹) := by rw [hc.eq, mul_inv_cancel_right]

/-- Conjugation by a lift of `λ_b(s)` scales the candidate by `s²`. -/
theorem Xt_conj {T : Over S} (t d : Γ(T.left, ⊤)ˣ) (u : Γ(T.left, ⊤)) {e : T ⟶ X.E.X}
    {s : Γ(T.left, ⊤)ˣ} (he : X.Q T e = Mat.lam b s) :
    e * X.Xt b t d u * e⁻¹ = X.Xt b t d ((s : Γ(T.left, ⊤)) * (s : Γ(T.left, ⊤)) * u) := by
  apply Loc.ext
  refine ((X.lift (Mat.lam b t)).and
    (X.lift (Mat.root b ((↑d⁻¹ : Γ(T.left, ⊤)) * u)))).mono ?_
  rintro V g ⟨⟨f, hf⟩, ⟨e₁, h₁⟩⟩
  have hge : X.Q V (g ≫ e) = res g (Mat.lam b s) := by rw [X.Q_nat, he]
  have k₁ : X.Q V ((g ≫ e) * f * (g ≫ e)⁻¹) = res g (Mat.lam b t) := by
    rw [X.Q_conj_res g hge hf, Mat.lam_comm, mul_inv_cancel_right]
  have k₂ : X.Q V ((g ≫ e) * e₁ * (g ≫ e)⁻¹) =
      res g (Mat.root b ((↑d⁻¹ : Γ(T.left, ⊤)) *
        ((s : Γ(T.left, ⊤)) * (s : Γ(T.left, ⊤)) * u))) := by
    rw [X.Q_conj_res g hge h₁, Mat.lam_root_conj,
      show (s : Γ(T.left, ⊤)) * (s : Γ(T.left, ⊤)) * ((↑d⁻¹ : Γ(T.left, ⊤)) * u) =
        (↑d⁻¹ : Γ(T.left, ⊤)) * ((s : Γ(T.left, ⊤)) * (s : Γ(T.left, ⊤)) * u) by ring]
  rw [X.comp_conj]
  simp only [Xt]
  rw [X.comm_spec _ _ g f e₁ hf h₁, X.comm_spec _ _ g _ _ k₁ k₂, conj_commutator]

/-! ### Independence of the auxiliary unit -/

/-- The difference of the candidates for two auxiliary units. -/
def δ {T : Over S} (t d t' d' : Γ(T.left, ⊤)ˣ) (u : Γ(T.left, ⊤)) : T ⟶ X.E.X :=
  X.Xt b t d u * (X.Xt b t' d' u)⁻¹

section Delta

variable {X b}
variable {T : Over S} {t d t' d' : Γ(T.left, ⊤)ˣ}

theorem Q_δ (hd : (d : Γ(T.left, ⊤)) = t * t - 1) (hd' : (d' : Γ(T.left, ⊤)) = t' * t' - 1)
    (u : Γ(T.left, ⊤)) : X.Q T (X.δ b t d t' d' u) = 1 := by
  rw [δ, map_mul, map_inv, X.Q_Xt b hd, X.Q_Xt b hd', mul_inv_cancel]

theorem δ_central (hd : (d : Γ(T.left, ⊤)) = t * t - 1)
    (hd' : (d' : Γ(T.left, ⊤)) = t' * t' - 1) (u : Γ(T.left, ⊤)) (y : T ⟶ X.E.X) :
    Commute (X.δ b t d t' d' u) y :=
  X.central _ y (Q_δ hd hd' u)

theorem δ_res {V : Over S} (g : V ⟶ T) (u : Γ(T.left, ⊤)) :
    g ≫ X.δ b t d t' d' u = X.δ b (umap g t) (umap g d) (umap g t') (umap g d') (ring g u) := by
  rw [δ, δ, MonObj.comp_mul, GrpObj.comp_inv, X.Xt_res, X.Xt_res]

theorem δ_add (hd : (d : Γ(T.left, ⊤)) = t * t - 1)
    (hd' : (d' : Γ(T.left, ⊤)) = t' * t' - 1) (u u' : Γ(T.left, ⊤)) :
    X.δ b t d t' d' (u + u') = X.δ b t d t' d' u * X.δ b t d t' d' u' := by
  simp only [δ]
  rw [X.Xt_add, X.Xt_add]
  have hc := δ_central (X := X) (b := b) hd hd' u' (X.Xt b t' d' u)
  simp only [δ] at hc
  calc X.Xt b t d u * X.Xt b t d u' * (X.Xt b t' d' u * X.Xt b t' d' u')⁻¹
      = X.Xt b t d u * (X.Xt b t' d' u)⁻¹ *
          (X.Xt b t' d' u * (X.Xt b t d u' * (X.Xt b t' d' u')⁻¹) * (X.Xt b t' d' u)⁻¹) := by
        group
    _ = X.Xt b t d u * (X.Xt b t' d' u)⁻¹ * (X.Xt b t d u' * (X.Xt b t' d' u')⁻¹) := by
        rw [← hc.eq, mul_inv_cancel_right]

theorem δ_zero (hd : (d : Γ(T.left, ⊤)) = t * t - 1)
    (hd' : (d' : Γ(T.left, ⊤)) = t' * t' - 1) : X.δ b t d t' d' 0 = 1 := by
  have := δ_add (X := X) (b := b) hd hd' 0 0
  rw [add_zero] at this
  exact (mul_eq_left.mp this.symm)

theorem δ_neg (hd : (d : Γ(T.left, ⊤)) = t * t - 1)
    (hd' : (d' : Γ(T.left, ⊤)) = t' * t' - 1) (u : Γ(T.left, ⊤)) :
    X.δ b t d t' d' (-u) = (X.δ b t d t' d' u)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← δ_add hd hd', neg_add_cancel, δ_zero hd hd']

end Delta

theorem δ_conj {T : Over S} {t d t' d' : Γ(T.left, ⊤)ˣ}
    (hd : (d : Γ(T.left, ⊤)) = t * t - 1) (hd' : (d' : Γ(T.left, ⊤)) = t' * t' - 1)
    (s : Γ(T.left, ⊤)ˣ) (u : Γ(T.left, ⊤)) :
    X.δ b t d t' d' ((s : Γ(T.left, ⊤)) * (s : Γ(T.left, ⊤)) * u) = X.δ b t d t' d' u := by
  apply Loc.ext
  refine (X.lift (Mat.lam b s)).mono ?_
  rintro V g ⟨e, he⟩
  rw [δ_res, δ_res, map_mul, map_mul]
  rw [Mat.map_lam] at he
  simp only [δ]
  rw [← umap_coe, ← X.Xt_conj b _ _ _ he, ← X.Xt_conj b _ _ _ he]
  have hc := δ_central (X := X) (b := b) (umap_hd g hd) (umap_hd g hd') (ring g u) e
  simp only [δ] at hc
  calc e * X.Xt b (umap g t) (umap g d) (ring g u) * e⁻¹ *
        (e * X.Xt b (umap g t') (umap g d') (ring g u) * e⁻¹)⁻¹
      = e * (X.Xt b (umap g t) (umap g d) (ring g u) *
          (X.Xt b (umap g t') (umap g d') (ring g u))⁻¹) * e⁻¹ := by group
    _ = _ := by rw [← hc.eq, mul_inv_cancel_right]

theorem δ_eq_one {T : Over S} {t d t' d' : Γ(T.left, ⊤)ˣ}
    (hd : (d : Γ(T.left, ⊤)) = t * t - 1) (hd' : (d' : Γ(T.left, ⊤)) = t' * t' - 1)
    (u : Γ(T.left, ⊤)) : X.δ b t d t' d' u = 1 := by
  apply Loc.ext
  refine (Loc.exists_unit_sq_sub_one T).mono ?_
  rintro V g ⟨s, c, hc⟩
  rw [δ_res, MonObj.comp_one]
  have hdV := umap_hd g hd
  have hdV' := umap_hd g hd'
  have key : ∀ w, X.δ b (umap g t) (umap g d) (umap g t') (umap g d') ((c : Γ(V.left, ⊤)) * w)
      = 1 := by
    intro w
    rw [hc, sub_mul, one_mul, sub_eq_add_neg, δ_add hdV hdV', δ_neg hdV hdV',
      X.δ_conj b hdV hdV', mul_inv_cancel]
  rw [show ring g u = (c : Γ(V.left, ⊤)) * (↑c⁻¹ * ring g u) by
    rw [← mul_assoc, Units.mul_inv, one_mul]]
  exact key _

theorem Xt_indep {T : Over S} {t d t' d' : Γ(T.left, ⊤)ˣ}
    (hd : (d : Γ(T.left, ⊤)) = t * t - 1) (hd' : (d' : Γ(T.left, ⊤)) = t' * t' - 1)
    (u : Γ(T.left, ⊤)) : X.Xt b t d u = X.Xt b t' d' u := by
  have := X.δ_eq_one b hd hd' u
  rwa [δ, mul_inv_eq_one] at this

/-! ### The glued lifts of the root groups -/

theorem exists_rootLift {T : Over S} (u : Γ(T.left, ⊤)) :
    ∃ e : T ⟶ X.E.X, ∀ ⦃V : Over S⦄ (g : V ⟶ T) (t d : Γ(V.left, ⊤)ˣ),
      (d : Γ(V.left, ⊤)) = t * t - 1 → g ≫ e = X.Xt b t d (ring g u) := by
  obtain ⟨e, he⟩ := Loc.glue (X := X.E.X)
    (fun V g x => ∃ t d : Γ(V.left, ⊤)ˣ, (d : Γ(V.left, ⊤)) = t * t - 1 ∧
      x = X.Xt b t d (ring g u))
    (by
      rintro V W g k x ⟨t, d, hd, rfl⟩
      exact ⟨umap k t, umap k d, umap_hd k hd, by rw [X.Xt_res, ring_comp_apply]⟩)
    (by
      rintro V g x y ⟨t, d, hd, rfl⟩ ⟨t', d', hd', rfl⟩
      exact X.Xt_indep b hd hd' _)
    ((Loc.exists_unit_sq_sub_one T).mono fun V g ⟨t, d, hd⟩ => ⟨_, t, d, hd, rfl⟩)
  exact ⟨e, fun V g t d hd => he g _ ⟨t, d, hd, rfl⟩⟩

/-- The canonical lift of `root_b(u)`, glued from the local commutators. -/
def rootLift {T : Over S} (u : Γ(T.left, ⊤)) : T ⟶ X.E.X :=
  (X.exists_rootLift b u).choose

theorem rootLift_spec {T : Over S} (u : Γ(T.left, ⊤)) ⦃V : Over S⦄ (g : V ⟶ T)
    {t d : Γ(V.left, ⊤)ˣ} (hd : (d : Γ(V.left, ⊤)) = t * t - 1) :
    g ≫ X.rootLift b u = X.Xt b t d (ring g u) :=
  (X.exists_rootLift b u).choose_spec g t d hd

theorem Q_rootLift {T : Over S} (u : Γ(T.left, ⊤)) :
    X.Q T (X.rootLift b u) = Mat.root b u := by
  apply X.sep
  refine (Loc.exists_unit_sq_sub_one T).mono ?_
  rintro V g ⟨t, d, hd⟩
  rw [← X.Q_nat, X.rootLift_spec b u g hd, X.Q_Xt b hd, Mat.map_root]

theorem rootLift_res {V T : Over S} (g : V ⟶ T) (u : Γ(T.left, ⊤)) :
    g ≫ X.rootLift b u = X.rootLift b (ring g u) := by
  apply Loc.ext
  refine (Loc.exists_unit_sq_sub_one V).mono ?_
  rintro W k ⟨t, d, hd⟩
  rw [← Category.assoc, X.rootLift_spec b u _ hd, X.rootLift_spec b _ k hd, ring_comp_apply]

theorem rootLift_add {T : Over S} (u u' : Γ(T.left, ⊤)) :
    X.rootLift b (u + u') = X.rootLift b u * X.rootLift b u' := by
  apply Loc.ext
  refine (Loc.exists_unit_sq_sub_one T).mono ?_
  rintro V g ⟨t, d, hd⟩
  rw [MonObj.comp_mul, X.rootLift_spec b _ g hd, X.rootLift_spec b _ g hd,
    X.rootLift_spec b _ g hd, map_add, X.Xt_add]

theorem rootLift_zero {T : Over S} : X.rootLift b (0 : Γ(T.left, ⊤)) = 1 := by
  have := X.rootLift_add b (0 : Γ(T.left, ⊤)) 0
  rw [add_zero] at this
  exact mul_eq_left.mp this.symm

theorem rootLift_neg {T : Over S} (u : Γ(T.left, ⊤)) :
    X.rootLift b (-u) = (X.rootLift b u)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← rootLift_add, neg_add_cancel, rootLift_zero]

theorem rootLift_sub {T : Over S} (u u' : Γ(T.left, ⊤)) :
    X.rootLift b (u - u') = X.rootLift b u * (X.rootLift b u')⁻¹ := by
  rw [sub_eq_add_neg, rootLift_add, rootLift_neg]

/-- Conjugating the canonical lift by a lift of `λ_b(s)` scales it by `s²`. -/
theorem rootLift_conj {T : Over S} (u : Γ(T.left, ⊤)) {e : T ⟶ X.E.X} {s : Γ(T.left, ⊤)ˣ}
    (he : X.Q T e = Mat.lam b s) :
    e * X.rootLift b u * e⁻¹ = X.rootLift b ((s : Γ(T.left, ⊤)) * (s : Γ(T.left, ⊤)) * u) := by
  apply Loc.ext
  refine (Loc.exists_unit_sq_sub_one T).mono ?_
  rintro V g ⟨t, d, hd⟩
  have hge : X.Q V (g ≫ e) = Mat.lam b (umap g s) := by rw [X.Q_nat, he, Mat.map_lam]
  rw [X.comp_conj, X.rootLift_spec b _ g hd, X.rootLift_spec b _ g hd, X.Xt_conj b _ _ _ hge,
    map_mul, map_mul, umap_coe]

/-- Lifts of `root_b(u)` and the canonical lift differ by a central element. -/
theorem rootLift_central_of_Q {T : Over S} {u : Γ(T.left, ⊤)} {e : T ⟶ X.E.X}
    (he : X.Q T e = Mat.root b u) : ∀ y, Commute ((X.rootLift b u)⁻¹ * e) y :=
  X.central_of_eq (by rw [Q_rootLift, he])

end Ext

end Langlands.GroupScheme.SL2CentralExtension
