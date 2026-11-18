import Langlands.GroupScheme.SL2CentralExtension.Splitting

/-! # The lifted torus and the relation `x'(u) y'(v) = y'(v/s) h'(s) x'(u/s)` -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SL2CentralExtension

variable {S : Scheme.{u}}

/-- Fppf-locally every unit is a square. -/
theorem Loc.exists_sqrt {T : Over S} (a : Γ(T.left, ⊤)ˣ) :
    Loc (fun V (g : V ⟶ T) => ∃ r : Γ(V.left, ⊤)ˣ, r * r = umap g a) := by
  rcases subsingleton_or_nontrivial Γ(T.left, ⊤) with hT | hT
  · refine Loc.of_forall fun V g => ⟨1, ?_⟩
    have h01 : (0 : Γ(V.left, ⊤)) = 1 := by
      rw [← map_zero (ring g), ← map_one (ring g), Subsingleton.elim (0 : Γ(T.left, ⊤)) 1]
    have : Subsingleton Γ(V.left, ⊤) := subsingleton_of_zero_eq_one h01
    exact Subsingleton.elim _ _
  have hp : (Polynomial.X ^ 2 - Polynomial.C (a : Γ(T.left, ⊤))).Monic :=
    Polynomial.monic_X_pow_sub_C _ two_ne_zero
  have hdeg : 0 < (Polynomial.X ^ 2 - Polynomial.C (a : Γ(T.left, ⊤))).natDegree := by
    rw [Polynomial.natDegree_X_pow_sub_C]; norm_num
  refine (Loc.exists_root _ hp hdeg).mono ?_
  rintro V g ⟨r, hr⟩
  simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
    Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at hr
  have hrs : r * r = ring g a := by rw [← sq]; exact sub_eq_zero.mp hr
  have hrr : IsUnit (r * r) := by rw [hrs]; exact a.isUnit.map (ring g)
  have hru : IsUnit r := isUnit_of_mul_isUnit_left hrr
  exact ⟨hru.unit, Units.ext (by rw [Units.val_mul, IsUnit.unit_spec, hrs, umap_coe])⟩

namespace Ext

variable (X : Ext S)

/-! ### Commutativity of lifts of diagonal matrices -/

/-- Lifts of diagonal matrices commute (the commutativity of `D'` in Conrad's proof). -/
def DComm : Prop :=
  ∀ ⦃T : Over S⦄ (s t : Γ(T.left, ⊤)ˣ), X.comm (Mat.h s) (Mat.h t) = 1

theorem commute_h {X : Ext S} (hD : X.DComm) {T : Over S} {e e' : T ⟶ X.E.X} {s t : Γ(T.left, ⊤)ˣ}
    (he : X.Q T e = Mat.h s) (he' : X.Q T e' = Mat.h t) : Commute e e' := by
  have := X.comm_eq he he'
  rw [hD] at this
  exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp this.symm)

/-! ### The lifts `x'` and `y'` -/

/-- The canonical lift `x'(u)` of `x(u)`. -/
def xl {T : Over S} (u : Γ(T.left, ⊤)) : T ⟶ X.E.X := X.rootLift false u

/-- The canonical lift `y'(v)` of `y(v)`. -/
def yl {T : Over S} (v : Γ(T.left, ⊤)) : T ⟶ X.E.X := X.rootLift true v

variable {T : Over S}

theorem Q_xl (u : Γ(T.left, ⊤)) : X.Q T (X.xl u) = Mat.x u := X.Q_rootLift false u

theorem Q_yl (v : Γ(T.left, ⊤)) : X.Q T (X.yl v) = Mat.y v := X.Q_rootLift true v

theorem xl_res {V : Over S} (g : V ⟶ T) (u : Γ(T.left, ⊤)) :
    g ≫ X.xl u = X.xl (ring g u) := X.rootLift_res false g u

theorem yl_res {V : Over S} (g : V ⟶ T) (v : Γ(T.left, ⊤)) :
    g ≫ X.yl v = X.yl (ring g v) := X.rootLift_res true g v

theorem xl_add (u u' : Γ(T.left, ⊤)) : X.xl (u + u') = X.xl u * X.xl u' :=
  X.rootLift_add false u u'

theorem yl_add (v v' : Γ(T.left, ⊤)) : X.yl (v + v') = X.yl v * X.yl v' :=
  X.rootLift_add true v v'

theorem xl_zero : X.xl (0 : Γ(T.left, ⊤)) = 1 := X.rootLift_zero false

theorem yl_zero : X.yl (0 : Γ(T.left, ⊤)) = 1 := X.rootLift_zero true

theorem xl_neg (u : Γ(T.left, ⊤)) : X.xl (-u) = (X.xl u)⁻¹ := X.rootLift_neg false u

theorem yl_neg (v : Γ(T.left, ⊤)) : X.yl (-v) = (X.yl v)⁻¹ := X.rootLift_neg true v

theorem xl_conj (u : Γ(T.left, ⊤)) {e : T ⟶ X.E.X} {s : Γ(T.left, ⊤)ˣ}
    (he : X.Q T e = Mat.h s) :
    e * X.xl u * e⁻¹ = X.xl ((s : Γ(T.left, ⊤)) * (s : Γ(T.left, ⊤)) * u) :=
  X.rootLift_conj false u he

theorem yl_conj (v : Γ(T.left, ⊤)) {e : T ⟶ X.E.X} {s : Γ(T.left, ⊤)ˣ}
    (he : X.Q T e = Mat.h s) :
    e * X.yl v * e⁻¹ = X.yl ((↑s⁻¹ : Γ(T.left, ⊤)) * (↑s⁻¹ : Γ(T.left, ⊤)) * v) :=
  X.rootLift_conj true v (s := s⁻¹) (by rw [he]; change Mat.h s = Mat.h s⁻¹⁻¹; rw [inv_inv])

/-! ### The lifts `g'(t) = y'(-1/t) x'(t) y'(-1/t)` and `h'(t) = g'(t) g'(1)⁻¹` -/

/-- Conrad's `g'(t) = y'(-1/t) x'(t) y'(-1/t)`, a lift of `w(t)`. -/
def gl (t : Γ(T.left, ⊤)ˣ) : T ⟶ X.E.X :=
  X.yl (-(↑t⁻¹ : Γ(T.left, ⊤))) * X.xl (t : Γ(T.left, ⊤)) * X.yl (-(↑t⁻¹ : Γ(T.left, ⊤)))

/-- Conrad's `h'(t) = g'(t) g'(1)⁻¹`, a lift of `h(t)`. -/
def hl (t : Γ(T.left, ⊤)ˣ) : T ⟶ X.E.X := X.gl t * (X.gl 1)⁻¹

theorem Q_gl (t : Γ(T.left, ⊤)ˣ) : X.Q T (X.gl t) = Mat.w t := by
  rw [gl, map_mul, map_mul, Q_xl, Q_yl, Mat.w]

theorem Q_hl (t : Γ(T.left, ⊤)ˣ) : X.Q T (X.hl t) = Mat.h t := by
  rw [hl, map_mul, map_inv, Q_gl, Q_gl, Mat.w_mul_w_one_inv]

theorem gl_res {V : Over S} (g : V ⟶ T) (t : Γ(T.left, ⊤)ˣ) :
    g ≫ X.gl t = X.gl (umap g t) := by
  rw [gl, gl, MonObj.comp_mul, MonObj.comp_mul, xl_res, yl_res, map_neg, ← map_inv, umap_coe,
    umap_coe]

theorem hl_res {V : Over S} (g : V ⟶ T) (t : Γ(T.left, ⊤)ˣ) :
    g ≫ X.hl t = X.hl (umap g t) := by
  rw [hl, hl, MonObj.comp_mul, GrpObj.comp_inv, gl_res, gl_res, map_one]

theorem hl_one : X.hl (1 : Γ(T.left, ⊤)ˣ) = 1 := mul_inv_cancel _

theorem gl_conj (t : Γ(T.left, ⊤)ˣ) {e : T ⟶ X.E.X} {s : Γ(T.left, ⊤)ˣ}
    (he : X.Q T e = Mat.h s) : e * X.gl t * e⁻¹ = X.gl (s * s * t) := by
  have h1 : e * X.gl t * e⁻¹ = (e * X.yl (-(↑t⁻¹ : Γ(T.left, ⊤))) * e⁻¹) *
      (e * X.xl (t : Γ(T.left, ⊤)) * e⁻¹) * (e * X.yl (-(↑t⁻¹ : Γ(T.left, ⊤))) * e⁻¹) := by
    rw [gl]; group
  rw [h1, X.yl_conj _ he, X.xl_conj _ he, gl]
  have hy : (↑s⁻¹ : Γ(T.left, ⊤)) * ↑s⁻¹ * -↑t⁻¹ = -↑(s * s * t)⁻¹ := by
    simp only [mul_inv_rev, Units.val_mul]; ring
  rw [hy, Units.val_mul, Units.val_mul]

theorem hl_conj (t : Γ(T.left, ⊤)ˣ) {e : T ⟶ X.E.X} {s : Γ(T.left, ⊤)ˣ}
    (he : X.Q T e = Mat.h s) : e * X.hl t * e⁻¹ = X.gl (s * s * t) * (X.gl (s * s))⁻¹ := by
  have h1 : e * X.hl t * e⁻¹ = (e * X.gl t * e⁻¹) * (e * X.gl 1 * e⁻¹)⁻¹ := by
    rw [hl]; group
  rw [h1, X.gl_conj _ he, X.gl_conj _ he, mul_one]

/-! ### Commutation of `h'` with `x'` and `y'` -/

theorem hl_xl (s : Γ(T.left, ⊤)ˣ) (u : Γ(T.left, ⊤)) :
    X.hl s * X.xl u = X.xl ((s : Γ(T.left, ⊤)) * (s : Γ(T.left, ⊤)) * u) * X.hl s := by
  rw [← X.xl_conj u (X.Q_hl s)]; group

theorem hl_yl (s : Γ(T.left, ⊤)ˣ) (v : Γ(T.left, ⊤)) :
    X.hl s * X.yl v = X.yl ((↑s⁻¹ : Γ(T.left, ⊤)) * (↑s⁻¹ : Γ(T.left, ⊤)) * v) * X.hl s := by
  rw [← X.yl_conj v (X.Q_hl s)]; group

theorem Q_hl_inv (s : Γ(T.left, ⊤)ˣ) : X.Q T (X.hl s)⁻¹ = Mat.h s⁻¹ := by
  rw [map_inv, Q_hl, Mat.h_inv]

theorem xl_hl (s : Γ(T.left, ⊤)ˣ) (u : Γ(T.left, ⊤)) :
    X.xl u * X.hl s = X.hl s * X.xl ((↑s⁻¹ : Γ(T.left, ⊤)) * (↑s⁻¹ : Γ(T.left, ⊤)) * u) := by
  rw [← X.xl_conj u (X.Q_hl_inv s)]; group

theorem yl_hl (s : Γ(T.left, ⊤)ˣ) (v : Γ(T.left, ⊤)) :
    X.yl v * X.hl s = X.hl s * X.yl ((s : Γ(T.left, ⊤)) * (s : Γ(T.left, ⊤)) * v) := by
  have := X.yl_conj v (X.Q_hl_inv s)
  simp only [inv_inv] at this
  rw [← this]; group

/-! ### `h'` is a homomorphism -/

variable {X}

theorem hl_sq_mul (hD : X.DComm) (s t : Γ(T.left, ⊤)ˣ) :
    X.hl (s * s * t) = X.hl t * X.hl (s * s) := by
  have h1 := X.hl_conj t (X.Q_hl s)
  rw [(commute_h hD (X.Q_hl s) (X.Q_hl t)).eq, mul_inv_cancel_right] at h1
  have h2 : X.gl (s * s * t) * (X.gl (s * s))⁻¹ = X.hl (s * s * t) * (X.hl (s * s))⁻¹ := by
    rw [hl, hl]; group
  rw [h2] at h1
  rw [h1, inv_mul_cancel_right]

theorem hl_mul (hD : X.DComm) (a b : Γ(T.left, ⊤)ˣ) : X.hl (a * b) = X.hl a * X.hl b := by
  apply Loc.ext
  refine (Loc.exists_sqrt a).mono ?_
  rintro V g ⟨r, hr⟩
  rw [MonObj.comp_mul, hl_res, hl_res, hl_res, map_mul, ← hr, hl_sq_mul hD,
    (commute_h hD (X.Q_hl _) (X.Q_hl _)).eq]

theorem hl_inv (hD : X.DComm) (a : Γ(T.left, ⊤)ˣ) : X.hl a⁻¹ = (X.hl a)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← hl_mul hD, inv_mul_cancel, hl_one]

theorem gl_mul_left (hD : X.DComm) (s t : Γ(T.left, ⊤)ˣ) : X.gl (s * t) = X.hl s * X.gl t := by
  have h := hl_mul hD s t
  rw [show X.hl (s * t) = X.gl (s * t) * (X.gl 1)⁻¹ from rfl,
    show X.hl t = X.gl t * (X.gl 1)⁻¹ from rfl, ← mul_assoc] at h
  exact mul_right_cancel h

/-! ### The relation `x'(u) y'(v) = y'(v/s) h'(s) x'(u/s)` for `s = 1 + uv` -/

/-- The relation when `u` is a unit (Conrad, proof of Proposition 4.3.1). -/
theorem xl_yl_of_unit (hD : X.DComm) (u s : Γ(T.left, ⊤)ˣ) (v : Γ(T.left, ⊤))
    (hs : (s : Γ(T.left, ⊤)) = 1 + u * v) :
    X.xl (u : Γ(T.left, ⊤)) * X.yl v =
      X.yl (v * (↑s⁻¹ : Γ(T.left, ⊤))) * X.hl s *
        X.xl ((u : Γ(T.left, ⊤)) * (↑s⁻¹ : Γ(T.left, ⊤))) := by
  obtain ⟨t, ht⟩ : ∃ t : Γ(T.left, ⊤)ˣ, t = u * s⁻¹ := ⟨_, rfl⟩
  have htv : (t : Γ(T.left, ⊤)) = ↑u * ↑s⁻¹ := by rw [ht, Units.val_mul]
  have htinv : (↑t⁻¹ : Γ(T.left, ⊤)) = ↑s * ↑u⁻¹ := by
    rw [ht, mul_inv_rev, inv_inv, Units.val_mul]
  have hg : X.gl u = X.hl s * X.gl t := by
    rw [← gl_mul_left hD, ht, mul_comm u, mul_inv_cancel_left]
  simp only [gl] at hg
  have hcomm := X.hl_yl s (-(↑t⁻¹ : Γ(T.left, ⊤)))
  have hu : (u : Γ(T.left, ⊤)) * ↑u⁻¹ = 1 := Units.mul_inv u
  have hs' : (s : Γ(T.left, ⊤)) * ↑s⁻¹ = 1 := Units.mul_inv s
  have e1 : -(↑t⁻¹ : Γ(T.left, ⊤)) + ((↑u⁻¹ : Γ(T.left, ⊤)) + v) = 0 := by
    rw [htinv]; linear_combination (-(↑u⁻¹ : Γ(T.left, ⊤))) * hs + (-v) * hu
  have e2 : (↑u⁻¹ : Γ(T.left, ⊤)) + ↑s⁻¹ * ↑s⁻¹ * -↑t⁻¹ = v * ↑s⁻¹ := by
    rw [htinv]
    linear_combination (-((↑s⁻¹ : Γ(T.left, ⊤)) * ↑u⁻¹) - ↑u⁻¹) * hs' +
      ((↑s⁻¹ : Γ(T.left, ⊤)) * ↑u⁻¹) * hs + ((↑s⁻¹ : Γ(T.left, ⊤)) * v) * hu
  calc X.xl (u : Γ(T.left, ⊤)) * X.yl v
      = X.yl ↑u⁻¹ * (X.yl (-(↑u⁻¹ : Γ(T.left, ⊤))) * X.xl (u : Γ(T.left, ⊤)) *
          X.yl (-(↑u⁻¹ : Γ(T.left, ⊤)))) * X.yl ((↑u⁻¹ : Γ(T.left, ⊤)) + v) := by
        rw [yl_add, yl_neg]; group
    _ = X.yl ↑u⁻¹ * (X.hl s * X.yl (-(↑t⁻¹ : Γ(T.left, ⊤)))) * X.xl (t : Γ(T.left, ⊤)) *
          X.yl (-(↑t⁻¹ : Γ(T.left, ⊤)) + ((↑u⁻¹ : Γ(T.left, ⊤)) + v)) := by
        rw [hg, X.yl_add (-(↑t⁻¹ : Γ(T.left, ⊤)))]; group
    _ = X.yl ↑u⁻¹ * X.yl ((↑s⁻¹ : Γ(T.left, ⊤)) * ↑s⁻¹ * -↑t⁻¹) * X.hl s *
          X.xl (t : Γ(T.left, ⊤)) := by
        rw [hcomm, e1, yl_zero]; group
    _ = _ := by rw [← yl_add, e2, htv]

/-- The relation, given a splitting `u = u' + u''` into units with `1 + u''v` a unit. -/
theorem xl_yl_of_split (hD : X.DComm) (u v : Γ(T.left, ⊤)) (s : Γ(T.left, ⊤)ˣ)
    (hs : (s : Γ(T.left, ⊤)) = 1 + u * v) (u' u'' s'' : Γ(T.left, ⊤)ˣ)
    (hu : u = u' + u'') (hs'' : (s'' : Γ(T.left, ⊤)) = 1 + u'' * v) :
    X.xl u * X.yl v =
      X.yl (v * (↑s⁻¹ : Γ(T.left, ⊤))) * X.hl s * X.xl (u * (↑s⁻¹ : Γ(T.left, ⊤))) := by
  obtain ⟨q, hq⟩ : ∃ q : Γ(T.left, ⊤)ˣ, q = s * s''⁻¹ := ⟨_, rfl⟩
  have hsi : (s : Γ(T.left, ⊤)) * ↑s⁻¹ = 1 := Units.mul_inv s
  have hsi'' : (s'' : Γ(T.left, ⊤)) * ↑s''⁻¹ = 1 := Units.mul_inv s''
  have hqv : (q : Γ(T.left, ⊤)) = 1 + u' * (v * ↑s''⁻¹) := by
    rw [hq, Units.val_mul]
    linear_combination (↑s''⁻¹ : Γ(T.left, ⊤)) * hs - (↑s''⁻¹ : Γ(T.left, ⊤)) * hs'' +
      (v * (↑s''⁻¹ : Γ(T.left, ⊤))) * hu + hsi''
  have hqinv : (↑q⁻¹ : Γ(T.left, ⊤)) = ↑s'' * ↑s⁻¹ := by
    rw [hq, mul_inv_rev, inv_inv, Units.val_mul]
  have hqs : q * s'' = s := by rw [hq, inv_mul_cancel_right]
  have e1 : v * ↑s''⁻¹ * (↑q⁻¹ : Γ(T.left, ⊤)) = v * ↑s⁻¹ := by
    rw [hqinv]; linear_combination (v * ↑s⁻¹) * hsi''
  have e2 : (↑s''⁻¹ : Γ(T.left, ⊤)) * ↑s''⁻¹ * (u' * ↑q⁻¹) + u'' * ↑s''⁻¹ = u * ↑s⁻¹ := by
    rw [hqinv]
    linear_combination ((↑s''⁻¹ : Γ(T.left, ⊤)) * u' * ↑s⁻¹ + u * ↑s⁻¹) * hsi'' -
      ((u'' : Γ(T.left, ⊤)) * ↑s''⁻¹) * hsi + ((u'' : Γ(T.left, ⊤)) * ↑s''⁻¹ * ↑s⁻¹) * hs -
      ((↑s''⁻¹ : Γ(T.left, ⊤)) * ↑s⁻¹) * hu - ((↑s''⁻¹ : Γ(T.left, ⊤)) * ↑s⁻¹ * u) * hs''
  calc X.xl u * X.yl v = X.xl (u' : Γ(T.left, ⊤)) * (X.xl (u'' : Γ(T.left, ⊤)) * X.yl v) := by
        rw [hu, xl_add, mul_assoc]
    _ = X.xl (u' : Γ(T.left, ⊤)) * X.yl (v * ↑s''⁻¹) * X.hl s'' *
          X.xl ((u'' : Γ(T.left, ⊤)) * ↑s''⁻¹) := by
        rw [xl_yl_of_unit hD u'' s'' v hs'']; group
    _ = X.yl (v * ↑s''⁻¹ * ↑q⁻¹) * X.hl q * (X.xl ((u' : Γ(T.left, ⊤)) * ↑q⁻¹) * X.hl s'') *
          X.xl ((u'' : Γ(T.left, ⊤)) * ↑s''⁻¹) := by
        rw [xl_yl_of_unit hD u' q (v * ↑s''⁻¹) hqv]; group
    _ = X.yl (v * ↑s''⁻¹ * ↑q⁻¹) * (X.hl q * X.hl s'') *
          (X.xl ((↑s''⁻¹ : Γ(T.left, ⊤)) * ↑s''⁻¹ * ((u' : Γ(T.left, ⊤)) * ↑q⁻¹)) *
            X.xl ((u'' : Γ(T.left, ⊤)) * ↑s''⁻¹)) := by
        rw [xl_hl]; simp only [mul_assoc]
    _ = _ := by rw [← hl_mul hD, hqs, ← xl_add, e1, e2]

/-- Conrad's relation (4.3.1): `x'(u) y'(v) = y'(v/s) h'(s) x'(u/s)` whenever `s = 1 + uv` is a
unit. -/
theorem xl_yl (hD : X.DComm) (u v : Γ(T.left, ⊤)) (s : Γ(T.left, ⊤)ˣ)
    (hs : (s : Γ(T.left, ⊤)) = 1 + u * v) :
    X.xl u * X.yl v =
      X.yl (v * (↑s⁻¹ : Γ(T.left, ⊤))) * X.hl s * X.xl (u * (↑s⁻¹ : Γ(T.left, ⊤))) := by
  apply Loc.ext
  let p : Polynomial Γ(T.left, ⊤) := Polynomial.X * (Polynomial.C u - Polynomial.X) *
    (1 + Polynomial.C v * Polynomial.X)
  have hp : Nondeg p := by
    refine (Nondeg.monic Polynomial.monic_X).mul (Nondeg.of_coeff 1 ?_) |>.mul
      (Nondeg.of_coeff 0 ?_)
    · simp only [Polynomial.coeff_sub, Polynomial.coeff_C, Polynomial.coeff_X_one]
      simp
    · simp
  refine (Loc.exists_isUnit_eval p hp).mono ?_
  rintro V g ⟨r, hr⟩
  simp only [p, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_X,
    Polynomial.map_C, Polynomial.map_one, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one] at hr
  rw [IsUnit.mul_iff, IsUnit.mul_iff] at hr
  obtain ⟨⟨h1, h2⟩, h3⟩ := hr
  rw [MonObj.comp_mul, MonObj.comp_mul, MonObj.comp_mul, xl_res, yl_res, yl_res, hl_res, xl_res,
    map_mul, map_mul, ← umap_coe g s⁻¹, map_inv]
  refine xl_yl_of_split hD _ _ _ ?_ h2.unit h1.unit h3.unit ?_ ?_
  · rw [umap_coe, hs, map_add, map_one, map_mul]
  · rw [IsUnit.unit_spec, IsUnit.unit_spec, sub_add_cancel]
  · rw [IsUnit.unit_spec, IsUnit.unit_spec, mul_comm]

end Ext

end Langlands.GroupScheme.SL2CentralExtension
