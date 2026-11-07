import Langlands.GroupScheme.Rational.VectorActionWeightCommuting

/-! # Bilinearity of equivariant pairings of weight vector groups

A pairing `V × V → W` of vector groups is bilinear over every test scheme's ring of global
functions in weight vector coordinates. The conditions are that it is multiplicative in each
argument and that it intertwines a split-torus action of one nonzero weight `χ` on `V` with an
action of weight `2 • χ` on `W`. This holds in every characteristic. The torus point `ζ(t)`
over `A[t, t⁻¹]`, for a cocharacter `ζ` with `⟨χ, ζ⟩ = D > 0`, makes the coordinates of the
pairing homogeneous of degree two. Comparing the substitutions `X ↦ t` and `X ↦ t⁻¹` in
Laurent polynomials then leaves only the bilinear terms.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj LaurentPolynomial Polynomial

namespace Langlands.GroupScheme.RelativeRoot

section Laurent

variable {A : Type u} [CommRing A]

/-- The nonnegative part of `t ^ 2 q(t⁻¹)` is the reflection of the terms of `q` of degree at
most two. -/
theorem trunc_T_two_mul_invert_toLaurent (q : A[X]) :
    LaurentPolynomial.trunc
        (LaurentPolynomial.T 2 * LaurentPolynomial.invert (Polynomial.toLaurent q)) =
      Polynomial.C (q.coeff 0) * Polynomial.X ^ 2 + Polynomial.C (q.coeff 1) * Polynomial.X +
        Polynomial.C (q.coeff 2) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, map_add, mul_add, map_add, hp, hq]
    simp only [Polynomial.coeff_add, map_add]
    ring
  | monomial n r =>
    have hm : LaurentPolynomial.T 2 * LaurentPolynomial.invert
        (LaurentPolynomial.C r * LaurentPolynomial.T (n : ℤ) : A[T;T⁻¹]) =
        LaurentPolynomial.C r * LaurentPolynomial.T (2 + -(n : ℤ)) := by
      rw [map_mul LaurentPolynomial.invert, LaurentPolynomial.invert_C,
        LaurentPolynomial.invert_T, ← mul_assoc, (LaurentPolynomial.commute_T 2 _).eq,
        mul_assoc, ← LaurentPolynomial.T_add]
    rw [Polynomial.toLaurent_C_mul_T, hm, LaurentPolynomial.trunc_C_mul_T]
    rcases n with _ | _ | _ | n
    · simp [Polynomial.C_mul_X_pow_eq_monomial]
    · simp [Polynomial.C_mul_X_eq_monomial, Polynomial.coeff_monomial]
    · simp [Polynomial.coeff_monomial]
    · have h : ¬ (0 : ℤ) ≤ 2 + -((n + 3 : ℕ) : ℤ) := by omega
      simp only [h, ite_false, Polynomial.coeff_monomial]
      simp

/-- If `p(t) = t ^ 2 q(t⁻¹)`, then `p` is the reflection of the terms of `q` of degree at most
two. -/
theorem eq_of_toLaurent_eq_T_two_mul_invert {p q : A[X]}
    (h : Polynomial.toLaurent p =
      LaurentPolynomial.T 2 * LaurentPolynomial.invert (Polynomial.toLaurent q)) :
    p = Polynomial.C (q.coeff 0) * Polynomial.X ^ 2 + Polynomial.C (q.coeff 1) * Polynomial.X +
      Polynomial.C (q.coeff 2) := by
  rw [← Polynomial.trunc_toLaurent p, h, trunc_T_two_mul_invert_toLaurent]

/-- The relation `p(t) = t ^ 2 q(t⁻¹)` is symmetric in `p` and `q`. -/
theorem toLaurent_eq_T_two_mul_invert_symm {p q : A[X]}
    (h : Polynomial.toLaurent p =
      LaurentPolynomial.T 2 * LaurentPolynomial.invert (Polynomial.toLaurent q)) :
    Polynomial.toLaurent q =
      LaurentPolynomial.T 2 * LaurentPolynomial.invert (Polynomial.toLaurent p) := by
  rw [h, map_mul, LaurentPolynomial.invert_T, ← mul_assoc, ← LaurentPolynomial.T_add]
  have hi : LaurentPolynomial.invert (LaurentPolynomial.invert (Polynomial.toLaurent q)) =
      Polynomial.toLaurent q := LaurentPolynomial.involutive_invert _
  rw [hi]
  norm_num [LaurentPolynomial.T_zero]

/-- With vanishing constant terms, `p(t) = t ^ 2 q(t⁻¹)` forces `p = c X` and `q = c X` for the
same constant `c`. -/
theorem eq_C_mul_X_of_toLaurent_eq_T_two_mul_invert {p q : A[X]}
    (h : Polynomial.toLaurent p =
      LaurentPolynomial.T 2 * LaurentPolynomial.invert (Polynomial.toLaurent q))
    (hp : p.coeff 0 = 0) (hq : q.coeff 0 = 0) :
    p = Polynomial.C (p.coeff 1) * Polynomial.X ∧ q = Polynomial.C (p.coeff 1) * Polynomial.X := by
  have hp' := eq_of_toLaurent_eq_T_two_mul_invert h
  have hq' := eq_of_toLaurent_eq_T_two_mul_invert (toLaurent_eq_T_two_mul_invert_symm h)
  have hp2 : q.coeff 2 = 0 := by
    have := congrArg (fun f => Polynomial.coeff f 0) hp'
    simpa [hp] using this.symm
  have hq1 : p.coeff 1 = q.coeff 1 := by
    have := congrArg (fun f => Polynomial.coeff f 1) hp'
    simpa using this
  refine ⟨?_, ?_⟩
  · conv_lhs => rw [hp']
    rw [hq, hp2, hq1]
    simp
  · rw [hq1]
    have hq2 : p.coeff 2 = 0 := by
      have := congrArg (fun f => Polynomial.coeff f 0) hq'
      simpa [hq] using this.symm
    conv_lhs => rw [hq']
    rw [hp, hq2, ← hq1]
    have := congrArg (fun f => Polynomial.coeff f 1) hq'
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C] at this
    simp

end Laurent

variable {k : Type u} [Field k] {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {V W : GroupScheme (Spec (CommRingCat.of k))} {d m : ℕ}

section Coordinates

variable (e : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ V.X) ≃* Multiplicative (Fin d → Γ(T.left, ⊤)))
    (e' : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ W.X) ≃* Multiplicative (Fin m → Γ(T.left, ⊤)))
    (P : V.X ⊗ V.X ⟶ W.X)

/-- A pairing of vector groups, written in the coefficient coordinates `e` and `e'`. -/
def coordinatePairing {A : Type u} [CommRing A] [Algebra k A] (x y : Fin d → A) : Fin m → A :=
  (vectorAffineCoordinates e' A
    (lift ((vectorAffineCoordinates e A).symm (Multiplicative.ofAdd x))
      ((vectorAffineCoordinates e A).symm (Multiplicative.ofAdd y)) ≫ P)).toAdd

/-- Scalar linearity of a pairing in each argument and additivity in each argument, in the
vector coordinates `e` and `e'` over every test scheme's ring of global functions. -/
def IsBilinearVectorPairing : Prop :=
  ∀ (T : Over (Spec (CommRingCat.of k))) (x x' y y' : T ⟶ V.X) (r : Γ(T.left, ⊤)),
    (e' T (lift (x * x') y ≫ P)).toAdd =
        (e' T (lift x y ≫ P)).toAdd + (e' T (lift x' y ≫ P)).toAdd ∧
      (e' T (lift x (y * y') ≫ P)).toAdd =
        (e' T (lift x y ≫ P)).toAdd + (e' T (lift x y' ≫ P)).toAdd ∧
      (e' T (lift ((e T).symm (Multiplicative.ofAdd (r • (e T x).toAdd))) y ≫ P)).toAdd =
        r • (e' T (lift x y ≫ P)).toAdd ∧
      (e' T (lift x ((e T).symm (Multiplicative.ofAdd (r • (e T y).toAdd))) ≫ P)).toAdd =
        r • (e' T (lift x y ≫ P)).toAdd

variable {e e' P}

theorem coordinatePairing_naturality (he : IsNaturalVectorCoordinates e)
    (he' : IsNaturalVectorCoordinates e')
    {A B : Type u} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
    (f : A →ₐ[k] B) (x y : Fin d → A) :
    coordinatePairing e e' P (fun j => f (x j)) (fun j => f (y j)) =
      fun l => f (coordinatePairing e e' P x y l) := by
  have hx (z : Fin d → A) : Lie.affineMap V f
      ((vectorAffineCoordinates e A).symm (Multiplicative.ofAdd z)) =
      (vectorAffineCoordinates e B).symm (Multiplicative.ofAdd fun j => f (z j)) := by
    apply (vectorAffineCoordinates e B).injective
    apply Multiplicative.toAdd.injective
    rw [he.vectorAffineCoordinates_naturality, MulEquiv.apply_symm_apply]
    simp only [MulEquiv.apply_symm_apply, toAdd_ofAdd]
  have hW := he'.vectorAffineCoordinates_naturality f
    (lift ((vectorAffineCoordinates e A).symm (Multiplicative.ofAdd x))
      ((vectorAffineCoordinates e A).symm (Multiplicative.ofAdd y)) ≫ P)
  dsimp only [coordinatePairing]
  rw [← hW, ← hx x, ← hx y]
  congr 2
  simp only [Lie.affineMap_apply]
  rw [← Category.assoc, comp_lift]

/-- The pairing at the identity in one argument is trivial in coordinates. -/
theorem coordinatePairing_zero_left
    (h1 : ∀ (T : Over (Spec (CommRingCat.of k))) (y : T ⟶ V.X), lift 1 y ≫ P = 1)
    {A : Type u} [CommRing A] [Algebra k A] (y : Fin d → A) :
    coordinatePairing e e' P 0 y = 0 := by
  dsimp only [coordinatePairing]
  rw [ofAdd_zero, map_one, h1, map_one, toAdd_one]

theorem coordinatePairing_zero_right
    (h1 : ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ V.X), lift x 1 ≫ P = 1)
    {A : Type u} [CommRing A] [Algebra k A] (x : Fin d → A) :
    coordinatePairing e e' P x 0 = 0 := by
  dsimp only [coordinatePairing]
  rw [ofAdd_zero, map_one, h1, map_one, toAdd_one]

variable {c : AutomorphicAction S.toGrp V} {c' : AutomorphicAction S.toGrp W}
    {χ ψ : characterLattice S}

/-- An equivariant pairing scales by the value of `ψ` when both arguments are scaled by the
value of `χ` at a torus point. -/
theorem coordinatePairing_weight_smul (he : IsWeightVectorCoordinates c χ e)
    (he' : IsWeightVectorCoordinates c' ψ e')
    (hP : ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (x y : T ⟶ V.X),
      lift (c.act s x) (c.act s y) ≫ P = c'.act s (lift x y ≫ P))
    {A : Type u} [CommRing A] [Algebra k A] (s : Lie.AffinePoints S.toGrp A) {w w' : A}
    (hw : (Scheme.ΓSpecIso (CommRingCat.of A)).hom
        (Gm.pointsEquiv _ ((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k A)))
          (s ≫ (CommGroupScheme.groupHom χ).hom.hom) :
            Γ(((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k A))).left, ⊤)) = w)
    (hw' : (Scheme.ΓSpecIso (CommRingCat.of A)).hom
        (Gm.pointsEquiv _ ((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k A)))
          (s ≫ (CommGroupScheme.groupHom ψ).hom.hom) :
            Γ(((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k A))).left, ⊤)) = w')
    (x y : Fin d → A) :
    coordinatePairing e e' P (w • x) (w • y) = w' • coordinatePairing e e' P x y := by
  have hx (z : Fin d → A) : (vectorAffineCoordinates e A).symm (Multiplicative.ofAdd (w • z)) =
      c.act s ((vectorAffineCoordinates e A).symm (Multiplicative.ofAdd z)) := by
    apply (vectorAffineCoordinates e A).injective
    apply Multiplicative.toAdd.injective
    rw [MulEquiv.apply_symm_apply, he.vectorAffineCoordinates_act, MulEquiv.apply_symm_apply,
      hw]
    rfl
  dsimp only [coordinatePairing]
  rw [hx x, hx y, hP, he'.vectorAffineCoordinates_act, hw']

/-- **Homogeneity.** An equivariant pairing of weights `χ` and `2 • χ`, with `χ ≠ 0`, is
homogeneous of degree two in coordinates. -/
theorem coordinatePairing_smul_smul (hS : IsSplitTorus S.toGrp) (hχ : χ ≠ 0)
    (he : IsWeightVectorCoordinates c χ e) (he' : IsWeightVectorCoordinates c' (2 • χ) e')
    (hP : ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (x y : T ⟶ V.X),
      lift (c.act s x) (c.act s y) ≫ P = c'.act s (lift x y ≫ P))
    {A : Type u} [CommRing A] [Algebra k A] (r : A) (x y : Fin d → A) :
    coordinatePairing e e' P (r • x) (r • y) = r ^ 2 • coordinatePairing e e' P x y := by
  obtain ⟨D, hD, ζ, hζ⟩ := hS.exists_pairing_eq_pos hχ
  have hζ2 : latticePairing S (2 • χ) ζ = ((2 * D : ℕ) : ℤ) := by
    rw [map_nsmul, LinearMap.smul_apply, hζ]
    push_cast
    ring
  let X' : Fin d → A[X] := fun j => Polynomial.X * Polynomial.C (x j)
  let Y' : Fin d → A[X] := fun j => Polynomial.X * Polynomial.C (y j)
  let Q := coordinatePairing e e' P X' Y'
  let φ := laurentPowerAlgHom (k := k) A D
  have hX : (fun j => φ (X' j)) =
      (LaurentPolynomial.T D : A[T;T⁻¹]) • fun j => laurentCAlgHom (k := k) A (x j) := by
    funext j
    simp [X', φ, laurentPowerAlgHom]
  have hY : (fun j => φ (Y' j)) =
      (LaurentPolynomial.T D : A[T;T⁻¹]) • fun j => laurentCAlgHom (k := k) A (y j) := by
    funext j
    simp [Y', φ, laurentPowerAlgHom]
  have hscale := coordinatePairing_weight_smul (P := P) he he' hP
    (laurentCocharacterPoint A ζ) (laurentCocharacterPoint_value hζ)
    (laurentCocharacterPoint_value hζ2)
    (fun j => laurentCAlgHom (k := k) A (x j)) (fun j => laurentCAlgHom (k := k) A (y j))
  rw [coordinatePairing_naturality he.1 he'.1] at hscale
  have hnat := coordinatePairing_naturality (P := P) he.1 he'.1 φ X' Y'
  rw [hX, hY, hscale] at hnat
  have hQ (l : Fin m) :
      Q l = Polynomial.X ^ 2 * Polynomial.C (coordinatePairing e e' P x y l) := by
    apply laurentPowerAlgHom_injective (k := k) A hD
    have hl := congrFun hnat l
    simp only [Pi.smul_apply, smul_eq_mul] at hl
    change φ (Q l) = _
    rw [← hl]
    simp only [laurentPowerAlgHom, map_mul, map_pow, Polynomial.aevalTower_X,
      Polynomial.aevalTower_C, LaurentPolynomial.T_pow]
    push_cast
    ring_nf
  let g : A[X] →ₐ[k] A := Polynomial.aevalTower (AlgHom.id k A) r
  have hgX : (fun j => g (X' j)) = r • x := by
    funext j
    simp only [X', g, map_mul, Polynomial.aevalTower_X, Polynomial.aevalTower_C,
      AlgHom.id_apply, Pi.smul_apply, smul_eq_mul]
  have hgY : (fun j => g (Y' j)) = r • y := by
    funext j
    simp only [Y', g, map_mul, Polynomial.aevalTower_X, Polynomial.aevalTower_C,
      AlgHom.id_apply, Pi.smul_apply, smul_eq_mul]
  have hev := coordinatePairing_naturality (P := P) he.1 he'.1 g X' Y'
  rw [hgX, hgY] at hev
  rw [hev]
  funext l
  change g (Q l) = r ^ 2 * coordinatePairing e e' P x y l
  rw [hQ]
  simp only [g, map_mul, map_pow, Polynomial.aevalTower_X, Polynomial.aevalTower_C,
    AlgHom.id_apply]

/-- The substitution `X ↦ t` is the inclusion of polynomials into Laurent polynomials. -/
theorem laurentPowerAlgHom_one_apply {A : Type u} [CommRing A] [Algebra k A] (p : A[X]) :
    laurentPowerAlgHom (k := k) A 1 p = Polynomial.toLaurent p := by
  have h : (laurentPowerAlgHom (k := k) A 1 : A[X] →+* A[T;T⁻¹]) = Polynomial.toLaurent := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [laurentPowerAlgHom, Polynomial.toLaurent_C]
    · simp [laurentPowerAlgHom, Polynomial.toLaurent_X]
  exact RingHom.congr_fun h p

/-- The substitution `X ↦ t⁻¹` is the inclusion of polynomials followed by `t ↦ t⁻¹`. -/
theorem aevalTower_laurentCAlgHom_T_neg_one {A : Type u} [CommRing A] [Algebra k A]
    (p : A[X]) :
    Polynomial.aevalTower (laurentCAlgHom (k := k) A) (LaurentPolynomial.T (-1)) p =
      LaurentPolynomial.invert (Polynomial.toLaurent p) := by
  have h : (Polynomial.aevalTower (laurentCAlgHom (k := k) A) (LaurentPolynomial.T (-1)) :
      A[X] →+* A[T;T⁻¹]) =
      ((LaurentPolynomial.invert (R := A) : A[T;T⁻¹] →ₐ[A] A[T;T⁻¹]) :
        A[T;T⁻¹] →+* A[T;T⁻¹]).comp Polynomial.toLaurent := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [Polynomial.toLaurent_C]
    · simp [Polynomial.toLaurent_X]
  exact RingHom.congr_fun h p

/-- **Scalar linearity in each argument.** An equivariant pairing of weights `χ` and `2 • χ`,
with `χ ≠ 0`, that is trivial when either argument is the identity, is linear over the
coefficient algebra in each argument separately, in coordinates. -/
theorem coordinatePairing_smul (hS : IsSplitTorus S.toGrp) (hχ : χ ≠ 0)
    (he : IsWeightVectorCoordinates c χ e) (he' : IsWeightVectorCoordinates c' (2 • χ) e')
    (hP : ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (x y : T ⟶ V.X),
      lift (c.act s x) (c.act s y) ≫ P = c'.act s (lift x y ≫ P))
    (h1 : ∀ (T : Over (Spec (CommRingCat.of k))) (y : T ⟶ V.X), lift 1 y ≫ P = 1)
    (h1' : ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ V.X), lift x 1 ≫ P = 1)
    {A : Type u} [CommRing A] [Algebra k A] (r : A) (x y : Fin d → A) :
    coordinatePairing e e' P (r • x) y = r • coordinatePairing e e' P x y ∧
      coordinatePairing e e' P x (r • y) = r • coordinatePairing e e' P x y := by
  obtain ⟨X', hX'⟩ : ∃ X' : Fin d → A[X], X' = fun j => Polynomial.X * Polynomial.C (x j) :=
    ⟨_, rfl⟩
  obtain ⟨Y', hY'⟩ : ∃ Y' : Fin d → A[X], Y' = fun j => Polynomial.X * Polynomial.C (y j) :=
    ⟨_, rfl⟩
  obtain ⟨Cx, hCx⟩ : ∃ Cx : Fin d → A[X], Cx = fun j => Polynomial.C (x j) := ⟨_, rfl⟩
  obtain ⟨Cy, hCy⟩ : ∃ Cy : Fin d → A[X], Cy = fun j => Polynomial.C (y j) := ⟨_, rfl⟩
  -- the pairings `G = P(X x, y)` and `K = P(x, X y)` over `A[X]`
  obtain ⟨G, hG⟩ : ∃ G, G = coordinatePairing e e' P X' Cy := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, K = coordinatePairing e e' P Cx Y' := ⟨_, rfl⟩
  let ev (a : A) : A[X] →ₐ[k] A := Polynomial.aevalTower (AlgHom.id k A) a
  have hev (a : A) : (fun j => ev a (X' j)) = a • x ∧ (fun j => ev a (Y' j)) = a • y ∧
      (fun j => ev a (Cx j)) = x ∧ (fun j => ev a (Cy j)) = y := by
    subst hX' hY' hCx hCy
    refine ⟨?_, ?_, ?_, ?_⟩ <;> funext j <;>
      simp only [ev, map_mul, Polynomial.aevalTower_X, Polynomial.aevalTower_C, AlgHom.id_apply,
        Pi.smul_apply, smul_eq_mul]
  have hevG (a : A) : coordinatePairing e e' P (a • x) y = fun l => ev a (G l) := by
    have h := coordinatePairing_naturality (P := P) he.1 he'.1 (ev a) X' Cy
    rw [(hev a).1, (hev a).2.2.2] at h
    rw [h, hG]
  have hevK (a : A) : coordinatePairing e e' P x (a • y) = fun l => ev a (K l) := by
    have h := coordinatePairing_naturality (P := P) he.1 he'.1 (ev a) Cx Y'
    rw [(hev a).2.2.1, (hev a).2.1] at h
    rw [h, hK]
  have hev0 (p : A[X]) : ev 0 p = p.coeff 0 := by
    have h : (ev 0 : A[X] →+* A) = Polynomial.constantCoeff := by
      apply Polynomial.ringHom_ext
      · intro a
        simp [ev]
      · simp [ev]
    exact RingHom.congr_fun h p
  have hG0 (l : Fin m) : (G l).coeff 0 = 0 := by
    have h := congrFun (hevG 0) l
    rw [zero_smul, coordinatePairing_zero_left h1] at h
    rw [← hev0]
    exact h.symm
  have hK0 (l : Fin m) : (K l).coeff 0 = 0 := by
    have h := congrFun (hevK 0) l
    rw [zero_smul, coordinatePairing_zero_right h1'] at h
    rw [← hev0]
    exact h.symm
  -- the Laurent relation `G(t) = t ^ 2 K(t⁻¹)`, from homogeneity at the scalar `t`
  have hrel (l : Fin m) : Polynomial.toLaurent (G l) =
      LaurentPolynomial.T 2 * LaurentPolynomial.invert (Polynomial.toLaurent (K l)) := by
    let Lx : Fin d → A[T;T⁻¹] := fun j => laurentCAlgHom (k := k) A (x j)
    let Ly : Fin d → A[T;T⁻¹] := fun j => laurentCAlgHom (k := k) A (y j)
    let ψ := laurentPowerAlgHom (k := k) A 1
    let ρ : A[X] →ₐ[k] A[T;T⁻¹] :=
      Polynomial.aevalTower (laurentCAlgHom (k := k) A) (LaurentPolynomial.T (-1))
    have hψX : (fun j => ψ (X' j)) = (LaurentPolynomial.T 1 : A[T;T⁻¹]) • Lx := by
      subst hX'
      funext j
      simp [ψ, Lx, laurentPowerAlgHom]
    have hψC : (fun j => ψ (Cy j)) = Ly := by
      subst hCy
      funext j
      simp [ψ, Ly, laurentPowerAlgHom]
    have hρC : (fun j => ρ (Cx j)) = Lx := by
      subst hCx
      funext j
      simp [ρ, Lx]
    have hρY : (fun j => ρ (Y' j)) = (LaurentPolynomial.T (-1) : A[T;T⁻¹]) • Ly := by
      subst hY'
      funext j
      simp [ρ, Ly]
    have hψ := coordinatePairing_naturality (P := P) he.1 he'.1 ψ X' Cy
    rw [hψX, hψC, ← hG] at hψ
    have hρ := coordinatePairing_naturality (P := P) he.1 he'.1 ρ Cx Y'
    rw [hρC, hρY, ← hK] at hρ
    have hTT : (LaurentPolynomial.T 1 : A[T;T⁻¹]) • (LaurentPolynomial.T (-1) : A[T;T⁻¹]) • Ly =
        Ly := by
      rw [smul_smul, ← LaurentPolynomial.T_add]
      norm_num [LaurentPolynomial.T_zero]
    have hom := coordinatePairing_smul_smul hS hχ he he' hP (LaurentPolynomial.T 1 : A[T;T⁻¹])
      Lx ((LaurentPolynomial.T (-1) : A[T;T⁻¹]) • Ly)
    rw [hTT, hψ, hρ] at hom
    have h := congrFun hom l
    simp only [Pi.smul_apply, smul_eq_mul] at h
    rw [← laurentPowerAlgHom_one_apply (k := k), ← aevalTower_laurentCAlgHom_T_neg_one (k := k)]
    refine h.trans ?_
    change LaurentPolynomial.T 1 ^ 2 * ρ (K l) = LaurentPolynomial.T 2 * ρ (K l)
    rw [LaurentPolynomial.T_pow]
    norm_num
  have hGK (l : Fin m) := eq_C_mul_X_of_toLaurent_eq_T_two_mul_invert (hrel l) (hG0 l) (hK0 l)
  have hval (a : A) (l : Fin m) :
      ev a (G l) = (G l).coeff 1 * a ∧ ev a (K l) = (G l).coeff 1 * a := by
    constructor
    · conv_lhs => rw [(hGK l).1]
      simp only [ev, map_mul, Polynomial.aevalTower_X, Polynomial.aevalTower_C, AlgHom.id_apply]
    · conv_lhs => rw [(hGK l).2]
      simp only [ev, map_mul, Polynomial.aevalTower_X, Polynomial.aevalTower_C, AlgHom.id_apply]
  have h1x : coordinatePairing e e' P x y = fun l => (G l).coeff 1 := by
    have h := hevG 1
    rw [one_smul] at h
    rw [h]
    funext l
    rw [(hval 1 l).1, mul_one]
  refine ⟨?_, ?_⟩
  · rw [hevG r, h1x]
    funext l
    rw [(hval r l).1]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · rw [hevK r, h1x]
    funext l
    rw [(hval r l).2]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

/-- The coordinates of the pairing on scheme tests are the coordinate pairing over the ring of
global functions. -/
theorem coordinatePairing_global (he : IsNaturalVectorCoordinates e)
    (he' : IsNaturalVectorCoordinates e') (T : Over (Spec (CommRingCat.of k)))
    (x y : T ⟶ V.X) :
    (e' T (lift x y ≫ P)).toAdd =
      coordinatePairing (A := ((algΓ (CommRingCat.of k)).obj T).unop) e e' P
        (e T x).toAdd (e T y).toAdd := by
  let A := ((algΓ (CommRingCat.of k)).obj T).unop
  let a := (algΓAlgSpecAdjunction (CommRingCat.of k)).unit.app T
  have hu (z : T ⟶ V.X) :
      a ≫ (vectorAffineCoordinates e A).symm (Multiplicative.ofAdd (e T z).toAdd) = z := by
    apply (e T).injective
    apply Multiplicative.toAdd.injective
    rw [← he.vectorAffineCoordinates_unit_comp]
    exact congrArg Multiplicative.toAdd ((vectorAffineCoordinates e A).apply_symm_apply _)
  dsimp only [coordinatePairing]
  rw [he'.vectorAffineCoordinates_unit_comp, ← Category.assoc, comp_lift, hu x, hu y]

/-- **Bilinearity.** A pairing of vector groups, multiplicative in each argument, that
intertwines a split-torus action of nonzero weight `χ` with one of weight `2 • χ`, is bilinear
over every test scheme's ring of global functions in weight vector coordinates. -/
theorem isBilinearVectorPairing_of_equivariant (hS : IsSplitTorus S.toGrp) (hχ : χ ≠ 0)
    (he : IsWeightVectorCoordinates c χ e) (he' : IsWeightVectorCoordinates c' (2 • χ) e')
    (hmul_left : ∀ (T : Over (Spec (CommRingCat.of k))) (x x' y : T ⟶ V.X),
      lift (x * x') y ≫ P = (lift x y ≫ P) * (lift x' y ≫ P))
    (hmul_right : ∀ (T : Over (Spec (CommRingCat.of k))) (x y y' : T ⟶ V.X),
      lift x (y * y') ≫ P = (lift x y ≫ P) * (lift x y' ≫ P))
    (hP : ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (x y : T ⟶ V.X),
      lift (c.act s x) (c.act s y) ≫ P = c'.act s (lift x y ≫ P)) :
    IsBilinearVectorPairing e e' P := by
  have h1 (T : Over (Spec (CommRingCat.of k))) (y : T ⟶ V.X) : lift 1 y ≫ P = 1 := by
    have h := hmul_left T 1 1 y
    rw [mul_one] at h
    exact (mul_left_cancel (a := lift 1 y ≫ P) ((mul_one _).trans h)).symm
  have h1' (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ V.X) : lift x 1 ≫ P = 1 := by
    have h := hmul_right T x 1 1
    rw [mul_one] at h
    exact (mul_left_cancel (a := lift x 1 ≫ P) ((mul_one _).trans h)).symm
  intro T x x' y y' r
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hmul_left, map_mul, toAdd_mul]
  · rw [hmul_right, map_mul, toAdd_mul]
  · rw [coordinatePairing_global he.1 he'.1, coordinatePairing_global he.1 he'.1,
      MulEquiv.apply_symm_apply, toAdd_ofAdd]
    exact (coordinatePairing_smul (A := ((algΓ (CommRingCat.of k)).obj T).unop) hS hχ he he' hP
      h1 h1' r _ _).1
  · rw [coordinatePairing_global he.1 he'.1, coordinatePairing_global he.1 he'.1,
      MulEquiv.apply_symm_apply, toAdd_ofAdd]
    exact (coordinatePairing_smul (A := ((algΓ (CommRingCat.of k)).obj T).unop) hS hχ he he' hP
      h1 h1' r _ _).2

end Coordinates

end Langlands.GroupScheme.RelativeRoot
