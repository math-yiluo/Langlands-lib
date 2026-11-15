import Langlands.GroupScheme.Reductive.LocalSplitCommutatorLaws

/-! # Universal commutator polynomials of positive cell factors -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace LocalSplitCell

section ScaleAlgebra

variable {R : Type*} [CommRing R]

/-- The substitution `S ↦ U ^ a * S` on `R[S]`, with coefficients in `R[U, U⁻¹]`. -/
def scaleS (a : ℤ) : Polynomial R →+* Polynomial (LaurentPolynomial R) :=
  Polynomial.eval₂RingHom (Polynomial.C.comp LaurentPolynomial.C)
    (Polynomial.C (LaurentPolynomial.T a) * Polynomial.X)

/-- The substitution `S ↦ U ^ a * S`, `T ↦ U ^ b * T` on `R[S][T]`, with coefficients in
`R[U, U⁻¹]`. Here `R[S][T]` is `Polynomial (Polynomial R)`, with `S = C X` and `T = X`. -/
def scaleST (a b : ℤ) :
    Polynomial (Polynomial R) →+* Polynomial (Polynomial (LaurentPolynomial R)) :=
  Polynomial.eval₂RingHom (Polynomial.C.comp (scaleS (R := R) a))
    (Polynomial.C (R := Polynomial (LaurentPolynomial R))
      (Polynomial.C (LaurentPolynomial.T b)) * Polynomial.X)

/-- The inclusion `R[S][T] → R[U, U⁻¹][S][T]`. -/
def laurentST : Polynomial (Polynomial R) →+* Polynomial (Polynomial (LaurentPolynomial R)) :=
  Polynomial.mapRingHom (Polynomial.mapRingHom LaurentPolynomial.C)

theorem scaleS_monomial (a : ℤ) (i : ℕ) (r : R) :
    scaleS a (Polynomial.monomial i r) =
      Polynomial.monomial i (LaurentPolynomial.C r * LaurentPolynomial.T (i * a)) := by
  rw [scaleS, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial, RingHom.comp_apply,
    mul_pow, ← Polynomial.C_pow, LaurentPolynomial.T_pow, ← mul_assoc, ← Polynomial.C_mul,
    Polynomial.C_mul_X_pow_eq_monomial]

theorem scaleST_monomial (a b : ℤ) (i j : ℕ) (r : R) :
    scaleST a b (Polynomial.monomial j (Polynomial.monomial i r)) =
      Polynomial.monomial j (Polynomial.monomial i
        (LaurentPolynomial.C r * LaurentPolynomial.T (i * a + j * b))) := by
  rw [scaleST, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial, RingHom.comp_apply,
    scaleS_monomial]
  rw [mul_pow (M := Polynomial (Polynomial (LaurentPolynomial R))), ← Polynomial.C_pow,
    ← Polynomial.C_pow, LaurentPolynomial.T_pow, ← mul_assoc, ← Polynomial.C_mul,
    Polynomial.C_mul_X_pow_eq_monomial, Polynomial.monomial_mul_C, mul_assoc,
    ← LaurentPolynomial.T_add]

/-- Coefficients of `E(U ^ a * S, U ^ b * T)`: the coefficient of `S ^ i T ^ j` is
`U ^ (a i + b j)` times that of `E`. -/
theorem coeff_coeff_scaleST (a b : ℤ) (E : Polynomial (Polynomial R)) (i j : ℕ) :
    ((scaleST a b E).coeff j).coeff i =
      LaurentPolynomial.C ((E.coeff j).coeff i) * LaurentPolynomial.T (i * a + j * b) := by
  induction E using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, Polynomial.coeff_add, Polynomial.coeff_add, hp, hq,
      Polynomial.coeff_add, Polynomial.coeff_add, map_add, add_mul]
  | monomial j0 q =>
    induction q using Polynomial.induction_on' with
    | add p q hp hq =>
      rw [map_add (Polynomial.monomial j0), map_add, Polynomial.coeff_add, Polynomial.coeff_add,
        hp, hq, Polynomial.coeff_add, Polynomial.coeff_add, map_add, add_mul]
    | monomial i0 r =>
      rw [scaleST_monomial, Polynomial.coeff_monomial, Polynomial.coeff_monomial]
      by_cases hj : j0 = j
      · subst hj
        rw [ite_eq_left_of_eq_true _ _ (eq_self j0), ite_eq_left_of_eq_true _ _ (eq_self j0),
          Polynomial.coeff_monomial, Polynomial.coeff_monomial]
        by_cases hi : i0 = i
        · subst hi
          rw [ite_eq_left_of_eq_true _ _ (eq_self i0), ite_eq_left_of_eq_true _ _ (eq_self i0)]
        · rw [ite_eq_right_of_eq_false _ _ (eq_false hi),
            ite_eq_right_of_eq_false _ _ (eq_false hi), map_zero, zero_mul]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hj), ite_eq_right_of_eq_false _ _ (eq_false hj),
          Polynomial.coeff_zero, Polynomial.coeff_zero, map_zero, zero_mul]

theorem coeff_coeff_laurentST (E : Polynomial (Polynomial R)) (i j : ℕ) :
    ((laurentST E).coeff j).coeff i = LaurentPolynomial.C ((E.coeff j).coeff i) := by
  rw [laurentST, Polynomial.coe_mapRingHom, Polynomial.coeff_map, Polynomial.coe_mapRingHom,
    Polynomial.coeff_map]

theorem scaleST_comp_C_C (a b : ℤ) :
    (scaleST (R := R) a b).comp (Polynomial.C.comp Polynomial.C) =
      (laurentST (R := R)).comp (Polynomial.C.comp Polynomial.C) := by
  ext r
  simp only [RingHom.comp_apply, scaleST, scaleS, laurentST, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_C, Polynomial.coe_mapRingHom, Polynomial.map_C]

theorem scaleST_C_X (a b : ℤ) :
    scaleST (R := R) a b (Polynomial.C Polynomial.X) =
      Polynomial.C (Polynomial.C (LaurentPolynomial.T a)) *
        laurentST (Polynomial.C Polynomial.X) := by
  simp only [scaleST, scaleS, laurentST, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
    Polynomial.eval₂_X, RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C,
    Polynomial.map_X, Polynomial.C_mul]

theorem scaleST_X (a b : ℤ) :
    scaleST (R := R) a b Polynomial.X =
      Polynomial.C (Polynomial.C (LaurentPolynomial.T b)) * laurentST Polynomial.X := by
  simp only [scaleST, laurentST, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
    Polynomial.coe_mapRingHom, Polynomial.map_X]

theorem val_zpow_isUnit_T (z : ℤ) :
    ((((LaurentPolynomial.isUnit_T (R := R) 1).unit ^ z : (LaurentPolynomial R)ˣ)) :
      LaurentPolynomial R) = LaurentPolynomial.T z := by
  have hU : (((LaurentPolynomial.isUnit_T (R := R) 1).unit : (LaurentPolynomial R)ˣ) :
      LaurentPolynomial R) = LaurentPolynomial.T 1 := IsUnit.unit_spec _
  have hinv : ((((LaurentPolynomial.isUnit_T (R := R) 1).unit : (LaurentPolynomial R)ˣ)⁻¹ :
      (LaurentPolynomial R)ˣ) : LaurentPolynomial R) = LaurentPolynomial.T (-1) :=
    Units.inv_eq_of_mul_eq_one_right (by
      rw [hU, ← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero])
  induction z using Int.induction_on with
  | zero => rw [zpow_zero, Units.val_one, LaurentPolynomial.T_zero]
  | succ k ih => rw [zpow_add_one, Units.val_mul, ih, hU, ← LaurentPolynomial.T_add]
  | pred k ih =>
    rw [zpow_sub_one, Units.val_mul, ih, hinv, ← LaurentPolynomial.T_add, sub_eq_add_neg]

/-- **Weights from a scaling identity.** If `E(U ^ a S, U ^ b T) = U ^ c E(S, T)`, then every
monomial `S ^ i T ^ j` occurring in `E` has weight `i a + j b = c`. -/
theorem weight_eq_of_scaleST_eq {a b c : ℤ} {E : Polynomial (Polynomial R)}
    (h : scaleST a b E = Polynomial.C (Polynomial.C (LaurentPolynomial.T c)) * laurentST E)
    {i j : ℕ} (hij : (E.coeff j).coeff i ≠ 0) : i * a + j * b = c := by
  have h1 := congrArg (fun F => (F.coeff j).coeff i) h
  simp only [coeff_coeff_scaleST, Polynomial.coeff_C_mul, coeff_coeff_laurentST] at h1
  rw [LaurentPolynomial.T_mul, ← LaurentPolynomial.single_eq_C_mul_T,
    ← LaurentPolynomial.single_eq_C_mul_T] at h1
  exact (AddMonoidAlgebra.single_left_inj hij).mp h1

end ScaleAlgebra

section Universal

open Polynomial

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] {J : Type u}
  {G : GroupScheme (Spec (CommRingCat.of R))}
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G} {ch : J → I → ℤ} {u : J → (Ga R ⟶ G)}
  {m n : ℕ} {neg : Fin m → J} {pos : Fin n → J}

/-- The structure map of the two-variable line `Spec R[S][T] → Spec R`. -/
def lineBase (R : Type u) [CommRing R] :
    Spec (CommRingCat.of (Polynomial (Polynomial R))) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (Polynomial.C.comp Polynomial.C))

/-- `E` consists of universal commutator coordinates of the positive cell factors at positions
`k` and `l`: over the two-variable line `R[S][T]`, the commutator `posComm` of `u_k(S)` and
`u_l(T)` is the product of the positive cell factors with coordinates `E`. Here `R[S][T]` is
`Polynomial (Polynomial R)`, with `S = C X` and `T = X`. -/
def IsUnivComm (u : J → (Ga R ⟶ G)) (pos : Fin n → J) (k l : Fin n)
    (E : Fin n → Polynomial (Polynomial R)) : Prop :=
  posComm u pos (Over.mk (lineBase R)) k l
      ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial (Polynomial R)))).inv (C X))
      ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial (Polynomial R)))).inv X) =
    orderedProduct u pos (Over.mk (lineBase R))
      (fun q => (Scheme.ΓSpecIso (CommRingCat.of (Polynomial (Polynomial R)))).inv (E q))

theorem specMap_ofHom_comp {L L' L'' : Type u} [CommRing L] [CommRing L'] [CommRing L'']
    (κ : L' →+* L'') (φ : L →+* L') :
    Spec.map (CommRingCat.ofHom κ) ≫ Spec.map (CommRingCat.ofHom φ) =
      Spec.map (CommRingCat.ofHom (κ.comp φ)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

/-- Universal commutator coordinates exist. -/
theorem exists_isUnivComm [IsOpenImmersion (cellMap i u neg pos).left]
    (hu : TorusEquivariant i ch u) (ν : I → ℤ) (hneg : ∀ k, coPairing (ch (neg k)) ν < 0)
    (hpos : ∀ k, 0 < coPairing (ch (pos k)) ν) (k l : Fin n) :
    ∃ E : Fin n → Polynomial (Polynomial R), IsUnivComm u pos k l E :=
  exists_posComm_eq_ring (neg := neg) hu ν hneg hpos (lineBase R) k l (C X) X

/-- Universal commutator coordinates are unique. -/
theorem IsUnivComm.unique [IsOpenImmersion (cellMap i u neg pos).left] {k l : Fin n}
    {E E' : Fin n → Polynomial (Polynomial R)} (hE : IsUnivComm u pos k l E)
    (hE' : IsUnivComm u pos k l E') : E = E' :=
  coord_eq_of_orderedProduct_eq (i := i) (neg := neg) _ (hE.symm.trans hE')

/-- Evaluation `R[S][T] → B` at `S = x`, `T = y`, over the ring map corresponding to
`s : Spec B ⟶ Spec R`. -/
def lineEval {B : Type u} [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
    (x y : B) : Polynomial (Polynomial R) →+* B :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (Spec.preimage s).hom x) y

theorem lineEval_C_X {B : Type u} [CommRing B]
    (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R)) (x y : B) :
    lineEval s x y (C X) = x := by
  simp [lineEval]

theorem lineEval_X {B : Type u} [CommRing B]
    (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R)) (x y : B) :
    lineEval s x y X = y := by
  simp [lineEval]

theorem specMap_lineEval {B : Type u} [CommRing B]
    (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R)) (x y : B) :
    Spec.map (CommRingCat.ofHom (lineEval s x y)) ≫ lineBase R = s := by
  have h : (lineEval s x y).comp (Polynomial.C.comp Polynomial.C) = (Spec.preimage s).hom := by
    ext r
    simp [lineEval]
  rw [lineBase, specMap_ofHom_comp, h, CommRingCat.ofHom_hom, Spec.map_preimage]

/-- **Specialization.** Universal commutator coordinates specialize to the commutator
coordinates over every ring. -/
theorem IsUnivComm.posComm_eq {k l : Fin n} {E : Fin n → Polynomial (Polynomial R)}
    (hE : IsUnivComm u pos k l E) {B : Type u} [CommRing B]
    (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R)) (x y : B) :
    posComm u pos (Over.mk s) k l ((Scheme.ΓSpecIso (CommRingCat.of B)).inv x)
        ((Scheme.ΓSpecIso (CommRingCat.of B)).inv y) =
      orderedProduct u pos (Over.mk s)
        (fun q => (Scheme.ΓSpecIso (CommRingCat.of B)).inv (lineEval s x y (E q))) := by
  have h := posComm_specHom (lineEval s x y) (specMap_lineEval s x y) k l _ _ E hE
  rw [lineEval_C_X, lineEval_X] at h
  exact h

/-- The universal commutator identity mapped along any ring map out of `R[S][T]`. -/
theorem IsUnivComm.posComm_map {k l : Fin n} {E : Fin n → Polynomial (Polynomial R)}
    (hE : IsUnivComm u pos k l E) {L : Type u} [CommRing L] (κ : Polynomial (Polynomial R) →+* L) :
    posComm u pos (Over.mk (Spec.map (CommRingCat.ofHom κ) ≫ lineBase R)) k l
        ((Scheme.ΓSpecIso (CommRingCat.of L)).inv (κ (C X)))
        ((Scheme.ΓSpecIso (CommRingCat.of L)).inv (κ X)) =
      orderedProduct u pos (Over.mk (Spec.map (CommRingCat.ofHom κ) ≫ lineBase R))
        (fun q => (Scheme.ΓSpecIso (CommRingCat.of L)).inv (κ (E q))) :=
  posComm_specHom κ rfl k l (C X) X E hE

/-- **Transfer.** If `E` gives universal commutator coordinates both for the family `u` of `G`
and for the family `u'` of `H`, then every commutator relation of `G` at positions `k`, `l`
over a ring holds in `H` with the same coordinates. -/
theorem posComm_transfer_of_isUnivComm [IsOpenImmersion (cellMap i u neg pos).left]
    {H : GroupScheme (Spec (CommRingCat.of R))} {u' : J → (Ga R ⟶ H)} {k l : Fin n}
    {E : Fin n → Polynomial (Polynomial R)} (hE : IsUnivComm u pos k l E)
    (hE' : IsUnivComm u' pos k l E) {B : Type u} [CommRing B]
    (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
    (x y : Γ((Over.mk s).left, ⊤)) (e : Fin n → Γ((Over.mk s).left, ⊤))
    (he : posComm u pos (Over.mk s) k l x y = orderedProduct u pos (Over.mk s) e) :
    posComm u' pos (Over.mk s) k l x y = orderedProduct u' pos (Over.mk s) e := by
  obtain ⟨x0, rfl⟩ : ∃ x0 : B,
      ((Scheme.ΓSpecIso (CommRingCat.of B)).inv x0 : Γ((Over.mk s).left, ⊤)) = x :=
    ⟨_, Iso.hom_inv_id_apply _ _⟩
  obtain ⟨y0, rfl⟩ : ∃ y0 : B,
      ((Scheme.ΓSpecIso (CommRingCat.of B)).inv y0 : Γ((Over.mk s).left, ⊤)) = y :=
    ⟨_, Iso.hom_inv_id_apply _ _⟩
  have h1 := hE.posComm_eq s x0 y0
  rw [he] at h1
  have h2 := orderedProduct_pos_injective (i := i) (neg := neg) _ h1
  rw [h2]
  exact hE'.posComm_eq s x0 y0

/-- Universal commutator coordinates vanish at `T = 0`. -/
theorem IsUnivComm.eval_zero [IsOpenImmersion (cellMap i u neg pos).left] {k l : Fin n}
    {E : Fin n → Polynomial (Polynomial R)} (hE : IsUnivComm u pos k l E) (p : Fin n) :
    Polynomial.eval 0 (E p) = 0 := by
  have H := posComm_specHom (Polynomial.evalRingHom (0 : Polynomial R)) (s := lineBase R) rfl
    k l _ _ E hE
  have hb : Polynomial.evalRingHom (0 : Polynomial R) (X : Polynomial (Polynomial R)) = 0 := by
    simp
  rw [hb, map_zero, posComm_zero_right] at H
  have H0 : orderedProduct u pos (Over.mk (Spec.map (CommRingCat.ofHom
      (Polynomial.evalRingHom (0 : Polynomial R))) ≫ lineBase R))
      (fun q => (Scheme.ΓSpecIso (CommRingCat.of (Polynomial R))).inv
        ((0 : Fin n → Polynomial R) q)) = 1 := by
    simp only [Pi.zero_apply, map_zero]
    exact orderedProduct_zero u pos _
  have := coord_eq_of_orderedProduct_eq (i := i) (neg := neg) _ (H0.trans H)
  exact (congrFun this p).symm

/-- Universal commutator coordinates vanish at `S = 0`. -/
theorem IsUnivComm.map_eval_zero [IsOpenImmersion (cellMap i u neg pos).left] {k l : Fin n}
    {E : Fin n → Polynomial (Polynomial R)} (hE : IsUnivComm u pos k l E) (p : Fin n) :
    Polynomial.map (Polynomial.evalRingHom (0 : R)) (E p) = 0 := by
  have H := posComm_specHom (Polynomial.mapRingHom (Polynomial.evalRingHom (0 : R)))
    (s := lineBase R) rfl k l _ _ E hE
  have hb : Polynomial.mapRingHom (Polynomial.evalRingHom (0 : R))
      (C X : Polynomial (Polynomial R)) = 0 := by
    simp
  rw [hb, map_zero, posComm_zero_left] at H
  have H0 : orderedProduct u pos (Over.mk (Spec.map (CommRingCat.ofHom
      (Polynomial.mapRingHom (Polynomial.evalRingHom (0 : R)))) ≫ lineBase R))
      (fun q => (Scheme.ΓSpecIso (CommRingCat.of (Polynomial R))).inv
        ((0 : Fin n → Polynomial R) q)) = 1 := by
    simp only [Pi.zero_apply, map_zero]
    exact orderedProduct_zero u pos _
  have := coord_eq_of_orderedProduct_eq (i := i) (neg := neg) _ (H0.trans H)
  exact (congrFun this p).symm

/-- Universal commutator coordinates only involve monomials `S ^ dS T ^ dT` with `dS ≥ 1` and
`dT ≥ 1`. -/
theorem IsUnivComm.one_le [IsOpenImmersion (cellMap i u neg pos).left] {k l : Fin n}
    {E : Fin n → Polynomial (Polynomial R)} (hE : IsUnivComm u pos k l E) (p : Fin n)
    {dS dT : ℕ} (h : ((E p).coeff dT).coeff dS ≠ 0) : 1 ≤ dS ∧ 1 ≤ dT := by
  constructor
  · rw [Nat.one_le_iff_ne_zero]
    rintro rfl
    apply h
    have h1 := congrArg (fun F => F.coeff dT)
      (IsUnivComm.map_eval_zero (i := i) (neg := neg) hE p)
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero, Polynomial.coe_evalRingHom] at h1
    rw [Polynomial.coeff_zero_eq_eval_zero]
    exact h1
  · rw [Nat.one_le_iff_ne_zero]
    rintro rfl
    apply h
    rw [Polynomial.coeff_zero_eq_eval_zero, IsUnivComm.eval_zero (i := i) (neg := neg) hE p,
      Polynomial.coeff_zero]

theorem val_units_map_zpow {M N : Type*} [Monoid M] [Monoid N] (f : M →* N) (U : Mˣ) (z : ℤ) :
    ((Units.map f U ^ z : Nˣ) : N) = f ((U ^ z : Mˣ) : M) := by
  rw [← map_zpow (Units.map f) U z, Units.coe_map]

/-- The value of an exponent character at the cocharacter point of the unit `U` of
`R[U, U⁻¹]`, mapped to a ring `L`. -/
theorem torusChar_cocharPoint_T {L : Type u} [CommRing L]
    (s : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of R)) (φ : LaurentPolynomial R →+* L)
    (χ ν : I → ℤ) :
    torusChar χ (Over.mk s) (cocharPoint ν (Over.mk s)
        (Units.map ((Scheme.ΓSpecIso (CommRingCat.of L)).inv.hom.comp φ).toMonoidHom
          (LaurentPolynomial.isUnit_T (R := R) 1).unit)) =
      (Scheme.ΓSpecIso (CommRingCat.of L)).inv (φ (LaurentPolynomial.T (coPairing χ ν))) := by
  rw [torusChar_cocharPoint, val_units_map_zpow, val_zpow_isUnit_T]
  rfl

/-- The structure map of the two-variable line over `R[U, U⁻¹]`. -/
def laurentLineBase (R : Type u) [CommRing R] :
    Spec (CommRingCat.of (Polynomial (Polynomial (LaurentPolynomial R)))) ⟶
      Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom ((laurentST (R := R)).comp (Polynomial.C.comp Polynomial.C)))

/-- The universal commutator identity specialized along `S ↦ U ^ a S`, `T ↦ U ^ b T`. -/
theorem IsUnivComm.posComm_scaleST {k l : Fin n} {E : Fin n → Polynomial (Polynomial R)}
    (hE : IsUnivComm u pos k l E) (a b : ℤ) :
    posComm u pos (Over.mk (laurentLineBase R)) k l
        ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial (Polynomial (LaurentPolynomial R))))).inv
          (C (C (LaurentPolynomial.T a)) * laurentST (C X)))
        ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial (Polynomial (LaurentPolynomial R))))).inv
          (C (C (LaurentPolynomial.T b)) * laurentST X)) =
      orderedProduct u pos (Over.mk (laurentLineBase R))
        (fun q => (Scheme.ΓSpecIso
            (CommRingCat.of (Polynomial (Polynomial (LaurentPolynomial R))))).inv
          (scaleST a b (E q))) := by
  have hsS : Spec.map (CommRingCat.ofHom (scaleST (R := R) a b)) ≫ lineBase R =
      laurentLineBase R := by
    rw [laurentLineBase, lineBase, specMap_ofHom_comp, scaleST_comp_C_C]
  have H2 := hE.posComm_map (L := Polynomial (Polynomial (LaurentPolynomial R)))
    (scaleST (R := R) a b)
  rw [hsS, scaleST_C_X, scaleST_X] at H2
  exact H2

/-- The universal commutator identity over `R[U, U⁻¹]`, conjugated by the torus point
`ν(U)`. -/
theorem IsUnivComm.posComm_laurent_conj (hu : TorusEquivariant i ch u) {k l : Fin n}
    {E : Fin n → Polynomial (Polynomial R)} (hE : IsUnivComm u pos k l E) (ν : I → ℤ) :
    posComm u pos (Over.mk (laurentLineBase R)) k l
        ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial (Polynomial (LaurentPolynomial R))))).inv
          (C (C (LaurentPolynomial.T (coPairing (ch (pos k)) ν))) * laurentST (C X)))
        ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial (Polynomial (LaurentPolynomial R))))).inv
          (C (C (LaurentPolynomial.T (coPairing (ch (pos l)) ν))) * laurentST X)) =
      orderedProduct u pos (Over.mk (laurentLineBase R))
        (fun q => (Scheme.ΓSpecIso
            (CommRingCat.of (Polynomial (Polynomial (LaurentPolynomial R))))).inv
          (C (C (LaurentPolynomial.T (coPairing (ch (pos q)) ν))) * laurentST (E q))) := by
  have hsL : Spec.map (CommRingCat.ofHom (laurentST (R := R))) ≫ lineBase R =
      laurentLineBase R := by
    rw [laurentLineBase, lineBase, specMap_ofHom_comp]
  have H1 := hE.posComm_map (L := Polynomial (Polynomial (LaurentPolynomial R)))
    (laurentST (R := R))
  rw [hsL] at H1
  obtain ⟨t, ht⟩ : ∃ t : Over.mk (laurentLineBase R) ⟶
      (splitTorus (Spec (CommRingCat.of R)) I).X,
      t = cocharPoint ν (Over.mk (laurentLineBase R))
        (Units.map ((Scheme.ΓSpecIso (CommRingCat.of
          (Polynomial (Polynomial (LaurentPolynomial R))))).inv.hom.comp
            (Polynomial.C.comp Polynomial.C)).toMonoidHom
          (LaurentPolynomial.isUnit_T (R := R) 1).unit) := ⟨_, rfl⟩
  have hχ : ∀ q : Fin n, torusChar (ch (pos q)) (Over.mk (laurentLineBase R)) t =
      (Scheme.ΓSpecIso (CommRingCat.of (Polynomial (Polynomial (LaurentPolynomial R))))).inv
        (C (C (LaurentPolynomial.T (coPairing (ch (pos q)) ν)))) := by
    intro q
    rw [ht]
    exact torusChar_cocharPoint_T (laurentLineBase R) (Polynomial.C.comp Polynomial.C) _ ν
  have hmul : ∀ a b : Polynomial (Polynomial (LaurentPolynomial R)),
      (((Scheme.ΓSpecIso (CommRingCat.of (Polynomial (Polynomial (LaurentPolynomial R))))).inv a :
          Γ((Over.mk (laurentLineBase R)).left, ⊤)) *
        (Scheme.ΓSpecIso (CommRingCat.of (Polynomial (Polynomial (LaurentPolynomial R))))).inv b) =
        (Scheme.ΓSpecIso (CommRingCat.of (Polynomial (Polynomial (LaurentPolynomial R))))).inv
          (a * b) :=
    fun a b => (map_mul _ a b).symm
  have Hc := congrArg (fun g => (t ≫ i.hom.hom) * g * (t ≫ i.hom.hom)⁻¹) H1
  simp only at Hc
  rw [torus_mul_posComm_mul_inv hu, torus_mul_orderedProduct_mul_inv hu, hχ k, hχ l, hmul,
    hmul] at Hc
  rw [Hc]
  congr 1
  funext q
  rw [hχ q, hmul]

/-- **Torus scaling of universal commutator coordinates.** For every cocharacter `ν`, with
`a`, `b`, `c` the pairings of `ν` with the characters at positions `k`, `l`, `p`:
`E_p(U ^ a S, U ^ b T) = U ^ c E_p(S, T)` in `R[U, U⁻¹][S][T]`. -/
theorem IsUnivComm.scaleST_eq [IsOpenImmersion (cellMap i u neg pos).left]
    (hu : TorusEquivariant i ch u) {k l : Fin n} {E : Fin n → Polynomial (Polynomial R)}
    (hE : IsUnivComm u pos k l E) (ν : I → ℤ) (p : Fin n) :
    scaleST (coPairing (ch (pos k)) ν) (coPairing (ch (pos l)) ν) (E p) =
      Polynomial.C (Polynomial.C (LaurentPolynomial.T (coPairing (ch (pos p)) ν))) *
        laurentST (E p) := by
  have h := (hE.posComm_laurent_conj hu ν).symm.trans (hE.posComm_scaleST _ _)
  have hinj := orderedProduct_pos_injective (i := i) (neg := neg) (u := u) (pos := pos) _ h
  have hp := congrArg (Scheme.ΓSpecIso
    (CommRingCat.of (Polynomial (Polynomial (LaurentPolynomial R))))).hom (congrFun hinj p)
  simp only at hp
  rw [Iso.inv_hom_id_apply, Iso.inv_hom_id_apply] at hp
  exact hp.symm

/-- **Multigrading of universal commutator coordinates.** Every monomial `S ^ dS T ^ dT`
occurring in the coordinate at position `p` satisfies
`dS • ch (pos k) + dT • ch (pos l) = ch (pos p)`. -/
theorem IsUnivComm.weight [IsOpenImmersion (cellMap i u neg pos).left]
    (hu : TorusEquivariant i ch u) {k l : Fin n} {E : Fin n → Polynomial (Polynomial R)}
    (hE : IsUnivComm u pos k l E) (p : Fin n) {dS dT : ℕ}
    (h : ((E p).coeff dT).coeff dS ≠ 0) :
    (dS : ℤ) • ch (pos k) + (dT : ℤ) • ch (pos l) = ch (pos p) := by
  classical
  funext t
  have hw := weight_eq_of_scaleST_eq
    (IsUnivComm.scaleST_eq (neg := neg) hu hE (Pi.single t 1) p) h
  have hc : ∀ χ : I → ℤ, coPairing χ (Pi.single t 1) = χ t := by
    intro χ
    simp [coPairing, Pi.single_apply]
  rw [hc, hc, hc] at hw
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [← hw]

/-- Universal coordinates vanish at every position that admits no weight relation. -/
theorem IsUnivComm.eq_zero_of_forall_ne [IsOpenImmersion (cellMap i u neg pos).left]
    (hu : TorusEquivariant i ch u) {k l : Fin n} {E : Fin n → Polynomial (Polynomial R)}
    (hE : IsUnivComm u pos k l E) (p : Fin n)
    (hp : ∀ dS dT : ℕ, 1 ≤ dS → 1 ≤ dT →
      (dS : ℤ) • ch (pos k) + (dT : ℤ) • ch (pos l) ≠ ch (pos p)) : E p = 0 := by
  ext dT dS
  rw [Polynomial.coeff_zero, Polynomial.coeff_zero]
  by_contra h
  obtain ⟨h1, h2⟩ := hE.one_le (i := i) (neg := neg) p h
  exact hp dS dT h1 h2 (hE.weight (neg := neg) hu p h)

/-- **Commuting factors.** If no position `p` has a character of the form
`dS • ch (pos k) + dT • ch (pos l)` with `dS, dT ≥ 1`, then the positive cell factors at
positions `k` and `l` commute over every ring. -/
theorem posComm_eq_one_of_forall_ne [IsOpenImmersion (cellMap i u neg pos).left]
    (hu : TorusEquivariant i ch u) (ν : I → ℤ) (hneg : ∀ k, coPairing (ch (neg k)) ν < 0)
    (hpos : ∀ k, 0 < coPairing (ch (pos k)) ν) {k l : Fin n}
    (h : ∀ (p : Fin n) (dS dT : ℕ), 1 ≤ dS → 1 ≤ dT →
      (dS : ℤ) • ch (pos k) + (dT : ℤ) • ch (pos l) ≠ ch (pos p))
    {B : Type u} [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
    (x y : Γ((Over.mk s).left, ⊤)) : posComm u pos (Over.mk s) k l x y = 1 := by
  obtain ⟨E, hE⟩ := exists_isUnivComm (i := i) (neg := neg) hu ν hneg hpos k l
  obtain ⟨x0, rfl⟩ : ∃ x0 : B,
      ((Scheme.ΓSpecIso (CommRingCat.of B)).inv x0 : Γ((Over.mk s).left, ⊤)) = x :=
    ⟨_, Iso.hom_inv_id_apply _ _⟩
  obtain ⟨y0, rfl⟩ : ∃ y0 : B,
      ((Scheme.ΓSpecIso (CommRingCat.of B)).inv y0 : Γ((Over.mk s).left, ⊤)) = y :=
    ⟨_, Iso.hom_inv_id_apply _ _⟩
  rw [hE.posComm_eq s x0 y0]
  have hz : ∀ q, E q = 0 := fun q => hE.eq_zero_of_forall_ne (neg := neg) hu q (h q)
  simp only [hz, map_zero]
  exact orderedProduct_zero u pos _

end Universal

section WeylFamilies

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] [DecidableEq I] {J : Type u}
  {G H : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G} {P : RootDatum J (I → ℤ) (I → ℤ)}

/-- **Commutator relations from shared universal coordinates.** If, for every pair of
positions `k < l`, the Weyl families of `G` and `H` have the same universal commutator
coordinates, then the commutator relations of the positive cell factors transfer from `G` to
`H`. -/
theorem commutatorRelations_of_isUnivComm (hG : IsReductive G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hP : IsFibrewiseRootDatumOf I G i P) {b : P.Base} (W : ∀ α, SimpleWord P b α)
    {u : J → (Ga R ⟶ G)} {u' : J → (Ga R ⟶ H)}
    (hu : ∀ a ∈ b.support, IsRootParametrization i (P.root a) (u a))
    (hw : ∀ a ∈ b.support, IsWeylPoint i (rootWeylPoint P u a) (P.reflection a))
    {m n : ℕ} (neg : Fin m ≃ {α // ¬ b.IsPos α}) (pos : Fin n ≃ {α // b.IsPos α})
    (hE : ∀ k l : Fin n, k < l → ∃ E : Fin n → Polynomial (Polynomial R),
      IsUnivComm (weylFamily P W u) (fun k => (pos k : J)) k l E ∧
        IsUnivComm (weylFamily P W u') (fun k => (pos k : J)) k l E) :
    CommutatorRelations b W u u' (fun k => (pos k : J)) := by
  have hWf := isRootParametrization_weylFamily hu hw W
  have := LocalSplitBigCell.isOpenImmersion_cellMap hG hmax hP b _ hWf neg pos
  intro A _ _ _ s k l hkl x y e he
  obtain ⟨E, h1, h2⟩ := hE k l hkl
  exact posComm_transfer_of_isUnivComm (i := i) (neg := fun k => (neg k : J)) h1 h2 s x y e he

end WeylFamilies

end LocalSplitCell

open LocalSplitCell in
/-- **Universal commutator polynomials of positive cell factors.** Let `u` be a family of
additive-group maps into a group scheme `G` over a commutative ring `R`, equivariant for a
split torus `i` with exponent characters `ch`, whose big-cell map for the index families `neg`
and `pos` is an open immersion, and let `ν` be a cocharacter pairing negatively with the
characters at `neg` and positively with those at `pos`. Then for any two positions `k`, `l`
there are polynomials `E_p ∈ R[S][T]` such that over every ring `B` over `R` and for all
`x y ∈ B`, the commutator of `u_{pos k}(x)` and `u_{pos l}(y)` is the ordered product of the
positive factors with coordinates `E_p(x, y)`; moreover each monomial `S ^ dS T ^ dT` occurring
in `E_p` has `1 ≤ dS`, `1 ≤ dT` and `dS • ch (pos k) + dT • ch (pos l) = ch (pos p)`. -/
def LocalSplitUniversalCommutatorStatement : Prop :=
  ∀ (R : Type u) [CommRing R] (I : Type u) [Fintype I] (J : Type u)
    (G : GroupScheme (Spec (CommRingCat.of R))) (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (ch : J → I → ℤ) (u : J → (Ga R ⟶ G)) (m n : ℕ) (neg : Fin m → J) (pos : Fin n → J),
    IsOpenImmersion (cellMap i u neg pos).left →
    TorusEquivariant i ch u →
    ∀ ν : I → ℤ, (∀ k, coPairing (ch (neg k)) ν < 0) → (∀ k, 0 < coPairing (ch (pos k)) ν) →
    ∀ k l : Fin n, ∃ E : Fin n → Polynomial (Polynomial R),
      (∀ (B : Type u) [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
        (x y : B),
        posComm u pos (Over.mk s) k l ((Scheme.ΓSpecIso (CommRingCat.of B)).inv x)
            ((Scheme.ΓSpecIso (CommRingCat.of B)).inv y) =
          orderedProduct u pos (Over.mk s)
            (fun q => (Scheme.ΓSpecIso (CommRingCat.of B)).inv (lineEval s x y (E q)))) ∧
      (∀ (p : Fin n) (dS dT : ℕ), ((E p).coeff dT).coeff dS ≠ 0 →
        1 ≤ dS ∧ 1 ≤ dT ∧ (dS : ℤ) • ch (pos k) + (dT : ℤ) • ch (pos l) = ch (pos p))

/-- Universal commutator polynomials exist and are bihomogeneous of the expected weights. -/
theorem localSplitUniversalCommutator : LocalSplitUniversalCommutatorStatement.{u} := by
  intro R _ I _ J G i ch u m n neg pos hopen hu ν hneg hpos k l
  have := hopen
  obtain ⟨E, hE⟩ := LocalSplitCell.exists_isUnivComm (i := i) (neg := neg) hu ν hneg hpos k l
  refine ⟨E, fun B _ s x y => hE.posComm_eq s x y, fun p dS dT h => ?_⟩
  obtain ⟨h1, h2⟩ := hE.one_le (i := i) (neg := neg) p h
  exact ⟨h1, h2, hE.weight (neg := neg) hu p h⟩

end Langlands.GroupScheme
