import Langlands.GroupScheme.Dynamic.CoactionGrading
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.Dynamic.AffineInclusionCriterion
import Langlands.GroupScheme.Rational.SplitComponentProof

/-! # Dynamic inclusions for a dominant combination of commuting cocharacters -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace Dynamic

variable {S : Scheme.{u}} {G : GroupScheme S} (χ : (Gm S).toGrp ⟶ G)

/-- The orbit map at a point `v` of `𝔾_m` is conjugation by `χ(v)`. -/
theorem lift_comp_orbit {T : Over S} (v : T ⟶ (Gm S).X) (g : T ⟶ G.X) :
    lift (𝟙 T) v ≫ orbit χ g = (v ≫ χ.hom.hom) * g * (v ≫ χ.hom.hom)⁻¹ := by
  simp only [orbit, MonObj.comp_mul, GrpObj.comp_inv, lift_fst_assoc, lift_snd_assoc,
    Category.id_comp]

end Dynamic

namespace AffineLine

variable {S : Scheme.{u}} {A : CommRingCat.{u}}

variable (A) in
/-- Evaluation at a unit `u`, `A[X, X⁻¹] ⟶ A`. -/
abbrev laurentEval (u : Aˣ) : CommRingCat.of (LaurentPolynomial A) ⟶ A :=
  CommRingCat.ofHom (LaurentPolynomial.eval₂ (RingHom.id A) u)

/-- The point of `𝔾_m` over `Spec A` given by a unit of `A`. -/
def unitPoint (f : Spec A ⟶ S) (u : Aˣ) : Over.mk f ⟶ (Gm S).X :=
  (Gm.pointsEquiv S (Over.mk f)).symm (Units.map (Scheme.ΓSpecIso A).inv.hom.toMonoidHom u)

theorem unitPoint_zpow (f : Spec A ⟶ S) (u : Aˣ) (n : ℤ) :
    unitPoint f (u ^ n) = unitPoint f u ^ n := by
  simp only [unitPoint, map_zpow]

theorem specMap_laurentEval_comp (u : Aˣ) :
    Spec.map (laurentEval A u) ≫ Spec.map (polynomialToLaurent A) ≫ Spec.map (polynomialC A) =
      𝟙 _ := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext a
  simp [Polynomial.toLaurent_C, LaurentPolynomial.eval₂_C]

/-- The point `X = u` of `Spec A[X, X⁻¹]` over `S`. -/
def laurentAt (f : Spec A ⟶ S) (u : Aˣ) : Over.mk f ⟶ laurentScheme f :=
  Over.homMk (Spec.map (laurentEval A u)) (by
    change Spec.map (laurentEval A u) ≫ Spec.map (polynomialToLaurent A) ≫
      Spec.map (polynomialC A) ≫ f = f
    rw [reassoc_of% (specMap_laurentEval_comp u)])

/-- The Laurent point at `X = u` is the point `(id, u)` of `Spec A ×_S 𝔾_{m,S}`. -/
theorem laurentAt_comp_laurentPoint (f : Spec A ⟶ S) (u : Aˣ) :
    laurentAt f u ≫ laurentPoint f = lift (𝟙 _) (unitPoint f u) := by
  refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
  · rw [Category.assoc, laurentPoint, lift_fst, lift_fst]
    apply Over.OverMorphism.ext
    exact specMap_laurentEval_comp u
  · rw [Category.assoc, laurentPoint, lift_snd, lift_snd]
    apply (Gm.pointsEquiv S _).injective
    rw [Gm.pointsEquiv_naturality, MulEquiv.apply_symm_apply, unitPoint, MulEquiv.apply_symm_apply]
    apply Units.ext
    change (Spec.map (laurentEval A u)).appTop
      ((Scheme.ΓSpecIso _).inv (LaurentPolynomial.T 1)) = (Scheme.ΓSpecIso A).inv u
    rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
    simp [LaurentPolynomial.eval₂_T]

section Substitution

variable {D D' : CommRingCat.{u}}

theorem laurentCoeffMap_C_mul_T (g : D' ⟶ D) (a : D') (n : ℤ) :
    laurentCoeffMap g (LaurentPolynomial.C a * LaurentPolynomial.T n) =
      LaurentPolynomial.C (g a) * LaurentPolynomial.T n := by
  rw [map_mul, Corepresented.laurentCoeffMap_C, laurentCoeffMap_T]

theorem laurentCoeffMap_single (g : D' ⟶ D) (a : ℤ) (z : D') :
    laurentCoeffMap g (AddMonoidAlgebra.single a z) = AddMonoidAlgebra.single a (g z) := by
  rw [LaurentPolynomial.single_eq_C_mul_T (R := D'), laurentCoeffMap_C_mul_T,
    ← LaurentPolynomial.single_eq_C_mul_T]

/-- A monomial `v Tʷ` is a polynomial with constant term `t` under the stated conditions. -/
theorem exists_toLaurent_eq_single {w : ℤ} {v t : D} (ht : w ≠ 0 → t = 0)
    (hv : w < 0 → v = 0) (hvt : w = 0 → v = t) :
    ∃ p : Polynomial D, Polynomial.toLaurent p = AddMonoidAlgebra.single w v ∧ p.eval 0 = t := by
  rcases lt_trichotomy w 0 with h | rfl | h
  · refine ⟨0, ?_, ?_⟩
    · rw [hv h, map_zero, AddMonoidAlgebra.single_zero]
    · rw [Polynomial.eval_zero, ht h.ne]
  · refine ⟨Polynomial.C v, ?_, ?_⟩
    · exact (Polynomial.toLaurent_C v).trans (LaurentPolynomial.single_eq_C v).symm
    · rw [Polynomial.eval_C, hvt rfl]
  · refine ⟨Polynomial.C v * Polynomial.X ^ w.toNat, ?_, ?_⟩
    · rw [Polynomial.toLaurent_C_mul_X_pow, Int.toNat_of_nonneg h.le,
        ← LaurentPolynomial.single_eq_C_mul_T]
    · rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, zero_pow (by omega),
        mul_zero, ht h.ne']

/-- Substituting the variable for itself after embedding the coefficients as constants. -/
theorem laurentCoeffMap_comp_laurentC_comp_laurentEval (g : D' ⟶ D) :
    laurentCoeffMap (g ≫ Gm.laurentC D) ≫
        laurentEval (CommRingCat.of (LaurentPolynomial D)) (Gm.relativeCoordUnit D) =
      laurentCoeffMap g := by
  refine CommRingCat.hom_ext (RingHom.ext fun q => ?_)
  induction q using LaurentPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add] at hp hq ⊢; rw [hp, hq]
  | C_mul_T n a =>
    rw [CommRingCat.comp_apply, laurentCoeffMap_C_mul_T, laurentCoeffMap_C_mul_T]
    simp [Gm.relativeCoordUnit_zpow_val]

theorem laurentCoeffMap_laurentC_comp_laurentEval :
    laurentCoeffMap (Gm.laurentC D) ≫
        laurentEval (CommRingCat.of (LaurentPolynomial D)) (Gm.relativeCoordUnit D) = 𝟙 _ := by
  refine CommRingCat.hom_ext (RingHom.ext fun q => ?_)
  induction q using LaurentPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add] at hp hq ⊢; rw [hp, hq]
  | C_mul_T n a =>
    rw [CommRingCat.comp_apply, laurentCoeffMap_C_mul_T]
    simp [Gm.relativeCoordUnit_zpow_val]

variable (D) in
/-- The variable of `D[X, X⁻¹]`, as a constant unit of `D[X, X⁻¹][Y, Y⁻¹]`. -/
abbrev innerUnit : (LaurentPolynomial (CommRingCat.of (LaurentPolynomial D)))ˣ :=
  Units.map (LaurentPolynomial.C : LaurentPolynomial D →+* _).toMonoidHom (Gm.relativeCoordUnit D)

theorem innerUnit_zpow_val (n : ℤ) :
    ((innerUnit D ^ n : (LaurentPolynomial (CommRingCat.of (LaurentPolynomial D)))ˣ) :
      LaurentPolynomial (CommRingCat.of (LaurentPolynomial D))) =
        LaurentPolynomial.C (LaurentPolynomial.T n) := by
  rw [← map_zpow, Units.coe_map, Gm.relativeCoordUnit_zpow_val]
  rfl

/-- Substituting the inner variable for the outer one after embedding `D` as double constants
gives the constants `D[X, X⁻¹] ⟶ D[X, X⁻¹][Y, Y⁻¹]`. -/
theorem laurentCoeffMap_laurentC_laurentC_comp_laurentEval :
    laurentCoeffMap (Gm.laurentC D ≫ Gm.laurentC (CommRingCat.of (LaurentPolynomial D))) ≫
        laurentEval (CommRingCat.of (LaurentPolynomial (CommRingCat.of (LaurentPolynomial D))))
          (innerUnit D) =
      Gm.laurentC (CommRingCat.of (LaurentPolynomial D)) := by
  refine CommRingCat.hom_ext (RingHom.ext fun q => ?_)
  induction q using LaurentPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add] at hp hq ⊢; rw [hp, hq]
  | C_mul_T n a =>
    rw [CommRingCat.comp_apply, laurentCoeffMap_C_mul_T]
    change LaurentPolynomial.eval₂ (RingHom.id _) (innerUnit D)
      (LaurentPolynomial.C (LaurentPolynomial.C (LaurentPolynomial.C a)) * LaurentPolynomial.T n) =
        LaurentPolynomial.C (LaurentPolynomial.C a * LaurentPolynomial.T n)
    rw [LaurentPolynomial.eval₂_C_mul_T, RingHom.id_apply, innerUnit_zpow_val, map_mul]

/-- The coefficients of the double substitution. -/
theorem coeff_coeff_laurentEval_laurentCoeffMap (h : D' ⟶ CommRingCat.of (LaurentPolynomial D))
    (q : LaurentPolynomial D') (a j : ℤ) :
    (((laurentCoeffMap (h ≫ laurentCoeffMap (Gm.laurentC D)) ≫
        laurentEval (CommRingCat.of (LaurentPolynomial (CommRingCat.of (LaurentPolynomial D))))
          (innerUnit D)) q).coeff a).coeff j = (h (q.coeff j)).coeff a := by
  induction q using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, AddMonoidAlgebra.coeff_add,
      Finsupp.add_apply, hp, hq, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, map_add,
      AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  | C_mul_T n b =>
    rw [CommRingCat.comp_apply, laurentCoeffMap_C_mul_T]
    change ((LaurentPolynomial.eval₂ (RingHom.id _) (innerUnit D)
      (LaurentPolynomial.C (laurentCoeffMap (Gm.laurentC D) (h b)) * LaurentPolynomial.T n)).coeff
        a).coeff j = _
    rw [LaurentPolynomial.eval₂_C_mul_T, RingHom.id_apply, innerUnit_zpow_val,
      ← LaurentPolynomial.single_eq_C, AddMonoidAlgebra.coeff_mul_single_zero,
      Corepresented.coeff_laurentCoeffMap, ← LaurentPolynomial.single_eq_C_mul_T]
    change (LaurentPolynomial.C ((h b).coeff a) * LaurentPolynomial.T n).coeff j = _
    rw [← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single,
      AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Finsupp.single_apply]
    split_ifs <;> simp

end Substitution

end AffineLine

namespace Corepresented

open AffineLine

variable {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}} {B : CommAlgCat.{u} R}
  {e : (F ⋙ forget GrpCat).CorepresentableBy B}

section Conjugation

variable (χ : (Gm (Spec R)).toGrp ⟶ groupScheme F e) {A : CommRingCat.{u}} {f : Spec A ⟶ Spec R}

/-- Conjugating a point over `Spec A` by `χ(u)` composes its classifying map with the coaction
and the evaluation at `u`. -/
theorem pointRing_conj (x : Over.mk f ⟶ (groupScheme F e).X) (u : Aˣ) :
    pointRing ((unitPoint f u ≫ χ.hom.hom) * x * (unitPoint f u ≫ χ.hom.hom)⁻¹) =
      coaction χ ≫ laurentCoeffMap (pointRing x) ≫ laurentEval A u := by
  rw [← Dynamic.lift_comp_orbit, ← laurentAt_comp_laurentPoint, Category.assoc]
  apply Spec.map_injective
  rw [specMap_pointRing, Over.comp_left, laurentPoint_comp_orbit_left]
  simp only [Spec.map_comp, Category.assoc]
  rfl

variable (e) in
/-- The point of `Spec B` over `Spec A` given by a ring map `B ⟶ A`. -/
def ringPoint (φ : CommRingCat.of B ⟶ A) :
    Over.mk (Spec.map φ ≫ structureMap e) ⟶ (groupScheme F e).X :=
  Over.homMk (Spec.map φ) rfl

theorem pointRing_ringPoint (φ : CommRingCat.of B ⟶ A) : pointRing (ringPoint e φ) = φ :=
  Spec.preimage_map φ

end Conjugation

section Combination

variable {χ tau ψ : (Gm (Spec R)).toGrp ⟶ groupScheme F e} {n : ℤ}

theorem conj_mul_conj {M : Type*} [Group M] (a b x : M) :
    (a * b) * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by
  group

theorem conj_conj_of_commute {M : Type*} [Group M] {a b : M} (h : a * b = b * a) (x : M) :
    a * (b * x * b⁻¹) * a⁻¹ = b * (a * x * a⁻¹) * b⁻¹ := by
  rw [← conj_mul_conj, ← conj_mul_conj, h]

/-- The coaction of `ψ` with `ψ(t) = χ(t)ⁿ τ(t)` is the coaction of `χ`, then that of `τ` on the
coefficients, evaluated at `Tⁿ`. -/
theorem coaction_eq_of_points
    (hψ : ∀ (T : Over (Spec R)) (t : T ⟶ (Gm (Spec R)).X),
      t ≫ ψ.hom.hom = ((t ^ n) ≫ χ.hom.hom) * (t ≫ tau.hom.hom)) :
    coaction ψ = coaction χ ≫ laurentCoeffMap (coaction tau) ≫
      laurentEval (CommRingCat.of (LaurentPolynomial (CommRingCat.of B)))
        (Gm.relativeCoordUnit (CommRingCat.of B) ^ n) := by
  have h1 : unitPoint (Spec.map (Gm.laurentC (CommRingCat.of B)) ≫ structureMap e)
      (Gm.relativeCoordUnit (CommRingCat.of B)) ≫ ψ.hom.hom =
        (unitPoint (Spec.map (Gm.laurentC (CommRingCat.of B)) ≫ structureMap e)
          (Gm.relativeCoordUnit (CommRingCat.of B) ^ n) ≫ χ.hom.hom) *
        (unitPoint (Spec.map (Gm.laurentC (CommRingCat.of B)) ≫ structureMap e)
          (Gm.relativeCoordUnit (CommRingCat.of B)) ≫ tau.hom.hom) := by
    rw [hψ, unitPoint_zpow]
  have key := pointRing_conj ψ (ringPoint e (Gm.laurentC (CommRingCat.of B)))
    (Gm.relativeCoordUnit (CommRingCat.of B))
  rw [h1, conj_mul_conj, pointRing_conj, pointRing_conj, pointRing_ringPoint,
    laurentCoeffMap_laurentC_comp_laurentEval, Category.comp_id] at key
  exact key.symm

/-- A function homogeneous of weight `a` for `χ` and `j` for `τ` has weight `j + n a` for `ψ`. -/
theorem coaction_eq_single_of_points
    (hψ : ∀ (T : Over (Spec R)) (t : T ⟶ (Gm (Spec R)).X),
      t ≫ ψ.hom.hom = ((t ^ n) ≫ χ.hom.hom) * (t ≫ tau.hom.hom)) {z : B} {a j : ℤ}
    (ha : coaction χ z = AddMonoidAlgebra.single a z)
    (hj : coaction tau z = AddMonoidAlgebra.single j z) :
    coaction ψ z = AddMonoidAlgebra.single (j + n * a) z := by
  rw [coaction_eq_of_points hψ]
  change LaurentPolynomial.eval₂ (RingHom.id _) _
    (laurentCoeffMap (coaction tau) (coaction χ z)) = _
  rw [ha, LaurentPolynomial.single_eq_C_mul_T (R := CommRingCat.of B) z a,
    laurentCoeffMap_C_mul_T, hj, LaurentPolynomial.eval₂_C_mul_T, RingHom.id_apply, ← zpow_mul,
    Gm.relativeCoordUnit_zpow_val, LaurentPolynomial.single_eq_C_mul_T (R := CommRingCat.of B) z j,
    LaurentPolynomial.single_eq_C_mul_T (R := CommRingCat.of B) z (j + n * a), mul_assoc,
    ← LaurentPolynomial.T_add]

/-- If `χ` and `τ` commute, their gradings commute: the `τ`-weight-`j` part of the
`χ`-weight-`a` part of `b` is the `χ`-weight-`a` part of its `τ`-weight-`j` part. -/
theorem coeff_coaction_comm
    (hc : ∀ (T : Over (Spec R)) (s t : T ⟶ (Gm (Spec R)).X),
      (s ≫ χ.hom.hom) * (t ≫ tau.hom.hom) = (t ≫ tau.hom.hom) * (s ≫ χ.hom.hom))
    (b : B) (a j : ℤ) :
    (coaction tau ((coaction χ b).coeff a)).coeff j =
      (coaction χ ((coaction tau b).coeff j)).coeff a := by
  have key : coaction χ ≫ laurentCoeffMap (coaction tau) =
      coaction tau ≫ laurentCoeffMap (coaction χ ≫ laurentCoeffMap (Gm.laurentC (CommRingCat.of B))) ≫
        laurentEval (CommRingCat.of (LaurentPolynomial
          (CommRingCat.of (LaurentPolynomial (CommRingCat.of B))))) (innerUnit (CommRingCat.of B)) := by
    have h := congrArg pointRing (conj_conj_of_commute
      (hc _ (unitPoint (Spec.map (Gm.laurentC (CommRingCat.of B) ≫
          Gm.laurentC (CommRingCat.of (LaurentPolynomial (CommRingCat.of B)))) ≫ structureMap e)
          (Gm.relativeCoordUnit (CommRingCat.of (LaurentPolynomial (CommRingCat.of B)))))
        (unitPoint (Spec.map (Gm.laurentC (CommRingCat.of B) ≫
          Gm.laurentC (CommRingCat.of (LaurentPolynomial (CommRingCat.of B)))) ≫ structureMap e)
          (innerUnit (CommRingCat.of B))))
      (ringPoint e (Gm.laurentC (CommRingCat.of B) ≫
        Gm.laurentC (CommRingCat.of (LaurentPolynomial (CommRingCat.of B))))))
    rw [pointRing_conj, pointRing_conj, pointRing_conj, pointRing_conj, pointRing_ringPoint,
      laurentCoeffMap_laurentC_laurentC_comp_laurentEval,
      laurentCoeffMap_comp_laurentC_comp_laurentEval,
      laurentCoeffMap_comp_laurentC_comp_laurentEval] at h
    exact h
  have hb := congrArg (fun φ => ((φ b).coeff a).coeff j) key
  dsimp only at hb
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply, coeff_laurentCoeffMap,
    coeff_coeff_laurentEval_laurentCoeffMap] at hb
  exact hb

/-- A finite-type coordinate algebra is generated by pieces homogeneous for both `χ` and `τ`
whose `τ`-weights are bounded by a fixed `M`. -/
theorem exists_bound [Algebra.FiniteType R B]
    (hc : ∀ (T : Over (Spec R)) (s t : T ⟶ (Gm (Spec R)).X),
      (s ≫ χ.hom.hom) * (t ≫ tau.hom.hom) = (t ≫ tau.hom.hom) * (s ≫ χ.hom.hom)) :
    ∃ M : ℕ, ∀ Q : B → Prop, (∀ r, Q (algebraMap R B r)) → (∀ x y, Q x → Q y → Q (x + y)) →
      (∀ x y, Q x → Q y → Q (x * y)) →
      (∀ (a j : ℤ) (z : B), j.natAbs ≤ M → coaction χ z = AddMonoidAlgebra.single a z →
        coaction tau z = AddMonoidAlgebra.single j z → Q z) → ∀ b, Q b := by
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := B)
  refine ⟨s.sup fun y => (coaction χ y).coeff.support.sup fun a =>
    (coaction tau ((coaction χ y).coeff a)).coeff.support.sup Int.natAbs, ?_⟩
  intro Q h0 hadd hmul hgen b
  have hQ0 : Q 0 := by simpa using h0 0
  have hb : b ∈ Algebra.adjoin R (s : Set B) := by rw [hs]; exact Algebra.mem_top
  induction hb using Algebra.adjoin_induction with
  | mem y hy =>
    rw [← sum_coeff_coaction χ y, Finsupp.sum]
    refine Finset.sum_induction _ Q hadd hQ0 fun a ha => ?_
    show Q ((coaction χ y).coeff a)
    rw [← sum_coeff_coaction tau ((coaction χ y).coeff a), Finsupp.sum]
    refine Finset.sum_induction _ Q hadd hQ0 fun j hj => ?_
    refine hgen a j _ ?_ ?_ (coaction_coeff_coaction tau _ j)
    · exact Finset.le_sup_of_le hy (Finset.le_sup_of_le ha (Finset.le_sup (f := Int.natAbs) hj))
    · rw [coeff_coaction_comm hc y a j]
      exact coaction_coeff_coaction χ _ a
  | algebraMap r => exact h0 r
  | add x y _ _ hx hy => exact hadd x y hx hy
  | mul x y _ _ hx hy => exact hmul x y hx hy

theorem weight_lt_zero {M : ℕ} {a j : ℤ} (hn : (M : ℤ) < n) (hj : j.natAbs ≤ M) (ha : a < 0) :
    j + n * a < 0 := by
  have hj' : j ≤ M := by omega
  have h : n * 1 ≤ n * -a := mul_le_mul_of_nonneg_left (by omega) (by omega)
  linarith

theorem weight_pos {M : ℕ} {a j : ℤ} (hn : (M : ℤ) < n) (hj : j.natAbs ≤ M) (ha : 0 < a) :
    0 < j + n * a := by
  have hj' : -(M : ℤ) ≤ j := by omega
  have h : n * 1 ≤ n * a := mul_le_mul_of_nonneg_left (by omega) (by omega)
  linarith

theorem weight_ne_zero {M : ℕ} {a j : ℤ} (hn : (M : ℤ) < n) (hj : j.natAbs ≤ M) (ha : a ≠ 0) :
    j + n * a ≠ 0 := by
  rcases ha.lt_or_gt with h | h
  · exact (weight_lt_zero hn hj h).ne
  · exact (weight_pos hn hj h).ne'

end Combination

section Tests

variable (χ : (Gm (Spec R)).toGrp ⟶ groupScheme F e)

/-- Centralizer membership as an identity of Laurent polynomials. -/
theorem mem_centralizer_iff' {A : CommRingCat.{u}} {f : Spec A ⟶ Spec R}
    (x : Over.mk f ⟶ (groupScheme F e).X) :
    x ∈ (Dynamic.centralizer χ).carrier (Over.mk f) ↔
      ∀ b, laurentCoeffMap (pointRing x) (coaction χ b) = LaurentPolynomial.C (pointRing x b) := by
  rw [mem_centralizer_iff]
  refine forall_congr' fun b => ⟨fun h => sub_eq_zero.1 (LaurentPolynomial.ext fun m => ?_),
    fun h m => ?_⟩
  · rw [← pointRing_coeff_coaction_sub_C, h m]
    rfl
  · rw [pointRing_coeff_coaction_sub_C, h, sub_self]
    rfl

theorem counit_algebraMap (r : R) : counit e (algebraMap R B r) = r := by
  have h := algebraMap_comp_pointRing (1 : Over.mk (𝟙 (Spec R)) ⟶ (groupScheme F e).X)
  rw [Spec.preimage_id] at h
  exact congrArg (fun φ => φ.hom r) h

/-- The counit kills functions of nonzero weight. -/
theorem counit_eq_zero {z : B} {a : ℤ} (hz : coaction χ z = AddMonoidAlgebra.single a z)
    (ha : a ≠ 0) : counit e z = 0 := by
  have h := (mem_centralizer_iff' χ (1 : Over.mk (𝟙 (Spec R)) ⟶ (groupScheme F e).X)).1
    (one_mem _) z
  rw [hz, laurentCoeffMap_single] at h
  have h' := congrArg (fun q => q.coeff a) h
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same, LaurentPolynomial.C_apply, ha,
    ↓reduceIte] at h'
  exact h'

end Tests

section Inclusions

variable {χ tau ψ : (Gm (Spec R)).toGrp ⟶ groupScheme F e} {n : ℤ} {M : ℕ}
  {A : CommRingCat.{u}} (g : CommRingCat.of B ⟶ A)

theorem parabolic_test (hn : (M : ℤ) < n)
    (hψ : ∀ (T : Over (Spec R)) (t : T ⟶ (Gm (Spec R)).X),
      t ≫ ψ.hom.hom = ((t ^ n) ≫ χ.hom.hom) * (t ≫ tau.hom.hom))
    (hM : ∀ Q : B → Prop, (∀ r, Q (algebraMap R B r)) → (∀ x y, Q x → Q y → Q (x + y)) →
      (∀ x y, Q x → Q y → Q (x * y)) →
      (∀ (a j : ℤ) (z : B), j.natAbs ≤ M → coaction χ z = AddMonoidAlgebra.single a z →
        coaction tau z = AddMonoidAlgebra.single j z → Q z) → ∀ b, Q b)
    (hg : ∀ b, ∀ m < 0, g ((coaction ψ b).coeff m) = 0) :
    ∀ b, ∀ m < 0, g ((coaction χ b).coeff m) = 0 := by
  have key : ∀ b, laurentCoeffMap g (coaction χ b) ∈ (Polynomial.toLaurent (R := A)).range := by
    refine hM _ (fun r => ?_) (fun x y hx hy => ?_) (fun x y hx hy => ?_)
      fun a j z hj ha htau => ?_
    · rw [coaction_algebraMap, laurentCoeffMap_C]
      exact RingHom.mem_range.2 ⟨Polynomial.C _, Polynomial.toLaurent_C _⟩
    · rw [map_add, map_add]
      exact add_mem hx hy
    · rw [map_mul, map_mul]
      exact mul_mem hx hy
    · rw [ha, laurentCoeffMap_single]
      rcases lt_or_ge a 0 with h | h
      · have hz := hg z _ (weight_lt_zero hn hj h)
        rw [coaction_eq_single_of_points hψ ha htau, AddMonoidAlgebra.coeff_single,
          Finsupp.single_eq_same] at hz
        rw [hz, AddMonoidAlgebra.single_zero]
        exact zero_mem _
      · refine RingHom.mem_range.2 ⟨Polynomial.C (g z) * Polynomial.X ^ a.toNat, ?_⟩
        rw [Polynomial.toLaurent_C_mul_X_pow, Int.toNat_of_nonneg h,
          ← LaurentPolynomial.single_eq_C_mul_T]
  intro b m hm
  obtain ⟨p, hp⟩ := RingHom.mem_range.1 (key b)
  rw [← coeff_laurentCoeffMap, ← hp, coeff_toLaurent_of_neg p hm]

theorem centralizer_test (hn : (M : ℤ) < n)
    (hψ : ∀ (T : Over (Spec R)) (t : T ⟶ (Gm (Spec R)).X),
      t ≫ ψ.hom.hom = ((t ^ n) ≫ χ.hom.hom) * (t ≫ tau.hom.hom))
    (hM : ∀ Q : B → Prop, (∀ r, Q (algebraMap R B r)) → (∀ x y, Q x → Q y → Q (x + y)) →
      (∀ x y, Q x → Q y → Q (x * y)) →
      (∀ (a j : ℤ) (z : B), j.natAbs ≤ M → coaction χ z = AddMonoidAlgebra.single a z →
        coaction tau z = AddMonoidAlgebra.single j z → Q z) → ∀ b, Q b)
    (hg : ∀ b, laurentCoeffMap g (coaction ψ b) = LaurentPolynomial.C (g b)) :
    ∀ b, laurentCoeffMap g (coaction χ b) = LaurentPolynomial.C (g b) := by
  refine hM _ (fun r => ?_) (fun x y hx hy => ?_) (fun x y hx hy => ?_)
    fun a j z hj ha htau => ?_
  · rw [coaction_algebraMap, laurentCoeffMap_C]
  · rw [map_add, map_add, hx, hy, map_add, map_add]
  · rw [map_mul, map_mul, hx, hy, map_mul, map_mul]
  · rw [ha, laurentCoeffMap_single]
    rcases eq_or_ne a 0 with rfl | h
    · exact LaurentPolynomial.single_eq_C _
    · have hw := weight_ne_zero hn hj h
      have hz := congrArg (fun q => q.coeff (j + n * a)) (hg z)
      rw [coaction_eq_single_of_points hψ ha htau, laurentCoeffMap_single] at hz
      simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same, LaurentPolynomial.C_apply,
        hw, ↓reduceIte] at hz
      rw [hz, AddMonoidAlgebra.single_zero, map_zero]

theorem unipotent_test (hn : (M : ℤ) < n)
    (hψ : ∀ (T : Over (Spec R)) (t : T ⟶ (Gm (Spec R)).X),
      t ≫ ψ.hom.hom = ((t ^ n) ≫ χ.hom.hom) * (t ≫ tau.hom.hom))
    (hM : ∀ Q : B → Prop, (∀ r, Q (algebraMap R B r)) → (∀ x y, Q x → Q y → Q (x + y)) →
      (∀ x y, Q x → Q y → Q (x * y)) →
      (∀ (a j : ℤ) (z : B), j.natAbs ≤ M → coaction χ z = AddMonoidAlgebra.single a z →
        coaction tau z = AddMonoidAlgebra.single j z → Q z) → ∀ b, Q b)
    (hg : (∀ b, ∀ m < 0, g ((coaction χ b).coeff m) = 0) ∧
      ∀ b, g ((coaction χ b).coeff 0 - algebraMap R B (counit e b)) = 0) :
    (∀ b, ∀ m < 0, g ((coaction ψ b).coeff m) = 0) ∧
      ∀ b, g ((coaction ψ b).coeff 0 - algebraMap R B (counit e b)) = 0 := by
  have key : ∀ b, ∃ p : Polynomial A, Polynomial.toLaurent p = laurentCoeffMap g (coaction ψ b) ∧
      p.eval 0 = g (algebraMap R B (counit e b)) := by
    refine hM _ (fun r => ?_) ?_ ?_ fun a j z hj ha htau => ?_
    · refine ⟨Polynomial.C (g (algebraMap R B r)), ?_, ?_⟩
      · rw [coaction_algebraMap, laurentCoeffMap_C, Polynomial.toLaurent_C]
      · rw [Polynomial.eval_C, counit_algebraMap]
    · rintro x y ⟨p, hp, hp0⟩ ⟨q, hq, hq0⟩
      refine ⟨p + q, ?_, ?_⟩
      · rw [map_add, hp, hq, map_add, map_add]
      · rw [Polynomial.eval_add, hp0, hq0, map_add, map_add, map_add]
    · rintro x y ⟨p, hp, hp0⟩ ⟨q, hq, hq0⟩
      refine ⟨p * q, ?_, ?_⟩
      · rw [map_mul, hp, hq, map_mul, map_mul]
      · rw [Polynomial.eval_mul, hp0, hq0, map_mul, map_mul, map_mul]
    · rw [coaction_eq_single_of_points hψ ha htau, laurentCoeffMap_single]
      have hc0 : j + n * a ≠ 0 → counit e z = 0 := fun hw => by
        rcases eq_or_ne a 0 with rfl | h
        · exact counit_eq_zero tau htau (by simpa using hw)
        · exact counit_eq_zero χ ha h
      refine exists_toLaurent_eq_single (fun hw => by rw [hc0 hw, map_zero, map_zero])
        (fun hw => ?_) (fun hw => ?_)
      · rcases lt_or_ge a 0 with h | h
        · have h1 := hg.1 z a h
          rwa [ha, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same] at h1
        · have ha0 : a = 0 := by
            by_contra h'
            have := weight_pos hn hj (lt_of_le_of_ne h (Ne.symm h'))
            linarith
          subst ha0
          have h1 := hg.2 z
          rw [ha, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same, hc0 hw.ne, map_zero,
            sub_zero] at h1
          exact h1
      · have ha0 : a = 0 := by
          by_contra h'
          exact weight_ne_zero hn hj h' hw
        subst ha0
        have h1 := hg.2 z
        rw [ha, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same, map_sub] at h1
        exact sub_eq_zero.1 h1
  refine ⟨fun b m hm => ?_, fun b => ?_⟩
  · obtain ⟨p, hp, -⟩ := key b
    rw [← coeff_laurentCoeffMap, ← hp, coeff_toLaurent_of_neg p hm]
  · obtain ⟨p, hp, hp0⟩ := key b
    have h0 : (Polynomial.toLaurent p).coeff 0 = p.eval 0 :=
      (coeff_toLaurent_natCast p 0).trans (Polynomial.coeff_zero_eq_eval_zero p)
    rw [map_sub, ← coeff_laurentCoeffMap, ← hp, h0, hp0, sub_self]

end Inclusions

section Model

variable {χ tau : (Gm (Spec R)).toGrp ⟶ groupScheme F e}

local instance dominantCombinationInclusionsIsAffine : IsAffine (groupScheme F e).X.left :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of B)))

/-- The dominant-combination inclusions for a finite-type corepresented group. -/
theorem exists_dominant_inclusions [Algebra.FiniteType R B]
    (hc : ∀ (T : Over (Spec R)) (s t : T ⟶ (Gm (Spec R)).X),
      (s ≫ χ.hom.hom) * (t ≫ tau.hom.hom) = (t ≫ tau.hom.hom) * (s ≫ χ.hom.hom)) :
    ∃ N : ℕ, ∀ n : ℤ, (N : ℤ) ≤ n → ∀ ψ : (Gm (Spec R)).toGrp ⟶ groupScheme F e,
      (∀ (T : Over (Spec R)) (t : T ⟶ (Gm (Spec R)).X),
        t ≫ ψ.hom.hom = ((t ^ n) ≫ χ.hom.hom) * (t ≫ tau.hom.hom)) →
      Dynamic.parabolic ψ ≤ Dynamic.parabolic χ ∧ Dynamic.unipotent χ ≤ Dynamic.unipotent ψ ∧
        Dynamic.centralizer ψ ≤ Dynamic.centralizer χ := by
  obtain ⟨M, hM⟩ := exists_bound hc
  refine ⟨M + 1, fun n hn ψ hψ => ?_⟩
  have hn' : (M : ℤ) < n := by omega
  refine ⟨Dynamic.parabolic_le_of_affine_tests ψ _ fun A f x hx => ?_,
    Dynamic.unipotent_le_of_affine_tests χ _ fun A f x hx => ?_,
    Dynamic.centralizer_le_of_affine_tests ψ _ fun A f x hx => ?_⟩
  · rw [mem_parabolic_iff] at hx ⊢
    exact parabolic_test _ hn' hψ hM hx
  · rw [mem_unipotent_iff] at hx ⊢
    exact unipotent_test _ hn' hψ hM hx
  · rw [mem_centralizer_iff'] at hx ⊢
    exact centralizer_test _ hn' hψ hM hx

end Model

end Corepresented

namespace Dynamic

/-- For commuting cocharacters `χ` and `τ` of an affine group of finite type over a field, every
cocharacter `ψ = χⁿ τ` with `n` large enough satisfies `P(ψ) ≤ P(χ)`, `U(χ) ≤ U(ψ)` and
`Z(ψ) ≤ Z(χ)`. -/
theorem exists_dominant_inclusions {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (χ tau : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (htau : SubgroupFunctor.range tau ≤ Dynamic.centralizer χ) :
    ∃ N : ℕ, ∀ n : ℤ, (N : ℤ) ≤ n → ∀ ψ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G,
      (∀ (T : Over (Spec (CommRingCat.of k))) (t : T ⟶ (Gm (Spec (CommRingCat.of k))).X),
        t ≫ ψ.hom.hom = ((t ^ n) ≫ χ.hom.hom) * (t ≫ tau.hom.hom)) →
      Dynamic.parabolic ψ ≤ Dynamic.parabolic χ ∧ Dynamic.unipotent χ ≤ Dynamic.unipotent ψ ∧
        Dynamic.centralizer ψ ≤ Dynamic.centralizer χ := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := finiteType_coordinateAlgebra G
  let E := AffineCoordinates.groupSchemeIso G
  have hc : ∀ (T : Over (Spec (CommRingCat.of k))) (s t : T ⟶ (Gm (Spec (CommRingCat.of k))).X),
      (s ≫ (χ ≫ E.inv).hom.hom) * (t ≫ (tau ≫ E.inv).hom.hom) =
        (t ≫ (tau ≫ E.inv).hom.hom) * (s ≫ (χ ≫ E.inv).hom.hom) := by
    intro T s t
    have hmem : t ≫ tau.hom.hom ∈ (Dynamic.centralizer χ).carrier T :=
      htau T (SubgroupFunctor.mem_range.2 ⟨t, rfl⟩)
    rw [Dynamic.mem_centralizer] at hmem
    have h := congrArg (lift (𝟙 T) s ≫ ·) hmem
    simp only [lift_comp_orbit, lift_fst_assoc, Category.id_comp] at h
    rw [mul_inv_eq_iff_eq_mul] at h
    rw [Grp.comp_hom_hom, Grp.comp_hom_hom, ← Category.assoc, ← Category.assoc,
      ← MonObj.mul_comp, ← MonObj.mul_comp, h]
  obtain ⟨N, hN⟩ := Corepresented.exists_dominant_inclusions hc
  refine ⟨N, fun n hn ψ hψ => ?_⟩
  have hψ' : ∀ (T : Over (Spec (CommRingCat.of k))) (t : T ⟶ (Gm (Spec (CommRingCat.of k))).X),
      t ≫ (ψ ≫ E.inv).hom.hom =
        ((t ^ n) ≫ (χ ≫ E.inv).hom.hom) * (t ≫ (tau ≫ E.inv).hom.hom) := by
    intro T t
    simp only [Grp.comp_hom_hom]
    rw [← Category.assoc, ← Category.assoc, ← Category.assoc, hψ, MonObj.mul_comp]
  obtain ⟨hP, hU, hZ⟩ := hN n hn (ψ ≫ E.inv) hψ'
  refine ⟨?_, ?_, ?_⟩
  · rw [parabolic_eq_comap_of_iso ψ E.symm, parabolic_eq_comap_of_iso χ E.symm]
    exact SubgroupFunctor.comap_mono hP
  · rw [unipotent_eq_comap_of_iso ψ E.symm, unipotent_eq_comap_of_iso χ E.symm]
    exact SubgroupFunctor.comap_mono hU
  · rw [centralizer_eq_comap_of_iso ψ E.symm, centralizer_eq_comap_of_iso χ E.symm]
    exact SubgroupFunctor.comap_mono hZ

end Dynamic

end Langlands.GroupScheme
