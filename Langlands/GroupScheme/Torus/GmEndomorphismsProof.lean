import Langlands.GroupScheme.Torus.GmEndomorphismsStatement
import Langlands.GroupScheme.MultiplicativeLaurent
import Langlands.AbelianScheme.Multiplication

/-! # Endomorphisms of the multiplicative group over an integral domain -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Polynomial
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

universe u

/-! ### Units of Laurent polynomials over a domain -/

/-- A polynomial whose trailing degree equals its degree is a single monomial. -/
theorem eq_C_mul_X_pow_of_natTrailingDegree_eq_natDegree {R : Type*} [Semiring R] {p : R[X]}
    (h : p.natTrailingDegree = p.natDegree) : p = C p.leadingCoeff * X ^ p.natDegree := by
  ext n
  rw [coeff_C_mul_X_pow]
  split_ifs with hn
  · rw [hn]
    rfl
  · rcases Nat.lt_or_gt_of_ne hn with hn | hn
    · exact coeff_eq_zero_of_lt_natTrailingDegree (h ▸ hn)
    · exact coeff_eq_zero_of_natDegree_lt hn

/-- Over an integral domain, every unit of `R[T, T⁻¹]` is a unit constant times a power
of `T`. -/
theorem laurent_unit_eq_C_mul_T {R : Type*} [CommRing R] [IsDomain R]
    (v : (LaurentPolynomial R)ˣ) :
    ∃ (c : Rˣ) (n : ℤ),
      (v : LaurentPolynomial R) = LaurentPolynomial.C (c : R) * LaurentPolynomial.T n := by
  obtain ⟨a, p, hp⟩ := LaurentPolynomial.exists_T_pow (v : LaurentPolynomial R)
  obtain ⟨b, q, hq⟩ :=
    LaurentPolynomial.exists_T_pow ((v⁻¹ : (LaurentPolynomial R)ˣ) : LaurentPolynomial R)
  have hpq : p * q = X ^ (a + b) := by
    apply Polynomial.toLaurent_injective
    rw [map_mul, hp, hq, Polynomial.toLaurent_X_pow, Nat.cast_add, LaurentPolynomial.T_add,
      mul_mul_mul_comm, Units.mul_inv, one_mul]
  have hp0 : p ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hpq
    exact pow_ne_zero _ X_ne_zero hpq.symm
  have hq0 : q ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hpq
    exact pow_ne_zero _ X_ne_zero hpq.symm
  have hdeg := congrArg natDegree hpq
  rw [natDegree_mul hp0 hq0, natDegree_X_pow] at hdeg
  have htr := congrArg natTrailingDegree hpq
  rw [natTrailingDegree_mul hp0 hq0, natTrailingDegree_X_pow] at htr
  have h1 := natTrailingDegree_le_natDegree (p := p)
  have h2 := natTrailingDegree_le_natDegree (p := q)
  have hpm : p.natTrailingDegree = p.natDegree := by omega
  have hlead : p.leadingCoeff * q.leadingCoeff = 1 := by
    rw [← leadingCoeff_mul, hpq, leadingCoeff_X_pow]
  have hmono : Polynomial.toLaurent p =
      LaurentPolynomial.C p.leadingCoeff * LaurentPolynomial.T p.natDegree := by
    conv_lhs => rw [eq_C_mul_X_pow_of_natTrailingDegree_eq_natDegree hpm]
    exact Polynomial.toLaurent_C_mul_X_pow _ _
  refine ⟨⟨p.leadingCoeff, q.leadingCoeff, hlead, by rw [mul_comm, hlead]⟩,
    p.natDegree - a, ?_⟩
  have hv : (v : LaurentPolynomial R) = Polynomial.toLaurent p * LaurentPolynomial.T (-a) := by
    rw [hp, mul_assoc, ← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero,
      mul_one]
  rw [hv, hmono, mul_assoc, ← LaurentPolynomial.T_add, sub_eq_add_neg]

/-! ### The universal point of `𝔾_m` over an affine base -/

namespace Gm

variable (R : CommRingCat.{u})

/-- The structural map `Spec R[T, T⁻¹] ⟶ Spec R`. -/
abbrev laurentStructure : Spec (CommRingCat.of (LaurentPolynomial R)) ⟶ Spec R :=
  Spec.map (CommRingCat.ofHom (LaurentPolynomial.C (R := R)))

/-- The universal point of `𝔾_{m, Spec R}`, defined on the relative Laurent spectrum. -/
def universalPoint : Over.mk (laurentStructure R) ⟶ (Gm (Spec R)).X :=
  (relativeLaurentIso R).inv

/-- The universal point is the Laurent coordinate `T`. -/
theorem affinePointsEquiv_universalPoint :
    ((affinePointsEquiv (laurentStructure R) (universalPoint R) :
      (CommRingCat.of (LaurentPolynomial R))ˣ) : LaurentPolynomial R) =
      LaurentPolynomial.T 1 := by
  rw [← relativeLaurentIso_affinePointsEquiv_val (laurentStructure R) (universalPoint R)]
  have h : universalPoint R ≫ (relativeLaurentIso R).hom = 𝟙 _ :=
    (relativeLaurentIso R).inv_hom_id
  rw [h]
  change (Scheme.ΓSpecIso _).hom (((Scheme.ΓSpecIso _).inv ≫
    Scheme.Hom.appTop (𝟙 (Spec (CommRingCat.of (LaurentPolynomial R)))))
      (LaurentPolynomial.T 1)) = _
  simp

/-- Every point of `𝔾_{m, Spec R}` factors through the universal point. -/
theorem factor_universalPoint {T : Over (Spec R)} (x : T ⟶ (Gm (Spec R)).X) :
    (x ≫ (relativeLaurentIso R).hom) ≫ universalPoint R = x := by
  simp [universalPoint]

/-- Group-scheme homomorphisms out of `𝔾_{m, Spec R}` agree when they agree on the universal
point. -/
theorem hom_ext_universalPoint {G : GroupScheme (Spec R)} {φ ψ : (Gm (Spec R)).toGrp ⟶ G}
    (h : universalPoint R ≫ φ.hom.hom = universalPoint R ≫ ψ.hom.hom) : φ = ψ :=
  hom_ext_points fun T x => by
    rw [← factor_universalPoint R x]
    simp only [Category.assoc, h]

/-- The Laurent unit recording an endomorphism of `𝔾_{m, Spec R}`: its value on the universal
point. -/
def endUnit (φ : (Gm (Spec R)).toGrp ⟶ (Gm (Spec R)).toGrp) :
    (CommRingCat.of (LaurentPolynomial R))ˣ :=
  affinePointsEquiv (laurentStructure R) (universalPoint R ≫ φ.hom.hom)

theorem endUnit_injective : Function.Injective (endUnit R) := fun _ _ h =>
  hom_ext_universalPoint R ((affinePointsEquiv (laurentStructure R)).injective h)

/-- Integer multiplication on `𝔾_m` sends the coordinate `T` to `T ^ n`. -/
theorem endUnit_multiplication (n : ℤ) :
    ((endUnit R (multiplication (Gm (Spec R)).toGrp n) :
      (CommRingCat.of (LaurentPolynomial R))ˣ) : LaurentPolynomial R) =
      LaurentPolynomial.T n := by
  rw [endUnit, points_multiplication, map_zpow]
  have hT : affinePointsEquiv (laurentStructure R) (universalPoint R) =
      (relativeCoordUnit R : (CommRingCat.of (LaurentPolynomial R))ˣ) :=
    Units.ext (affinePointsEquiv_universalPoint R)
  rw [hT]
  exact relativeCoordUnit_zpow_val R n

/-- Evaluation of Laurent polynomials at `T = 1`. -/
abbrev evalOne : CommRingCat.of (LaurentPolynomial R) ⟶ R :=
  CommRingCat.ofHom (LaurentPolynomial.eval₂ (RingHom.id R) 1)

/-- The universal point specialises to the identity point at `T = 1`. -/
theorem affineMap_evalOne_universalPoint :
    affineMap (evalOne R) (laurentStructure R) ≫ universalPoint R = 1 := by
  apply (affinePointsEquiv (Spec.map (evalOne R) ≫ laurentStructure R)).injective
  rw [affinePointsEquiv_naturality, map_one]
  apply Units.ext
  change LaurentPolynomial.eval₂ (RingHom.id R) 1
    ((affinePointsEquiv (laurentStructure R) (universalPoint R) :
      (CommRingCat.of (LaurentPolynomial R))ˣ) : LaurentPolynomial R) = 1
  rw [affinePointsEquiv_universalPoint, LaurentPolynomial.eval₂_T]
  simp

/-- The constant coefficient of the Laurent unit of an endomorphism is `1`. -/
theorem evalOne_endUnit (φ : (Gm (Spec R)).toGrp ⟶ (Gm (Spec R)).toGrp) :
    Units.map (evalOne R).hom.toMonoidHom (endUnit R φ) = 1 := by
  rw [endUnit, ← affinePointsEquiv_naturality, ← Category.assoc,
    affineMap_evalOne_universalPoint, MonObj.one_comp, map_one]

variable [IsDomain R]

/-- Over an integral domain, every endomorphism of `𝔾_{m, Spec R}` is multiplication by an
integer. -/
theorem exists_eq_multiplication (φ : (Gm (Spec R)).toGrp ⟶ (Gm (Spec R)).toGrp) :
    ∃ n : ℤ, φ = multiplication (Gm (Spec R)).toGrp n := by
  obtain ⟨c, n, hcn⟩ := laurent_unit_eq_C_mul_T (R := R) (endUnit R φ)
  have hc : (c : R) = 1 := by
    have h := congrArg (fun w : Rˣ => (w : R)) (evalOne_endUnit R φ)
    change LaurentPolynomial.eval₂ (RingHom.id R) 1
      ((endUnit R φ : (CommRingCat.of (LaurentPolynomial R))ˣ) : LaurentPolynomial R) = 1 at h
    rw [hcn, map_mul, LaurentPolynomial.eval₂_C, LaurentPolynomial.eval₂_T] at h
    simpa using h
  refine ⟨n, endUnit_injective R (Units.ext ?_)⟩
  rw [hcn, hc, endUnit_multiplication, map_one, one_mul]

/-- Over an integral domain, integer multiplication on `𝔾_m` determines the integer. -/
theorem multiplication_injective :
    Function.Injective (multiplication (Gm (Spec R)).toGrp) := fun m n h => by
  have h' := congrArg (fun φ => ((endUnit R φ : (CommRingCat.of (LaurentPolynomial R))ˣ) :
    LaurentPolynomial R)) h
  simp only [endUnit_multiplication] at h'
  exact AddMonoidAlgebra.single_left_injective (one_ne_zero (α := R)) h'

omit [IsDomain R] in
/-- Over the spectrum of an integral domain, integer multiplication is a bijection onto the
endomorphisms of `𝔾_m`. -/
theorem endomorphismsStatement : EndomorphismsStatement.{u} := fun R _ =>
  ⟨multiplication_injective R, fun φ => (exists_eq_multiplication R φ).imp fun _ h => h.symm⟩

end Gm

end Langlands.GroupScheme
