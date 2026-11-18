import Langlands.GroupScheme.ArtinianUniformExponent
import Langlands.GroupScheme.Lie.BaseChange

/-! # Proof of the Artinian-local uniform exponent theorem -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.ArtinianUniformExponent

variable {R : Type u} [CommRing R]

/-- Testing the chosen affine universal point suffices for all test schemes. -/
theorem all_points_of_affine (G : GroupScheme (Spec (CommRingCat.of R)))
    [IsAffineHom G.X.hom] (n : ℕ)
    (h : ∀ (A : Type u) [CommRing A] [Algebra R A]
      (x : Lie.AffinePoints G A), x ^ n = 1) :
    ∀ (T : Over (Spec (CommRingCat.of R))) (x : T ⟶ G.X), x ^ n = 1 := by
  have hcoord := h (Lie.coordinateAlgebra G) (Lie.coordinateIso G).hom
  intro T x
  have hx : x = (x ≫ (Lie.coordinateIso G).inv) ≫ (Lie.coordinateIso G).hom := by simp
  rw [hx, ← MonObj.comp_pow, hcoord, MonObj.comp_one]

/-- Reduction to the residue fibre gives a uniform exponent modulo the extended
maximal ideal of every coefficient algebra. -/
theorem exists_residue_exponent [IsLocalRing R]
    (G : GroupScheme (Spec (CommRingCat.of R))) [IsFinite G.X.hom] :
    ∃ n : ℕ, 0 < n ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A] (x : Lie.AffinePoints G A),
        Lie.affineMap G (Ideal.Quotient.mkₐ R
          ((IsLocalRing.maximalIdeal R).map (algebraMap R A))) (x ^ n) = 1 := by
  let k := IsLocalRing.ResidueField R
  let b := algebraBaseMap R k
  let G₀ := (GroupScheme.baseChange b).obj G
  have : IsFinite G₀.X.hom := by
    change IsFinite (pullback.snd G.X.hom b)
    infer_instance
  obtain ⟨n, hn, hpow⟩ := finiteGroupSchemeUniformExponent k G₀ inferInstance
  refine ⟨n, hn, ?_⟩
  intro A _ _ x
  let I := (IsLocalRing.maximalIdeal R).map (algebraMap R A)
  let : Algebra k (A ⧸ I) := Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  let : IsScalarTower R k (A ⧸ I) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let e := Lie.affineBaseChangeEquiv R k G (A ⧸ I)
  let y := Lie.affineMap G (Ideal.Quotient.mkₐ R I) x
  have h := congrArg e (hpow _ (e.symm y))
  simpa only [map_pow, map_one, MulEquiv.apply_symm_apply] using h

/-- A chosen positive exponent on the residue fibre, used in both characteristic branches. -/
def residueExponent [IsLocalRing R]
    (G : GroupScheme (Spec (CommRingCat.of R))) [IsFinite G.X.hom] : ℕ :=
  (exists_residue_exponent G).choose

theorem residueExponent_pos [IsLocalRing R]
    (G : GroupScheme (Spec (CommRingCat.of R))) [IsFinite G.X.hom] :
    0 < residueExponent G := (exists_residue_exponent G).choose_spec.1

theorem residueExponent_kills [IsLocalRing R]
    (G : GroupScheme (Spec (CommRingCat.of R))) [IsFinite G.X.hom]
    (A : Type u) [CommRing A] [Algebra R A] (x : Lie.AffinePoints G A) :
    Lie.affineMap G (Ideal.Quotient.mkₐ R
      ((IsLocalRing.maximalIdeal R).map (algebraMap R A))) (x ^ residueExponent G) = 1 :=
  (exists_residue_exponent G).choose_spec.2 A x

/-- In positive residue characteristic, a power of that characteristic kills
all the successive nilpotent coefficient kernels. -/
theorem exists_exponent_of_charP [IsLocalRing R] [IsArtinianRing R]
    (G : GroupScheme (Spec (CommRingCat.of R))) [IsFinite G.X.hom]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField R) p] :
    ∃ n : ℕ, 0 < n ∧ ∀ (T : Over (Spec (CommRingCat.of R))) (x : T ⟶ G.X),
      x ^ n = 1 := by
  let n := residueExponent G
  have hn : 0 < n := residueExponent_pos G
  have hpow := residueExponent_kills G
  obtain ⟨N, hN⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal R).mp inferInstance
  have hN' : (IsLocalRing.maximalIdeal R) ^ (N + 1) = ⊥ := by
    simp [pow_succ, hN]
  have hpR : (p : R) ∈ IsLocalRing.maximalIdeal R := by
    apply (IsLocalRing.residue_eq_zero_iff _).mp
    rw [map_natCast, CharP.cast_eq_zero]
  refine ⟨n * p ^ N, Nat.mul_pos hn (pow_pos (Fact.out : p.Prime).pos N),
    all_points_of_affine G _ ?_⟩
  intro A _ _ x
  let I := (IsLocalRing.maximalIdeal R).map (algebraMap R A)
  have hpA : (p : A) ∈ I := by
    simpa only [map_natCast] using Ideal.mem_map_of_mem (algebraMap R A) hpR
  have hI : I ^ (N + 1) = ⊥ := by
    dsimp only [I]
    rw [← Ideal.map_pow, hN', Ideal.map_bot]
  rw [pow_mul]
  exact NilpotentCoefficientPowers.pow_eq_one G I p N hpA hI (x ^ n) (hpow A x)

/-- In residue characteristic zero, formal unramifiedness makes residue
exponents lift unchanged through the nilpotent coefficient ideal. -/
theorem exists_exponent_of_charZero [IsLocalRing R] [IsArtinianRing R]
    (G : GroupScheme (Spec (CommRingCat.of R))) [IsFinite G.X.hom]
    [CharZero (IsLocalRing.ResidueField R)] :
    ∃ n : ℕ, 0 < n ∧ ∀ (T : Over (Spec (CommRingCat.of R))) (x : T ⟶ G.X),
      x ^ n = 1 := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : Module.Finite R (AffineCoordinates.hopfAlgebra G) := finite_hopfAlgebra G
  have : Algebra.FormallyUnramified R (AffineCoordinates.hopfAlgebra G) :=
    formallyUnramified_hopf R (AffineCoordinates.hopfAlgebra G)
  have : Algebra.FormallyUnramified R (Lie.coordinateAlgebra G) :=
    Algebra.FormallyUnramified.of_equiv (coordinatesEquiv G)
  let n := residueExponent G
  have hn : 0 < n := residueExponent_pos G
  have hpow := residueExponent_kills G
  have hm : IsNilpotent (IsLocalRing.maximalIdeal R) :=
    (isArtinianRing_iff_isNilpotent_maximalIdeal R).mp inferInstance
  refine ⟨n, hn, all_points_of_affine G n ?_⟩
  intro A _ _ x
  let I := (IsLocalRing.maximalIdeal R).map (algebraMap R A)
  have hI : IsNilpotent I := hm.map (Ideal.mapHom _)
  apply (Lie.pointCoordinates G).injective
  apply Algebra.FormallyUnramified.lift_unique I hI
  rw [← Lie.pointCoordinates_naturality G (Ideal.Quotient.mkₐ R I) (x ^ n),
    ← Lie.pointCoordinates_naturality G (Ideal.Quotient.mkₐ R I) 1, map_one]
  exact congrArg (Lie.pointCoordinates G) (hpow A x)

/-- The Artinian-local uniform exponent assertion in every universe. -/
theorem artinianUniformExponent : Statement.{u} := by
  intro R _ _ _ G hqc hqf
  let := hqc
  let := hqf
  have : IsLocallyArtinian (Spec (CommRingCat.of R)) :=
    Scheme.isLocallyArtinianScheme_Spec.mpr inferInstance
  have : IsFinite G.X.hom := IsFinite.of_locallyQuasiFinite G.X.hom
  rcases CharP.exists' (IsLocalRing.ResidueField R) with hzero | ⟨p, hp, hchar⟩
  · let := hzero
    exact exists_exponent_of_charZero G
  · let := hp
    let := hchar
    exact exists_exponent_of_charP G p

end Langlands.GroupScheme.ArtinianUniformExponent
