import Langlands.AlgebraicGeometry.ProjectiveSpace.UnitChart

/-! # Actual projective coordinate lines on arbitrary schemes -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry HomogeneousLocalization

namespace Langlands.AlgebraicGeometry.ProjectiveSpace.CoordinateLines

open GlobalCoordinates

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R] (n : ℕ) (X : Scheme.{u}) [Algebra R Γ(X, ⊤)]

local notation "𝒜" => projectiveSpaceGrading R n

/-- The homogeneous coordinate homomorphism of a coordinate basis vector. -/
def basisEval (j : Fin (n + 1)) : ProjectiveCoordinateRing R n →+* Γ(X, ⊤) :=
  MvPolynomial.eval₂Hom (algebraMap R Γ(X, ⊤)) (Pi.single j 1)

@[simp] theorem basisEval_X (j i : Fin (n + 1)) :
    basisEval (R := R) n X j (MvPolynomial.X i : ProjectiveCoordinateRing R n) = (Pi.single j 1 : Fin (n + 1) → Γ(X, ⊤)) i := by
  simp [basisEval]

@[simp] theorem basisEval_C (j : Fin (n + 1)) (r : R) :
    basisEval (R := R) n X j (MvPolynomial.C r : ProjectiveCoordinateRing R n) = algebraMap R Γ(X, ⊤) r := by
  simp [basisEval]

/-- A basis vector supplies homogeneous coordinates generating the unit ideal. -/
theorem basisEval_primitive (j : Fin (n + 1)) :
    (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map (basisEval (R := R) n X j) = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  have hmem := Ideal.mem_map_of_mem (basisEval (R := R) n X j)
    (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 Nat.one_pos
      (projectiveSpace_X_mem R n j))
  simpa using hmem

/-- The actual projective morphism represented by a coordinate basis line. -/
def basisPoint (j : Fin (n + 1)) : X ⟶ ProjectiveSpace R n :=
  Proj.fromOfGlobalSections 𝒜 (basisEval (R := R) n X j) (basisEval_primitive n X j)

/-- A global function with the whole scheme as its unit open is a global unit. -/
theorem isUnit_of_basicOpen_eq_top (f : Γ(X, ⊤)) (hf : X.basicOpen f = ⊤) : IsUnit f := by
  apply X.toRingedSpace.isUnit_of_isUnit_germ ⊤ f
  intro x hx
  exact (X.mem_basicOpen f x hx).mp (by rw [hf]; trivial)

/-- A basis-point coordinate chart is the whole source scheme. -/
theorem basisPoint_preimage_coordinate (j : Fin (n + 1)) :
    basisPoint (R := R) n X j ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X j) = ⊤ := by
  rw [basisPoint, Proj.fromOfGlobalSections_preimage_basicOpen 𝒜 _ _ Nat.one_pos
    (projectiveSpace_X_mem R n j)]
  simp

/-- Equality with the actual coordinate basis point is precisely multiplication
of the homogeneous coordinates by a global scalar unit, on every scheme. -/
theorem eq_basisPoint_iff (j : Fin (n + 1))
    (f : ProjectiveCoordinateRing R n →+* Γ(X, ⊤))
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤)
    (hc : ∀ r : R, f (MvPolynomial.C r) = algebraMap R Γ(X, ⊤) r) :
    Proj.fromOfGlobalSections 𝒜 f hf = basisPoint (R := R) n X j ↔
      ∃ u : Γ(X, ⊤)ˣ, ∀ i : Fin (n + 1),
        f (MvPolynomial.X i) = (u : Γ(X, ⊤)) * (Pi.single j 1 : Fin (n + 1) → Γ(X, ⊤)) i := by
  have hbunit : IsUnit (basisEval (R := R) n X j (MvPolynomial.X j)) := by simp
  have hbratio (i : Fin (n + 1)) :
      unitChartRingMap n (basisEval (R := R) n X j) (MvPolynomial.X j) hbunit
        (_root_.AlgebraicGeometry.ProjSpace.ratio R n j i) = (Pi.single j 1 : Fin (n + 1) → Γ(X, ⊤)) i := by
    simpa using unitChartRingMap_ratio_mul n (basisEval (R := R) n X j) j i hbunit
  constructor
  · intro h
    have htop : X.basicOpen (f (MvPolynomial.X j)) = ⊤ := by
      rw [← Proj.fromOfGlobalSections_preimage_basicOpen 𝒜 f hf Nat.one_pos
        (projectiveSpace_X_mem R n j), h, basisPoint_preimage_coordinate]
    have hunit := isUnit_of_basicOpen_eq_top X (f (MvPolynomial.X j)) htop
    have heq := (fromOfGlobalSections_eq_iff_unitChart n f (basisEval (R := R) n X j) hf
      (basisEval_primitive n X j) Nat.one_pos (MvPolynomial.X j)
      (projectiveSpace_X_mem R n j) hunit hbunit).mp h
    obtain ⟨u, hu⟩ := hunit
    refine ⟨u, fun i => ?_⟩
    calc
      f (MvPolynomial.X i) =
          unitChartRingMap n f (MvPolynomial.X j) ⟨u, hu⟩
            (_root_.AlgebraicGeometry.ProjSpace.ratio R n j i) * f (MvPolynomial.X j) :=
        (unitChartRingMap_ratio_mul n f j i ⟨u, hu⟩).symm
      _ = (Pi.single j 1 : Fin (n + 1) → Γ(X, ⊤)) i * f (MvPolynomial.X j) := by rw [heq, hbratio]
      _ = (u : Γ(X, ⊤)) * (Pi.single j 1 : Fin (n + 1) → Γ(X, ⊤)) i := by rw [← hu, mul_comm]
  · rintro ⟨u, hu⟩
    have hunit : IsUnit (f (MvPolynomial.X j)) := by
      simpa only [hu j, Pi.single_eq_same, mul_one] using u.isUnit
    apply (fromOfGlobalSections_eq_iff_unitChart n f (basisEval (R := R) n X j) hf
      (basisEval_primitive n X j) Nat.one_pos (MvPolynomial.X j)
      (projectiveSpace_X_mem R n j) hunit hbunit).mpr
    apply unitChartRingMap_ext n f (basisEval (R := R) n X j) j hunit hbunit hc (basisEval_C n X j)
    intro i
    apply hunit.mul_left_inj.mp
    rw [unitChartRingMap_ratio_mul, hbratio, hu i, hu j, Pi.single_eq_same, mul_one]
    exact mul_comm _ _

/-- Basis-coordinate evaluation commutes with extending the coefficient ring. -/
theorem basisEval_eq_eval (j : Fin (n + 1)) (a : ProjectiveCoordinateRing R n) :
    basisEval (R := R) n X j a =
      algebraMap R Γ(X, ⊤) (MvPolynomial.eval (Pi.single j 1 : Fin (n + 1) → R) a) := by
  have h : basisEval (R := R) n X j = (algebraMap R Γ(X, ⊤)).comp
      (MvPolynomial.eval (Pi.single j 1 : Fin (n + 1) → R)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro i
      by_cases hi : i = j
      · subst i
        simp
      · simp [hi]
  exact DFunLike.congr_fun h a

/-- The actual polynomial projective action fixes a basis section exactly when
its basis vector is multiplied by a unit of global functions. -/
theorem basisPoint_linearAction_eq_iff (j : Fin (n + 1))
    (e : (Fin (n + 1) → R) ≃ₗ[R] (Fin (n + 1) → R)) :
    basisPoint (R := R) n X j ≫ linearAction R n e = basisPoint (R := R) n X j ↔
      ∃ u : Γ(X, ⊤)ˣ, ∀ i : Fin (n + 1),
        algebraMap R Γ(X, ⊤) (e (Pi.single j 1) i) =
          (u : Γ(X, ⊤)) * (Pi.single j 1 : Fin (n + 1) → Γ(X, ⊤)) i := by
  let g := gradedLinearSubstitution R n e.toLinearMap
  let f := basisEval (R := R) n X j
  have hg := irrelevant_le_map_gradedLinearSubstitution R n e
  have hf := basisEval_primitive (R := R) n X j
  have hfg : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map (f.comp g.toRingHom) = ⊤ := by
    apply top_unique
    calc
      ⊤ = (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f := hf.symm
      _ ≤ ((HomogeneousIdeal.irrelevant 𝒜).toIdeal.map g.toRingHom).map f :=
        Ideal.map_mono hg
      _ = (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map (f.comp g.toRingHom) := Ideal.map_map _ _
  have hc (r : R) : (f.comp g.toRingHom) (MvPolynomial.C r) = algebraMap R Γ(X, ⊤) r := by
    simp [f, g, gradedLinearSubstitution_apply]
  have hXi (i : Fin (n + 1)) :
      (f.comp g.toRingHom) (MvPolynomial.X i) =
        algebraMap R Γ(X, ⊤) (e (Pi.single j 1) i) := by
    change basisEval (R := R) n X j (linearSubstitution R n e.toLinearMap (MvPolynomial.X i)) = _
    rw [basisEval_eq_eval, linearSubstitution_X, eval_linearFormPolynomialEquiv]
    rfl
  change Proj.fromOfGlobalSections 𝒜 f hf ≫ Proj.map g hg = basisPoint (R := R) n X j ↔ _
  rw [← fromOfGlobalSections_comp_gradedMap n g hg f hf hfg,
    eq_basisPoint_iff n X j (f.comp g.toRingHom) hfg hc]
  simp only [hXi]

end Langlands.AlgebraicGeometry.ProjectiveSpace.CoordinateLines
