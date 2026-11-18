import Langlands.GroupScheme.Reductive.GaloisTwistWeights
import Langlands.GroupScheme.MatrixRepresentation.TitsAlgebra
import Langlands.GroupScheme.Rational.SplitHighestWeightClassificationProof
import Langlands.GroupScheme.Reductive.InnerStarWeights

/-! # The Tits class of a dominant star-fixed weight -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix TensorProduct

namespace Langlands.GroupScheme

namespace MatrixRepresentation

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- An intertwiner between two representations conjugates their coefficient matrices. -/
theorem coefficientMatrix_intertwines_of
    {ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n}
    {τ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) m}
    {C : Matrix m n K} (hC : ρ.Intertwines τ C) (φ : CharacterUnits.Coord G →ₗ[k] k) :
    C * coefficientMatrix ρ φ = coefficientMatrix τ φ * C := by
  rw [intertwines_iff_universalMatrix] at hC
  have h := congrArg (fun M => M.map (baseFunctional K φ)) hC
  simp only at h
  have hl : ∀ {p q r : Type} [Fintype q] (A : Matrix p q K)
      (M : Matrix q r (K ⊗[k] CharacterUnits.Coord G)),
      (A.map (algebraMap K (K ⊗[k] CharacterUnits.Coord G)) * M).map (baseFunctional K φ) =
        A * M.map (baseFunctional K φ) := by
    intro p q r _ A M
    ext i j
    simp only [Matrix.map_apply, Matrix.mul_apply, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  have hr : ∀ {p q r : Type} [Fintype q] (M : Matrix p q (K ⊗[k] CharacterUnits.Coord G))
      (A : Matrix q r K),
      (M * A.map (algebraMap K (K ⊗[k] CharacterUnits.Coord G))).map (baseFunctional K φ) =
        M.map (baseFunctional K φ) * A := by
    intro p q r _ M A
    ext i j
    simp only [Matrix.map_apply, Matrix.mul_apply, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  rw [hl, hr] at h
  exact h

/-- Conjugation `X ↦ C X D` by mutually inverse rectangular matrices, as an algebra
equivalence. -/
def conjAlgEquiv (C : Matrix m n K) (D : Matrix n m K) (hCD : C * D = 1) (hDC : D * C = 1) :
    Matrix n n K ≃ₐ[k] Matrix m m K where
  toFun X := C * X * D
  invFun Y := D * Y * C
  left_inv X := by
    change D * (C * X * D) * C = X
    rw [show D * (C * X * D) * C = (D * C) * X * (D * C) by simp only [Matrix.mul_assoc], hDC,
      Matrix.one_mul, Matrix.mul_one]
  right_inv Y := by
    change C * (D * Y * C) * D = Y
    rw [show C * (D * Y * C) * D = (C * D) * Y * (C * D) by simp only [Matrix.mul_assoc], hCD,
      Matrix.one_mul, Matrix.mul_one]
  map_mul' X Y := by
    change C * (X * Y) * D = (C * X * D) * (C * Y * D)
    rw [show (C * X * D) * (C * Y * D) = C * X * (D * C) * Y * D by
      simp only [Matrix.mul_assoc], hDC, Matrix.mul_one]
    simp only [Matrix.mul_assoc]
  map_add' X Y := by
    change C * (X + Y) * D = C * X * D + C * Y * D
    rw [Matrix.mul_add, Matrix.add_mul]
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, hCD]

/-- Conjugation by an intertwiner carries the Tits algebra of `ρ` onto that of `τ`. -/
theorem titsAlgebra_map_conjAlgEquiv
    {ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n}
    {τ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) m}
    {C : Matrix m n K} (hC : ρ.Intertwines τ C) (D : Matrix n m K) (hCD : C * D = 1)
    (hDC : D * C = 1) :
    (titsAlgebra ρ).map (conjAlgEquiv (k := k) C D hCD hDC).toAlgHom = titsAlgebra τ := by
  have hconj : ∀ φ, C * coefficientMatrix ρ φ * D = coefficientMatrix τ φ := by
    intro φ
    rw [coefficientMatrix_intertwines_of hC, Matrix.mul_assoc, hCD, Matrix.mul_one]
  rw [titsAlgebra, titsAlgebra, AlgHom.map_adjoin]
  congr 1
  ext Y
  constructor
  · rintro ⟨X, ⟨φ, rfl⟩, rfl⟩
    exact ⟨φ, (hconj φ).symm⟩
  · rintro ⟨φ, rfl⟩
    exact ⟨coefficientMatrix ρ φ, ⟨φ, rfl⟩, hconj φ⟩

/-- Isomorphic representations have isomorphic Tits algebras. -/
def titsAlgebraEquivOfIntertwines
    {ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n}
    {τ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) m}
    {C : Matrix m n K} (hC : ρ.Intertwines τ C) (D : Matrix n m K) (hCD : C * D = 1)
    (hDC : D * C = 1) : titsAlgebra ρ ≃ₐ[k] titsAlgebra τ :=
  ((conjAlgEquiv (k := k) C D hCD hDC).subalgebraMap (titsAlgebra ρ)).trans
    (Subalgebra.equivOfEq _ _ (titsAlgebra_map_conjAlgEquiv hC D hCD hDC))

end MatrixRepresentation

namespace GaloisPinningData

open MatrixRepresentation

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (d : GaloisPinningData k K G)

local instance titsDominantAffine :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

omit [LocallyOfFiniteType G.X.hom] in
theorem smul_eq_weightEquiv (e : d.toSplitPinning.rootDatum.Aut)
    (lam : characterLattice d.toSplitPinning.torus) : e • lam = e.weightEquiv lam :=
  rfl

theorem isUnit_of_bijective_mulVecLin {n : Type} [Fintype n] [DecidableEq n] {C : Matrix n n K}
    (h : Function.Bijective C.mulVecLin) : IsUnit C :=
  Matrix.isUnit_toLin'_iff.mp ((Module.End.isUnit_iff _).mpr h)

/-- A representation of star-fixed highest weight is isomorphic to each of its Galois twists. -/
theorem exists_intertwiner_galoisTwist {n : ℕ}
    {ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) (Fin n)}
    {lam : characterLattice d.toSplitPinning.torus}
    (hρ : d.toSplitPinning.IsHighestWeight ρ lam) (hfix : d.IsStarFixedWeight lam)
    (σ : K ≃ₐ[k] K) :
    ∃ C : Matrix (Fin n) (Fin n) K, ρ.Intertwines (galoisTwist σ ρ) C ∧ IsUnit C := by
  have hσ := d.isHighestWeight_galoisTwist σ hρ (by rw [smul_eq_weightEquiv]; exact hfix σ)
  obtain ⟨C, hC, hbij⟩ :=
    ((splitHighestWeightClassification K _ d.toSplitPinning).2.1 n n ρ (galoisTwist σ ρ) lam lam
      hρ hσ).mpr rfl
  exact ⟨C, hC, isUnit_of_bijective_mulVecLin hbij⟩

omit [LocallyOfFiniteType G.X.hom] in
/-- A representation with a highest weight is nonzero. -/
theorem nonempty_of_isHighestWeight {n : ℕ}
    {ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) (Fin n)}
    {lam : characterLattice d.toSplitPinning.torus}
    (hρ : d.toSplitPinning.IsHighestWeight ρ lam) : Nonempty (Fin n) := by
  have hle := Submodule.finrank_le (d.toSplitPinning.representationWeightSpace ρ lam)
  rw [hρ.2.2.1, Module.finrank_fin_fun] at hle
  exact ⟨⟨0, hle⟩⟩

variable [IsGalois k K]

/-- The Tits central simple algebra of a representation of star-fixed highest weight. -/
def titsCSAOf {n : ℕ}
    {ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) (Fin n)}
    {lam : characterLattice d.toSplitPinning.torus}
    (hρ : d.toSplitPinning.IsHighestWeight ρ lam) (hfix : d.IsStarFixedWeight lam) :
    CSA.{u, u} k :=
  haveI := d.nonempty_of_isHighestWeight hρ
  titsCSA ρ hρ.1 (SplitPinning.IsHighestWeight.intertwiner_eq_scalar d.toSplitPinning hρ)
    (fun σ => (d.exists_intertwiner_galoisTwist hρ hfix σ).choose)
    (fun σ => (d.exists_intertwiner_galoisTwist hρ hfix σ).choose_spec.2)
    (fun σ => (d.exists_intertwiner_galoisTwist hρ hfix σ).choose_spec.1)

/-- The Tits class of a dominant star-fixed weight. -/
def dominantTitsClass (lam : characterLattice d.toSplitPinning.torus)
    (hdom : d.toSplitPinning.IsDominantWeight lam) (hfix : d.IsStarFixedWeight lam) :
    BrauerGroup k :=
  Quotient.mk (Brauer.CSA_Setoid k)
    (d.titsCSAOf ((splitHighestWeightClassification K _ d.toSplitPinning).1 lam
      hdom).choose_spec.choose_spec hfix)

/-- Two representations of the same star-fixed highest weight have Brauer equivalent Tits
algebras. -/
theorem titsCSAOf_isBrauerEquivalent {n n' : ℕ}
    {ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) (Fin n)}
    {ρ' : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) (Fin n')}
    {lam : characterLattice d.toSplitPinning.torus}
    (hρ : d.toSplitPinning.IsHighestWeight ρ lam) (hρ' : d.toSplitPinning.IsHighestWeight ρ' lam)
    (hfix : d.IsStarFixedWeight lam) :
    IsBrauerEquivalent (d.titsCSAOf hρ hfix) (d.titsCSAOf hρ' hfix) := by
  obtain ⟨C, hC, hbij⟩ :=
    ((splitHighestWeightClassification K _ d.toSplitPinning).2.1 n n' ρ ρ' lam lam hρ
      hρ').mpr rfl
  let e := LinearEquiv.ofBijective C.mulVecLin hbij
  let D : Matrix (Fin n) (Fin n') K := LinearMap.toMatrix' e.symm.toLinearMap
  have hCD : C * D = 1 := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_one, Matrix.toLin'_toMatrix']
    refine LinearMap.ext fun v => ?_
    rw [LinearMap.comp_apply, LinearMap.id_apply]
    exact e.apply_symm_apply v
  have hDC : D * C = 1 := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_one, Matrix.toLin'_toMatrix']
    refine LinearMap.ext fun v => ?_
    rw [LinearMap.comp_apply, LinearMap.id_apply]
    exact e.symm_apply_apply v
  exact ⟨1, 1, one_ne_zero, one_ne_zero,
    ⟨(titsAlgebraEquivOfIntertwines (k := k) hC D hCD hDC).mapMatrix⟩⟩

/-- The class of any representation of a dominant star-fixed highest weight is the Tits class. -/
theorem dominantTitsClass_eq {lam : characterLattice d.toSplitPinning.torus}
    (hdom : d.toSplitPinning.IsDominantWeight lam) (hfix : d.IsStarFixedWeight lam) {n : ℕ}
    {ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) (Fin n)}
    (hρ : d.toSplitPinning.IsHighestWeight ρ lam) :
    d.dominantTitsClass lam hdom hfix =
      Quotient.mk (Brauer.CSA_Setoid k) (d.titsCSAOf hρ hfix) :=
  Quotient.sound (d.titsCSAOf_isBrauerEquivalent _ hρ hfix)

end GaloisPinningData

end Langlands.GroupScheme
