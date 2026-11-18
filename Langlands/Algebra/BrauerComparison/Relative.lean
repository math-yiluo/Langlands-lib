import Langlands.Algebra.TensorCubeScalarDefect
import Langlands.ClassFieldTheory.Local.Cohomology
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-! # The relative Brauer class of a matrix splitting -/

noncomputable section

open CategoryTheory Matrix
open scoped TensorProduct

universe u v

namespace Langlands.BrauerComparison

open ClassFieldTheory.Local (unitsRepresentation relativeCohomology)
open ScalarTwoCocycle (IsTwoCocycle IsCoboundary coboundary)
open CentralSimple CentralSimple.SemilinearGaloisAction

attribute [local instance] coefficientGLAction

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/-- A unit-valued factor set gives an ordinary Mathlib two-cocycle. -/
def unitCocycle (c : Gal(L/K) → Gal(L/K) → Lˣ) (hc : IsTwoCocycle c) :
    groupCohomology.cocycles₂ (unitsRepresentation K L) :=
  ⟨fun st => Additive.ofMul (c st.1 st.2), (groupCohomology.mem_cocycles₂_iff _).2
    (fun s t r => by
      change Additive.ofMul (c (s * t) r * c s t) =
        Additive.ofMul ((s • c t r) * c s (t * r))
      rw [mul_comm (c (s * t) r), hc s t r])⟩

/-- The class of a unit-valued factor set in ordinary relative cohomology. -/
def unitClass (c : Gal(L/K) → Gal(L/K) → Lˣ) (hc : IsTwoCocycle c) :
    relativeCohomology K L 2 :=
  groupCohomology.H2π (unitsRepresentation K L) (unitCocycle c hc)

@[simp] theorem unitCocycle_apply (c : Gal(L/K) → Gal(L/K) → Lˣ)
    (hc : IsTwoCocycle c) (s t : Gal(L/K)) :
    unitCocycle c hc (s, t) = Additive.ofMul (c s t) := rfl

private theorem coboundary_eq_d₁₂ (b : Gal(L/K) → Lˣ) (s t : Gal(L/K)) :
    Additive.ofMul (coboundary b s t) =
      groupCohomology.d₁₂ (unitsRepresentation K L) (Additive.ofMul ∘ b) (s, t) := by
  rw [groupCohomology.d₁₂_hom_apply]
  change coboundary b s t = (s • b t) * (b (s * t))⁻¹ * b s
  unfold coboundary
  ac_rfl

/-- The class vanishes precisely when the factor set is a unit coboundary. -/
theorem unitClass_eq_zero_iff (c : Gal(L/K) → Gal(L/K) → Lˣ) (hc : IsTwoCocycle c) :
    unitClass c hc = 0 ↔ IsCoboundary c := by
  rw [unitClass, groupCohomology.H2π_eq_zero_iff]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨Additive.toMul ∘ b, fun s t => ?_⟩
    apply Additive.ofMul.injective
    have h := congrFun hb (s, t)
    exact h.symm.trans (coboundary_eq_d₁₂ (Additive.toMul ∘ b) s t).symm
  · rintro ⟨b, hb⟩
    refine ⟨Additive.ofMul ∘ b, funext fun st => ?_⟩
    rcases st with ⟨s, t⟩
    exact (coboundary_eq_d₁₂ b s t).symm.trans (congrArg Additive.ofMul (hb s t).symm)

/-- Multiplying a factor set by a scalar coboundary leaves its class unchanged. -/
theorem unitClass_eq_of_coboundary_mul
    {c d : Gal(L/K) → Gal(L/K) → Lˣ} (hc : IsTwoCocycle c) (hd : IsTwoCocycle d)
    (b : Gal(L/K) → Lˣ) (hb : ∀ s t, c s t = coboundary b s t * d s t) :
    unitClass c hc = unitClass d hd := by
  apply (groupCohomology.H2π_eq_iff _ _).2
  refine ⟨Additive.ofMul ∘ b, funext fun st => ?_⟩
  rcases st with ⟨s, t⟩
  rw [← coboundary_eq_d₁₂]
  change coboundary b s t = c s t * (d s t)⁻¹
  rw [hb, mul_inv_cancel_right]

/-- A product of unit-valued factor sets represents the sum of the classes. -/
theorem unitClass_mul {c d : Gal(L/K) → Gal(L/K) → Lˣ}
    (hc : IsTwoCocycle c) (hd : IsTwoCocycle d)
    (hcd : IsTwoCocycle (fun s t => c s t * d s t)) :
    unitClass (fun s t => c s t * d s t) hcd = unitClass c hc + unitClass d hd := by
  unfold unitClass
  rw [← map_add]
  congr 1

/-- Every ordinary relative class has a unit-valued factor-set representative. -/
theorem exists_unitClass_eq (x : relativeCohomology K L 2) :
    ∃ (c : Gal(L/K) → Gal(L/K) → Lˣ) (hc : IsTwoCocycle c), unitClass c hc = x := by
  induction x using groupCohomology.H2_induction_on with
  | h z =>
    let c : Gal(L/K) → Gal(L/K) → Lˣ := fun s t => Additive.toMul (z (s, t))
    have hc : IsTwoCocycle c := by
      intro s t r
      rw [mul_comm (c s t)]
      exact congrArg Additive.toMul ((groupCohomology.mem_cocycles₂_iff _).1 z.2 s t r)
    refine ⟨c, hc, ?_⟩
    unfold unitClass
    congr 1

section MatrixDescent

variable {I : Type v} [Fintype I] [DecidableEq I] [Nonempty I]
variable {A : Type u} [Ring A] [Algebra K A]

/-- The cohomology class of the scalar defect of a semilinear matrix action. -/
def descentClass (ρ : SemilinearGaloisAction K L (Matrix I I L)) :
    relativeCohomology K L 2 := unitClass ρ.scalarDefect ρ.scalarDefect_isTwoCocycle

/-- The relative Brauer comparison on a supplied matrix splitting chart. -/
def relativeClass (e : L ⊗[K] A ≃ₐ[L] Matrix I I L) : relativeCohomology K L 2 :=
  descentClass (splittingChartIndexAction e)

omit [Nonempty I] in
/-- The defect satisfies Serre's factor-set formula in the actual general linear group. -/
theorem scalarDefect_formula (ρ : SemilinearGaloisAction K L (Matrix I I L))
    (s t : Gal(L/K)) :
    GeneralLinearGroup.scalar I (ρ.scalarDefect s t) =
      ρ.innerMatrix s * (s • ρ.innerMatrix t) * (ρ.innerMatrix (s * t))⁻¹ := by
  rw [ρ.innerMatrix_mul, mul_inv_cancel_right]

/-- For two lift families of the same action the defects differ by the
coboundary of their scalar ratio. -/
theorem exists_defect_ratio
    (P Q : Gal(L/K) → GL I L) (c d : Gal(L/K) → Gal(L/K) → Lˣ)
    (hP : ∀ s t, P s * (s • P t) = GeneralLinearGroup.scalar I (c s t) * P (s * t))
    (hQ : ∀ s t, Q s * (s • Q t) = GeneralLinearGroup.scalar I (d s t) * Q (s * t))
    (hconj : ∀ (s : Gal(L/K)) (X : Matrix I I L),
      (P s : Matrix I I L) * X.map s * (((P s)⁻¹ : GL I L) : Matrix I I L) =
      (Q s : Matrix I I L) * X.map s * (((Q s)⁻¹ : GL I L) : Matrix I I L)) :
    ∃ b : Gal(L/K) → Lˣ, ∀ s t, c s t = coboundary b s t * d s t := by
  let scalar := GeneralLinearGroup.scalar I (R := L)
  have hscalar (s : Gal(L/K)) : ∃ b : Lˣ, P s = scalar b * Q s := by
    obtain ⟨b, hb⟩ :=
      Langlands.LinearAlgebra.SpecialLinearConjugation.exists_unit_scalar_of_conjugation_eq_conjugation
        (P s) (Q s) (fun g => by
          apply Units.ext
          obtain ⟨X, hX⟩ := s.mapMatrix.surjective (g : Matrix I I L)
          change X.map s = (g : Matrix I I L) at hX
          simpa only [hX, Units.val_mul, SpecialLinearGroup.coe_GL_coe_matrix] using hconj s X)
    exact ⟨b, hb.trans (unit_scalar_central b (Q s)).symm.eq⟩
  choose b hb using hscalar
  refine ⟨b, fun s t => ?_⟩
  have he : c s t * b (s * t) = (b s * (s • b t)) * d s t := by
    apply unit_scalar_injective (I := I)
    change scalar (c s t * b (s * t)) = scalar ((b s * (s • b t)) * d s t)
    apply mul_right_cancel (b := Q (s * t))
    calc
      scalar (c s t * b (s * t)) * Q (s * t) = P s * (s • P t) := by
        rw [hP, hb (s * t), map_mul, mul_assoc]
      _ = scalar (b s * (s • b t)) * (Q s * (s • Q t)) := by
        rw [hb s, hb t, smul_mul', coefficientGLAction_scalar, map_mul]
        simp only [← mul_assoc]
        rw [mul_assoc (scalar (b s)), (unit_scalar_central (s • b t) (Q s)).symm.eq,
          ← mul_assoc]
      _ = _ := by
        rw [hQ]
        simp only [scalar, map_mul, mul_assoc]
  calc
    c s t = (c s t * b (s * t)) * (b (s * t))⁻¹ := by rw [mul_inv_cancel_right]
    _ = coboundary b s t * d s t := by rw [he, coboundary]; ac_rfl

/-- Any invertible lifts and unit factors for the given matrix action compute
its relative cohomology class. -/
theorem descentClass_eq_of_lifts (ρ : SemilinearGaloisAction K L (Matrix I I L))
    (P : Gal(L/K) → GL I L) (c : Gal(L/K) → Gal(L/K) → Lˣ)
    (hact : ∀ (s : Gal(L/K)) (X : Matrix I I L), ρ.act s X =
      (P s : Matrix I I L) * X.map s * (((P s)⁻¹ : GL I L) : Matrix I I L))
    (hP : ∀ s t, P s * (s • P t) = GeneralLinearGroup.scalar I (c s t) * P (s * t)) :
    descentClass ρ = unitClass c
      (ScalarTwoCocycle.isTwoCocycle_of_lifts (GeneralLinearGroup.scalar I)
        unit_scalar_injective unit_scalar_central coefficientGLAction_scalar P c hP) := by
  obtain ⟨b, hb⟩ := exists_defect_ratio ρ.innerMatrix P ρ.scalarDefect c
    ρ.innerMatrix_mul hP (fun s X => (ρ.act_eq_innerMatrix s X).symm.trans (hact s X))
  exact unitClass_eq_of_coboundary_mul _ _ b hb

/-- A chart change by conjugation preserves the class of its semilinear action. -/
theorem descentClass_eq_of_conjugation
    (ρ τ : SemilinearGaloisAction K L (Matrix I I L)) (U : GL I L)
    (h : ∀ (s : Gal(L/K)) (X : Matrix I I L),
      τ.act s ((U : Matrix I I L) * X * ((U⁻¹ : GL I L) : Matrix I I L)) =
        (U : Matrix I I L) * ρ.act s X * ((U⁻¹ : GL I L) : Matrix I I L)) :
    descentClass τ = descentClass ρ := by
  let Q : Gal(L/K) → GL I L := fun s => U * ρ.innerMatrix s * (s • U)⁻¹
  have hQ (s t : Gal(L/K)) : Q s * (s • Q t) =
      GeneralLinearGroup.scalar I (ρ.scalarDefect s t) * Q (s * t) := by
    dsimp only [Q]
    simp only [smul_mul', smul_inv', ← mul_smul]
    calc
      _ = U * (ρ.innerMatrix s * (s • ρ.innerMatrix t)) * ((s * t) • U)⁻¹ := by group
      _ = _ := by
        rw [ρ.innerMatrix_mul, ← mul_assoc U, (unit_scalar_central (ρ.scalarDefect s t) U).symm.eq]
        simp only [mul_assoc]
  have hact (s : Gal(L/K)) (X : Matrix I I L) : τ.act s X =
      (Q s : Matrix I I L) * X.map s * (((Q s)⁻¹ : GL I L) : Matrix I I L) := by
    have h' : τ.act s X =
        (U : Matrix I I L) *
          ρ.act s (((U⁻¹ : GL I L) : Matrix I I L) * X * (U : Matrix I I L)) *
          ((U⁻¹ : GL I L) : Matrix I I L) := by
      simpa [Matrix.mul_assoc] using
        h s (((U⁻¹ : GL I L) : Matrix I I L) * X * (U : Matrix I I L))
    rw [h', ρ.act_eq_innerMatrix]
    simp only [Q, Matrix.map_mul, _root_.mul_inv_rev, Units.val_mul, ← smul_inv',
      coefficientGLAction_coe, inv_inv, Matrix.mul_assoc]
  exact descentClass_eq_of_lifts τ Q ρ.scalarDefect hact hQ

/-- Two splitting charts with the same matrix indices determine the same class. -/
theorem relativeClass_eq (e f : L ⊗[K] A ≃ₐ[L] Matrix I I L) :
    relativeClass e = relativeClass f := by
  obtain ⟨U, hU⟩ := Langlands.MatrixAlgebra.exists_unit_conj_of_charts f e
  apply descentClass_eq_of_conjugation _ _ U
  intro s X
  obtain ⟨Y, rfl⟩ := f.surjective X
  rw [← hU, splittingChartIndexAction_apply, splittingChartIndexAction_apply, hU]

end MatrixDescent

end Langlands.BrauerComparison
