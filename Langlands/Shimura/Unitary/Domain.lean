import Langlands.Shimura.Unitary.Signature
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Algebra.Algebra.Pi
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Topology.Algebra.Group.Quotient

/-! # Concrete archimedean homomorphisms and their conjugacy domains -/

universe u v

namespace Langlands.Shimura

namespace AlgebraInvolution

variable {A : Type u} [Ring A] [Algebra ℝ A]

/-- An actual complex algebra homomorphism with its involution certificate. -/
structure ComplexHom (σ : AlgebraInvolution ℝ A) where
  hom : ℂ →ₐ[ℝ] A
  star_compatible (z : ℂ) : σ (hom z) = hom (star z)

namespace ComplexHom

variable {σ : AlgebraInvolution ℝ A}

/-- The norm-square multiplier of a nonzero complex scalar, as a real unit. -/
def normSqUnits : ℂˣ →* ℝˣ := Units.map Complex.normSq.toMonoidHom

/-- The group homomorphism obtained from the genuine complex algebra map. -/
def toSimilitudes (h : ComplexHom σ) : ℂˣ →* σ.similitudes where
  toFun z := ⟨(Units.map h.hom.toMonoidHom z, normSqUnits z), by
    rw [σ.mem_similitudes_iff]
    change h.hom (z : ℂ) * σ (h.hom (z : ℂ)) =
      algebraMap ℝ A (Complex.normSq (z : ℂ))
    rw [h.star_compatible, ← _root_.map_mul]
    simpa only [Complex.star_def, Complex.mul_conj] using
      h.hom.map_coe_real_complex (Complex.normSq (z : ℂ))⟩
  map_one' := Subtype.ext (Prod.ext (_root_.map_one _) (_root_.map_one _))
  map_mul' z w := Subtype.ext (Prod.ext (_root_.map_mul _ z w) (_root_.map_mul _ z w))

@[simp] theorem toSimilitudes_multiplier (h : ComplexHom σ) (z : ℂˣ) :
    σ.multiplier (h.toSimilitudes z) = normSqUnits z := rfl

theorem toSimilitudes_multiplier_pos (h : ComplexHom σ) (z : ℂˣ) :
    0 < (σ.multiplier (h.toSimilitudes z) : ℝ) :=
  Complex.normSq_pos.mpr z.ne_zero

end ComplexHom
end AlgebraInvolution

/-- The corrected Harris homomorphism at a place of signature `(r,n-r)`:
conjugation on the positive block and identity on the negative block. -/
noncomputable def correctedComplexHom (n r : ℕ) :
    ℂ →ₐ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  (Matrix.diagonalAlgHom (n := Fin n) (α := ℂ) ℝ).comp
    (AlgHom.pi fun i : Fin n =>
      if i.val < r then Complex.conjAe.toAlgHom else AlgHom.id ℝ ℂ)

@[simp] theorem correctedComplexHom_apply (n r : ℕ) (z : ℂ) :
    correctedComplexHom n r z =
      Matrix.diagonal (fun i : Fin n => if i.val < r then star z else z) := by
  ext i j
  simp [correctedComplexHom, Matrix.diagonal_apply]
  split_ifs <;> rfl

theorem signatureAdjoint_diagonal (n r : ℕ) (v : Fin n → ℂ) :
    signatureAdjoint n r (Matrix.diagonal v) = Matrix.diagonal (fun i => star (v i)) := by
  change signatureMatrix n r * star (Matrix.diagonal v) * signatureMatrix n r = _
  change signatureMatrix n r * (Matrix.diagonal v).conjTranspose * signatureMatrix n r = _
  rw [Matrix.diagonal_conjTranspose]
  simp only [signatureMatrix, Matrix.diagonal_mul_diagonal]
  apply congrArg Matrix.diagonal
  funext i
  split_ifs <;> simp

/-- The corrected homomorphism with its proved adjoint compatibility. -/
noncomputable def correctedHom (n r : ℕ) :
    AlgebraInvolution.ComplexHom (signatureAdjoint n r) where
  hom := correctedComplexHom n r
  star_compatible z := by
    rw [correctedComplexHom_apply, signatureAdjoint_diagonal, correctedComplexHom_apply]
    apply congrArg Matrix.diagonal
    funext i
    split_ifs <;> simp

/-- A product of actual algebra involutions, used for the archimedean factors. -/
def AlgebraInvolution.pi {I : Type v} {A : I → Type u}
    [∀ i, Ring (A i)] [∀ i, Algebra ℝ (A i)]
    (σ : ∀ i, AlgebraInvolution ℝ (A i)) : AlgebraInvolution ℝ (∀ i, A i) where
  linear :=
    { toFun x i := σ i (x i)
      map_add' x y := by funext i; exact (σ i).apply_add _ _
      map_smul' r x := by funext i; exact (σ i).apply_smul r _ }
  map_one := by funext i; exact (σ i).apply_one
  map_mul x y := by funext i; exact (σ i).apply_mul _ _
  involutive x := by funext i; exact (σ i).apply_apply _

/-- One factor has signature `(n-1,1)`; every other factor is definite. -/
noncomputable def harrisArchimedeanInvolution (n : ℕ) (I : Type v)
    [DecidableEq I] (distinguished : I) :
    AlgebraInvolution ℝ (I → Matrix (Fin n) (Fin n) ℂ) :=
  AlgebraInvolution.pi fun i => signatureAdjoint n (if i = distinguished then n - 1 else n)

/-- The corrected homomorphism on all archimedean factors has a single
common norm-square multiplier. -/
noncomputable def harrisArchimedeanHom (n : ℕ) (I : Type v)
    [DecidableEq I] (distinguished : I) :
    AlgebraInvolution.ComplexHom (harrisArchimedeanInvolution n I distinguished) where
  hom := AlgHom.pi fun i => correctedComplexHom n (if i = distinguished then n - 1 else n)
  star_compatible z := by
    funext i
    exact (correctedHom n (if i = distinguished then n - 1 else n)).star_compatible z

section Conjugacy

variable (H : Type u) (G : Type v) [Group H] [Group G]

/-- Actual homomorphisms with the conjugation action distinguished from any
other possible action on a homomorphism space. -/
@[ext] structure ConjugationHom where
  hom : H →* G

namespace ConjugationHom

variable {H G}

instance : MulAction G (ConjugationHom H G) where
  smul g h := ⟨(MulAut.conj g).toMonoidHom.comp h.hom⟩
  one_smul h := by
    ext z
    change (1 : G) * h.hom z * 1⁻¹ = h.hom z
    simp
  mul_smul g g' h := by
    ext z
    change (g * g') * h.hom z * (g * g')⁻¹ =
      g * (g' * h.hom z * g'⁻¹) * g⁻¹
    simp [mul_assoc]

@[simp] theorem smul_hom_apply (g : G) (h : ConjugationHom H G) (z : H) :
    (g • h).hom z = g * h.hom z * g⁻¹ := rfl

theorem stabilizer_eq_centralizer (h : ConjugationHom H G) :
    MulAction.stabilizer G h = Subgroup.centralizer (Set.range h.hom) := by
  ext g
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro heq y hy
    obtain ⟨z, rfl⟩ := hy
    have hz : g * h.hom z * g⁻¹ = h.hom z := congrArg (fun f => f.hom z) heq
    exact ((mul_inv_eq_iff_eq_mul).mp hz).symm
  · intro hc
    ext z
    change g * h.hom z * g⁻¹ = h.hom z
    rw [← hc _ ⟨z, rfl⟩]
    simp [mul_assoc]

/-- The actual homogeneous-space quotient realizing the conjugacy domain. -/
def Domain (h : ConjugationHom H G) : Type v :=
  G ⧸ MulAction.stabilizer G h

instance (h : ConjugationHom H G) : MulAction G h.Domain :=
  inferInstanceAs (MulAction G (G ⧸ MulAction.stabilizer G h))

instance [TopologicalSpace G] (h : ConjugationHom H G) : TopologicalSpace h.Domain :=
  inferInstanceAs (TopologicalSpace (G ⧸ MulAction.stabilizer G h))

/-- A coset determines its actual conjugated group homomorphism. -/
def realization (h : ConjugationHom H G) : h.Domain → ConjugationHom H G :=
  MulAction.ofQuotientStabilizer G h

theorem realization_injective (h : ConjugationHom H G) :
    Function.Injective h.realization :=
  MulAction.injective_ofQuotientStabilizer G h

theorem realization_smul (h : ConjugationHom H G) (g : G) (x : h.Domain) :
    h.realization (g • x) = g • h.realization x :=
  MulAction.ofQuotientStabilizer_smul G h g x

/-- The homogeneous quotient is equivalent to the actual conjugacy orbit. -/
noncomputable def domainEquivOrbit (h : ConjugationHom H G) :
    h.Domain ≃ MulAction.orbit G h :=
  (MulAction.orbitEquivQuotientStabilizer G h).symm

end ConjugationHom
end Conjugacy

/-- The corrected Harris homomorphism, viewed in its real similitude group. -/
noncomputable def harrisDomainHom (n : ℕ) (I : Type v)
    [DecidableEq I] (distinguished : I) :
    ConjugationHom ℂˣ (harrisArchimedeanInvolution n I distinguished).similitudes :=
  ⟨(harrisArchimedeanHom n I distinguished).toSimilitudes⟩

/-- The actual conjugacy-domain homogeneous space of the standard
archimedean Harris model. -/
noncomputable def StandardArchimedeanDomain (n : ℕ) (I : Type v)
    [DecidableEq I] (distinguished : I) :=
  (harrisDomainHom n I distinguished).Domain

/-- The standard corrected domain indexed by the actual real embeddings of
the totally real number field, with the dimension bound of Harris's setting. -/
noncomputable def HarrisArchimedeanDomain (E : Type v)
    [Field E] [NumberField E] [NumberField.IsTotallyReal E]
    (n : ℕ) (_hn : 1 < n) (distinguished : E →+* ℝ) := by
  classical
  exact StandardArchimedeanDomain n (E →+* ℝ) distinguished

end Langlands.Shimura
