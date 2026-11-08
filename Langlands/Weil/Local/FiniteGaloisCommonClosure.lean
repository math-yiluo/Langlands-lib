import Langlands.Galois.Local.TotallyRamifiedSolvabilityProof
import Langlands.Weil.Local.FiniteGaloisTowerConstruction
import Langlands.ClassFieldTheory.Local.UnramifiedExtensionDegreeProof

/-! # A finite Galois common closure with an unramified extension of the same degree -/

noncomputable section

namespace Langlands.Weil.Local.FiniteGaloisTower

universe u

open LocalClassField ClassFieldTheory.Local

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

section Intermediate

variable (M : FiniteIntermediateExtension F.Carrier)

local notation "MP" => M.asPadicField (p := p)

local instance : Algebra (Padic p) M.field := (MP).algebra

/-- A Galois intermediate field is Galois for the algebra of its literal inclusion. -/
theorem intermediateEmbedding_isGalois [IsGalois F.Carrier M.field] :
    letI := extensionAlgebra F MP (intermediateEmbedding F M)
    IsGalois F.Carrier (MP).Carrier := by
  rw [extensionAlgebra_intermediateEmbedding]
  infer_instance

/-- For a normal intermediate field, the published chosen image of its literal inclusion
lies in the field itself. -/
theorem extensionIntermediateField_intermediateEmbedding_le [Normal F.Carrier M.field] :
    extensionIntermediateField F MP (intermediateEmbedding F M) ≤ M.field := by
  intro y hy
  obtain ⟨x, rfl⟩ := (mem_extensionIntermediateField F MP (intermediateEmbedding F M) y).mp hy
  have hx : AlgEquiv.toAlgHom (intermediateClosureCorrection F M)⁻¹
      (x : AlgebraicClosure F.Carrier) =
        extensionFieldEmbedding F MP (intermediateEmbedding F M) x := by
    rw [← intermediateClosureCorrection_fieldEmbedding F M x]
    exact (intermediateClosureCorrection F M).symm_apply_apply _
  rw [← hx]
  exact absoluteGalois_mem_of_normal F M _ x.property

end Intermediate

section Tower

variable (E : PadicField.{u} p) (f : F.Carrier →ₐ[Padic p] E.Carrier)

/-- The image of a Galois extension in the closure is a Galois intermediate field. -/
theorem extensionIntermediateField_isGalois
    (hE : letI := extensionAlgebra F E f; IsGalois F.Carrier E.Carrier) :
    IsGalois F.Carrier (extensionIntermediateField F E f) := by
  let := extensionAlgebra F E f
  exact IsGalois.of_algEquiv (extensionIntermediateFieldEquiv F E f)

variable (L₀ : FiniteIntermediateExtension F.Carrier)

local notation "LP" => L₀.asPadicField (p := p)

local instance : Algebra (Padic p) L₀.field := (LP).algebra

variable [Normal F.Carrier L₀.field]

/-- The tower law for `F ⊂ E ⊂ L₀` with the tower embedding of `E` into `L₀`. -/
theorem towerFieldEmbedding_finrank_mul
    (hEL : extensionIntermediateField F E f ≤ L₀.field) :
    (letI := extensionAlgebra E LP (towerFieldEmbedding F E f L₀ hEL);
      Module.finrank E.Carrier (LP).Carrier) * extensionDegree F E f =
      Module.finrank F.Carrier L₀.field := by
  let := extensionAlgebra F E f
  let := extensionAlgebra E LP (towerFieldEmbedding F E f L₀ hEL)
  have : IsScalarTower F.Carrier E.Carrier (LP).Carrier :=
    IsScalarTower.of_algebraMap_eq fun x =>
      (DFunLike.congr_fun (towerFieldEmbedding_comp F E f L₀ hEL) x).symm
  have := extensionAlgebra_finiteDimensional F E f
  have := extensionAlgebra_finiteDimensional E LP (towerFieldEmbedding F E f L₀ hEL)
  rw [mul_comm]
  exact Module.finrank_mul_finrank F.Carrier E.Carrier (LP).Carrier

/-- Two subextensions of `L₀` of the same degree over `F` have the same degree under `L₀`. -/
theorem towerFieldEmbedding_finrank_eq
    (hEL : extensionIntermediateField F E f ≤ L₀.field)
    (E' : PadicField.{u} p) (f' : F.Carrier →ₐ[Padic p] E'.Carrier)
    (hE'L : extensionIntermediateField F E' f' ≤ L₀.field)
    (hdeg : extensionDegree F E f = extensionDegree F E' f') :
    (letI := extensionAlgebra E LP (towerFieldEmbedding F E f L₀ hEL);
      Module.finrank E.Carrier (LP).Carrier) =
      (letI := extensionAlgebra E' LP (towerFieldEmbedding F E' f' L₀ hE'L);
        Module.finrank E'.Carrier (LP).Carrier) := by
  have h := (towerFieldEmbedding_finrank_mul F E f L₀ hEL).trans
    (towerFieldEmbedding_finrank_mul F E' f' L₀ hE'L).symm
  rw [hdeg] at h
  exact Nat.eq_of_mul_eq_mul_right (extensionDegree_pos F E' f') h

end Tower

section CommonClosure

variable (E : PadicField.{u} p) (f : F.Carrier →ₐ[Padic p] E.Carrier)
  (M : FiniteIntermediateExtension F.Carrier)

/-- The compositum, in the fixed algebraic closure of `F`, of the published image of `E`
and an intermediate field `M`. -/
def commonClosure : FiniteIntermediateExtension F.Carrier :=
  ⟨extensionIntermediateField F E f ⊔ M.field, inferInstance⟩

theorem commonClosure_field :
    (commonClosure F E f M).field = extensionIntermediateField F E f ⊔ M.field :=
  rfl

theorem extensionIntermediateField_le_commonClosure :
    extensionIntermediateField F E f ≤ (commonClosure F E f M).field :=
  le_sup_left

theorem intermediateField_le_commonClosure : M.field ≤ (commonClosure F E f M).field :=
  le_sup_right

/-- The common closure of a Galois extension and a Galois intermediate field is Galois. -/
theorem commonClosure_isGalois
    (hE : letI := extensionAlgebra F E f; IsGalois F.Carrier E.Carrier)
    [IsGalois F.Carrier M.field] : IsGalois F.Carrier (commonClosure F E f M).field := by
  have := extensionIntermediateField_isGalois F E f hE
  rw [commonClosure_field]
  exact { }

end CommonClosure

/-- **Common closure with the unramified extension of the same degree.** For a finite
Galois extension `E/F` given by `f`, there are finite Galois intermediate fields `M₀` and
`L₀` of the closure of `F` such that `M₀/F` is unramified of degree `[E : F]`, and `L₀`
contains the image of `E` and the published image of `M₀`. -/
theorem exists_unramified_commonClosure (E : PadicField.{u} p)
    (f : F.Carrier →ₐ[Padic p] E.Carrier)
    (hE : letI := extensionAlgebra F E f; IsGalois F.Carrier E.Carrier) :
    ∃ (M₀ L₀ : FiniteIntermediateExtension F.Carrier) (_ : IsGalois F.Carrier M₀.field)
      (_ : IsGalois F.Carrier L₀.field),
      F.canonicalTopologicalData.ramificationIndex =
          (M₀.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex ∧
        extensionDegree F (M₀.asPadicField (p := p)) (intermediateEmbedding F M₀) =
          extensionDegree F E f ∧
        extensionIntermediateField F E f ≤ L₀.field ∧
        extensionIntermediateField F (M₀.asPadicField (p := p)) (intermediateEmbedding F M₀) ≤
          L₀.field := by
  let _ : CharZero F.Carrier := Algebra.charZero_of_charZero (Padic p) F.Carrier
  obtain ⟨M₀, hM, hUnr, hdeg⟩ :=
    unramifiedExtensionDegreeExistence p F (extensionDegree F E f) (extensionDegree_pos F E f)
  refine ⟨M₀, commonClosure F E f M₀, hM, commonClosure_isGalois F E f M₀ hE, hUnr, ?_,
    extensionIntermediateField_le_commonClosure F E f M₀,
    (extensionIntermediateField_intermediateEmbedding_le F M₀).trans
      (intermediateField_le_commonClosure F E f M₀)⟩
  rw [Langlands.PadicField.extensionDegree_intermediateEmbedding, hdeg]

end Langlands.Weil.Local.FiniteGaloisTower
