import Langlands.Representation.Archimedean.PrincipalSeriesStability
import Langlands.LocalFactor.ArchimedeanPairFactor

/-!
# Complex conjugation of complex standard modules

Entrywise complex conjugation `c` is a group automorphism of `GL_n(ℂ)` preserving `U(n)`,
the diagonal torus and the upper unipotent subgroup. Precomposition with `c` carries the
`U(n)`-finite functions of the standard module of the blocks `ds` onto those of the conjugate
blocks `ds.map ComplexCharacterData.conj`. It carries right translation by `k` to right
translation by `c k`, and the right derivative along `X` to the right derivative along the
entrywise conjugate of `X`.
-/

noncomputable section

open scoped Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean

namespace ComplexConjugation

variable {n : ℕ}

/-- Entrywise complex conjugation of complex matrices, as a continuous real-linear map. -/
def matrixConj (n : ℕ) : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => A.map (starRingEnd ℂ)
      map_add' := fun A B => by
        ext i j
        simp
      map_smul' := fun c A => by
        ext i j
        simp [Complex.real_smul] }

@[simp] theorem matrixConj_apply (A : Matrix (Fin n) (Fin n) ℂ) :
    matrixConj n A = A.map (starRingEnd ℂ) := rfl

theorem matrixConj_mul (A B : Matrix (Fin n) (Fin n) ℂ) :
    matrixConj n (A * B) = matrixConj n A * matrixConj n B := by
  simp only [matrixConj_apply]
  exact Matrix.map_mul

theorem matrixConj_matrixConj (A : Matrix (Fin n) (Fin n) ℂ) :
    matrixConj n (matrixConj n A) = A := by
  ext i j
  simp

/-- Entrywise complex conjugation on `GL_n(ℂ)`. -/
def glConj (n : ℕ) : Langlands.GeneralLinear n ℂ →* Langlands.GeneralLinear n ℂ :=
  Units.map ((starRingEnd ℂ).mapMatrix : Matrix (Fin n) (Fin n) ℂ →+* _).toMonoidHom

@[simp] theorem glConj_val (g : Langlands.GeneralLinear n ℂ) :
    ((glConj n g : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) =
      matrixConj n (g : Matrix (Fin n) (Fin n) ℂ) := rfl

@[simp] theorem glConj_glConj (g : Langlands.GeneralLinear n ℂ) :
    glConj n (glConj n g) = g := by
  apply Units.ext
  rw [glConj_val, glConj_val, matrixConj_matrixConj]

theorem isUnit_matrixConj {A : Matrix (Fin n) (Fin n) ℂ} (hA : IsUnit A) :
    IsUnit (matrixConj n A) :=
  hA.map ((starRingEnd ℂ).mapMatrix : Matrix (Fin n) (Fin n) ℂ →+* _)

/-- Conjugation preserves unitary matrices. -/
theorem matrixConj_mem_unitaryGroup {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    matrixConj n A ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  let f := (starRingEnd ℂ).mapMatrix (m := Fin n)
  have hf : ∀ B : Matrix (Fin n) (Fin n) ℂ, star (f B) = f (star B) := by
    intro B
    ext i j
    simp [f, Matrix.star_apply]
  have hfA : f A = matrixConj n A := rfl
  rw [← hfA]
  rw [Unitary.mem_iff] at hA ⊢
  refine ⟨?_, ?_⟩
  · rw [hf, ← map_mul, hA.1, map_one]
  · rw [hf, ← map_mul, hA.2, map_one]

/-- Conjugation preserves the unitary group `U(n)`. -/
theorem glConj_mem_unitaryCompact {k : Langlands.GeneralLinear n ℂ}
    (hk : k ∈ unitaryCompact ℂ n) : glConj n k ∈ unitaryCompact ℂ n :=
  matrixConj_mem_unitaryGroup (n := n) (A := (k : Matrix (Fin n) (Fin n) ℂ)) hk

/-- Conjugation of a diagonal matrix conjugates its entries. -/
theorem glConj_diagonalUnits (a : Fin n → ℂˣ) :
    glConj n (Iwasawa.diagonalUnits a) =
      Iwasawa.diagonalUnits (fun i => complexConjugation (a i)) := by
  apply Units.ext
  ext i j
  rw [glConj_val, matrixConj_apply, Iwasawa.diagonalUnits_val, Iwasawa.diagonalUnits_val,
    Matrix.map_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs with h
  · rfl
  · simp

/-- Conjugation preserves the upper unipotent subgroup. -/
theorem glConj_mem_upperUnipotent {u : Langlands.GeneralLinear n ℂ}
    (hu : u ∈ upperUnipotent n ℂ) : glConj n u ∈ upperUnipotent n ℂ := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · change starRingEnd ℂ ((u : Matrix (Fin n) (Fin n) ℂ) i j) = 0
    rw [hu.1 hij, map_zero]
  · change starRingEnd ℂ ((u : Matrix (Fin n) (Fin n) ℂ) i i) = 1
    have h : (u : Matrix (Fin n) (Fin n) ℂ) i i = 1 := hu.2 i
    rw [h, map_one]

/-- Precomposition with entrywise conjugation of `GL_n(ℂ)`. -/
def conjComp (n : ℕ) :
    (Langlands.GeneralLinear n ℂ → ℂ) →ₗ[ℂ] (Langlands.GeneralLinear n ℂ → ℂ) :=
  LinearMap.funLeft ℂ ℂ (glConj n)

@[simp] theorem conjComp_apply (f : Langlands.GeneralLinear n ℂ → ℂ)
    (g : Langlands.GeneralLinear n ℂ) : conjComp n f g = f (glConj n g) := rfl

@[simp] theorem conjComp_conjComp (f : Langlands.GeneralLinear n ℂ → ℂ) :
    conjComp n (conjComp n f) = f := by
  funext g
  simp

/-- Precomposition with `c` carries right translation by `k` to right translation by `c k`. -/
theorem conjComp_rightTranslation (k : Langlands.GeneralLinear n ℂ)
    (f : Langlands.GeneralLinear n ℂ → ℂ) :
    conjComp n (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ) k f) =
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ) (glConj n k) (conjComp n f) := by
  funext g
  change f (glConj n g * k) = f (glConj n (g * glConj n k))
  rw [map_mul, glConj_glConj]

/-- Smooth functions stay smooth under precomposition with conjugation. -/
theorem contMDiff_conjComp {f : Langlands.GeneralLinear n ℂ → ℂ}
    (hf : ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ f) :
    ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ (conjComp n f) := by
  refine contMDiff_of_contDiffOn (ψ := fun y => unitsExtension f (matrixConj n y)) ?_ ?_
  · exact (contDiffOn_unitsExtension hf).comp (matrixConj n).contDiff.contDiffOn
      (fun y hy => isUnit_matrixConj hy)
  · intro g
    change f (glConj n g) = unitsExtension f (matrixConj n (g : Matrix (Fin n) (Fin n) ℂ))
    rw [← glConj_val, unitsExtension_val]

/-- The right derivative of `f ∘ c` along `X` is the right derivative of `f` along the
conjugate of `X`, evaluated at `c g`. -/
theorem rightDerivative_conjComp {f : Langlands.GeneralLinear n ℂ → ℂ}
    (hf : ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ f) (X : Matrix (Fin n) (Fin n) ℂ)
    (g : Langlands.GeneralLinear n ℂ) :
    rightDerivative (matrixModel ℂ n) X (conjComp n f) g =
      rightDerivative (matrixModel ℂ n) (matrixConj n X) f (glConj n g) := by
  have hu : IsUnit (matrixConj n ((g : Matrix (Fin n) (Fin n) ℂ) * 1)) := by
    rw [mul_one]
    exact isUnit_matrixConj (Units.isUnit g)
  have h1 : HasFDerivAt (unitsExtension f)
      (fderiv ℝ (unitsExtension f) (matrixConj n ((g : Matrix (Fin n) (Fin n) ℂ) * 1)))
      (matrixConj n ((g : Matrix (Fin n) (Fin n) ℂ) * 1)) :=
    (differentiableAt_unitsExtension hf hu).hasFDerivAt
  have h2 : HasFDerivAt
      (fun y : Matrix (Fin n) (Fin n) ℂ => matrixConj n ((g : Matrix (Fin n) (Fin n) ℂ) * y))
      ((matrixConj n).comp
        ((g : Matrix (Fin n) (Fin n) ℂ) • ContinuousLinearMap.id ℝ _)) 1 :=
    (matrixConj n).hasFDerivAt.comp (1 : Matrix (Fin n) (Fin n) ℂ)
      ((hasFDerivAt_id (1 : Matrix (Fin n) (Fin n) ℂ)).const_mul (g : Matrix (Fin n) (Fin n) ℂ))
  have h3 := h1.comp (1 : Matrix (Fin n) (Fin n) ℂ) h2
  have hφ : ∀ h : Langlands.GeneralLinear n ℂ, conjComp n f (g * h) =
      (fun y : Matrix (Fin n) (Fin n) ℂ =>
        unitsExtension f (matrixConj n ((g : Matrix (Fin n) (Fin n) ℂ) * y)))
        (h : Matrix (Fin n) (Fin n) ℂ) := by
    intro h
    change f (glConj n (g * h)) = unitsExtension f (matrixConj n
      ((g : Matrix (Fin n) (Fin n) ℂ) * (h : Matrix (Fin n) (Fin n) ℂ)))
    rw [← Units.val_mul, ← glConj_val, unitsExtension_val]
  have hd : DifferentiableAt ℝ (fun y : Matrix (Fin n) (Fin n) ℂ =>
      unitsExtension f (matrixConj n ((g : Matrix (Fin n) (Fin n) ℂ) * y)))
      ((1 : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) := by
    rw [Units.val_one]
    exact h3.differentiableAt
  have hm := mfderiv_eq_fderiv_of_eq_comp (φ := fun h => conjComp n f (g * h))
    (ψ := fun y : Matrix (Fin n) (Fin n) ℂ =>
      unitsExtension f (matrixConj n ((g : Matrix (Fin n) (Fin n) ℂ) * y))) hφ 1 hd
  have hr : rightDerivative (matrixModel ℂ n) X (conjComp n f) g =
      fderiv ℝ (fun y : Matrix (Fin n) (Fin n) ℂ =>
        unitsExtension f (matrixConj n ((g : Matrix (Fin n) (Fin n) ℂ) * y))) 1 X := by
    rw [Units.val_one] at hm
    exact congrArg (fun L => L X) hm
  have h4 : fderiv ℝ (fun y : Matrix (Fin n) (Fin n) ℂ =>
      unitsExtension f (matrixConj n ((g : Matrix (Fin n) (Fin n) ℂ) * y))) 1 =
      (fderiv ℝ (unitsExtension f) (matrixConj n ((g : Matrix (Fin n) (Fin n) ℂ) * 1))).comp
        ((matrixConj n).comp ((g : Matrix (Fin n) (Fin n) ℂ) • ContinuousLinearMap.id ℝ _)) :=
    h3.fderiv
  rw [hr, h4, rightDerivative_eq_fderiv hf]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul, mul_one, glConj_val, matrixConj_mul]

/-- Precomposition with `c` carries the right derivative along `X` to the right derivative
along the conjugate of `X`. -/
theorem conjComp_rightDerivative {f : Langlands.GeneralLinear n ℂ → ℂ}
    (hf : ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ f) (X : Matrix (Fin n) (Fin n) ℂ) :
    conjComp n (rightDerivative (matrixModel ℂ n) X f) =
      rightDerivative (matrixModel ℂ n) (matrixConj n X) (conjComp n f) := by
  funext g
  rw [rightDerivative_conjComp hf, matrixConj_matrixConj]
  rfl

/-- The position characters of conjugate blocks are the position characters of the blocks
composed with conjugation. -/
theorem complexPositionCharacter_map_conj :
    ∀ (ds : List ComplexCharacterData) (p : ℕ) (z : ℂˣ),
      complexPositionCharacter (ds.map ComplexCharacterData.conj) p z =
        complexPositionCharacter ds p (complexConjugation z)
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | _ :: ds, p + 1, z => complexPositionCharacter_map_conj ds p z

theorem principalSeriesCharacter_map_conj (N : ℕ) (ds : List ComplexCharacterData)
    (a : Fin N → ℂˣ) :
    principalSeriesCharacter ℂ N (complexPositionCharacter ds)
        (fun i => complexConjugation (a i)) =
      principalSeriesCharacter ℂ N (complexPositionCharacter (ds.map ComplexCharacterData.conj))
        a := by
  unfold principalSeriesCharacter
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [complexPositionCharacter_map_conj, coe_complexConjugation, Complex.norm_conj]

/-- Precomposition with `c` maps the principal series of the blocks `ds` into that of the
conjugate blocks. -/
theorem conjComp_mem_complexStandardModule {ds : List ComplexCharacterData}
    {f : Langlands.GeneralLinear n ℂ → ℂ} (hf : f ∈ complexStandardModule n ds) :
    conjComp n f ∈ complexStandardModule n (ds.map ComplexCharacterData.conj) := by
  refine ⟨contMDiff_conjComp hf.1, fun a u g => ?_⟩
  change f (glConj n ((Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℂ) *
      (u : Langlands.GeneralLinear n ℂ) * g)) = _ * f (glConj n g)
  rw [map_mul, map_mul, glConj_diagonalUnits]
  have h := hf.2 (fun i => complexConjugation (a i))
    ⟨glConj n (u : Langlands.GeneralLinear n ℂ), glConj_mem_upperUnipotent u.2⟩ (glConj n g)
  rw [h, principalSeriesCharacter_map_conj]

/-- Precomposition with `c` preserves `U(n)`-finiteness under right translation. -/
theorem conjComp_mem_kFiniteVectors {f : Langlands.GeneralLinear n ℂ → ℂ}
    (hf : f ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ))
      (unitaryCompact ℂ n)) :
    conjComp n f ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ))
      (unitaryCompact ℂ n) := by
  rw [mem_kFiniteVectors_iff] at hf ⊢
  set W := Submodule.span ℂ (Set.range fun k : unitaryCompact ℂ n =>
    Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ) (k : _) f)
  refine Submodule.finiteDimensional_of_le (S₂ := W.map (conjComp n)) (Submodule.span_le.mpr ?_)
  rintro _ ⟨k, rfl⟩
  have hk : glConj n (glConj n (k : Langlands.GeneralLinear n ℂ)) = k := glConj_glConj _
  refine ⟨Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ)
    (glConj n (k : Langlands.GeneralLinear n ℂ)) f,
    Submodule.subset_span ⟨⟨_, glConj_mem_unitaryCompact k.2⟩, rfl⟩, ?_⟩
  change conjComp n (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ) _ f) = _
  rw [conjComp_rightTranslation, hk]

/-- Precomposition with `c` maps the `U(n)`-finite functions of the standard module of `ds`
into those of the conjugate blocks. -/
theorem conjComp_mem_kFiniteFunctions {ds : List ComplexCharacterData}
    {f : Langlands.GeneralLinear n ℂ → ℂ}
    (hf : f ∈ kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)) :
    conjComp n f ∈
      kFiniteFunctions (complexStandardModule n (ds.map ComplexCharacterData.conj))
        (unitaryCompact ℂ n) :=
  ⟨conjComp_mem_complexStandardModule hf.1, conjComp_mem_kFiniteVectors hf.2⟩

/-- Functions of a complex standard module are smooth. -/
theorem contMDiff_of_mem_kFiniteFunctions {ds : List ComplexCharacterData}
    {f : Langlands.GeneralLinear n ℂ → ℂ}
    (hf : f ∈ kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)) :
    ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ f :=
  hf.1.1

end ComplexConjugation

end Langlands.Archimedean
