import Langlands.GroupScheme.Examples.QuasiSplitUnitary
import Langlands.GroupScheme.GeneralLinear
import Langlands.GroupScheme.Torus.Split
import Langlands.Shimura.Unitary.ExchangeInvolution
import Langlands.Shimura.Unitary.SchemeScalarExtension
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # The splitting of the quasi-split unitary group `U(1,1)` over `E` -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry Algebra
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.QuasiSplitUnitary

section Exchange
variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
  (σ : Langlands.Shimura.AlgebraInvolution R A)

/-- The unitary group of an exchange involution is the unit group of the first factor. -/
def exchangeUnitaryEquiv : σ.exchange.unitary ≃* Aˣ where
  toFun g := (MulEquiv.prodUnits g.val).1
  invFun a := ⟨MulEquiv.prodUnits.symm (a, σ.units a⁻¹), by
    rw [Langlands.Shimura.AlgebraInvolution.mem_unitary_iff]
    apply Prod.ext
    · change (a : A) * σ (σ ((a⁻¹ : Aˣ) : A)) = 1
      rw [σ.apply_apply, Units.mul_inv]
    · change σ ((a⁻¹ : Aˣ) : A) * σ (a : A) = 1
      rw [← σ.apply_mul, Units.mul_inv, σ.apply_one]⟩
  left_inv g := by
    have hg := (σ.exchange.mem_unitary_iff g.val).mp g.property
    have h1 : ((MulEquiv.prodUnits g.val).1 : A) * σ (g.val : A × A).2 = 1 :=
      congrArg Prod.fst hg
    apply Subtype.ext
    apply Units.ext
    apply Prod.ext
    · rfl
    · change σ (((MulEquiv.prodUnits g.val).1⁻¹ : Aˣ) : A) = (g.val : A × A).2
      rw [← Units.eq_inv_of_mul_eq_one_left h1, σ.apply_apply]
  right_inv a := rfl
  map_mul' g h := by
    change (MulEquiv.prodUnits (g.val * h.val)).1 = _
    rw [_root_.map_mul]
    rfl

@[simp] theorem exchangeUnitaryEquiv_apply (g : σ.exchange.unitary) :
    ((exchangeUnitaryEquiv σ g : Aˣ) : A) = (g.val : A × A).1 := rfl

@[simp] theorem exchangeUnitaryEquiv_symm_apply (a : Aˣ) :
    (((exchangeUnitaryEquiv σ).symm a).val : A × A) = ((a : A), σ ((a⁻¹ : Aˣ) : A)) := rfl

end Exchange

/-- The transpose for the antidiagonal Gram matrix, with trivial conjugation. -/
def transposeInvolution (R : Type*) [CommRing R] :
    Langlands.Shimura.AlgebraInvolution R (Matrix (Fin 2) (Fin 2) R) :=
  matrixInvolution (AlgEquiv.refl : R ≃ₐ[R] R)
    (fun _ => rfl : Function.Involutive (AlgEquiv.refl : R ≃ₐ[R] R))

theorem transposeInvolution_adjoint (R : Type*) [CommRing R] (M : Matrix (Fin 2) (Fin 2) R) :
    transposeInvolution R M = adjoint id M := rfl

theorem transposeInvolution_apply (R : Type*) [CommRing R] (M : Matrix (Fin 2) (Fin 2) R) :
    transposeInvolution R M = gram R * M.transpose * gram R := by
  show adjoint _ M = _
  exact adjoint_eq_gram _ M

variable {F E : Type u} [Field F] [Field E] [Algebra F E]

section FieldSplitting

/-- Evaluation at the identity and at the conjugation. -/
def evaluation (c : E ≃ₐ[F] E) : E →ₐ[F] E × E :=
  (AlgHom.id F E).prod (c : E →ₐ[F] E)

/-- Scalar extension of the two evaluations. -/
def tensorEvaluation (c : E ≃ₐ[F] E) : E ⊗[F] E →ₐ[E] E × E :=
  AlgHom.liftEquiv F E E _ (evaluation c)

@[simp] theorem tensorEvaluation_tmul (c : E ≃ₐ[F] E) (x y : E) :
    tensorEvaluation c (x ⊗ₜ[F] y) = (x * y, x * c y) := rfl

/-- A nontrivial conjugation makes the two evaluations span `E × E`. -/
theorem tensorEvaluation_surjective (c : E ≃ₐ[F] E) (hc : c ≠ AlgEquiv.refl) :
    Function.Surjective (tensorEvaluation c) := by
  have hn : ∃ t : E, t ≠ c t := by
    by_contra! h
    apply hc
    ext t
    exact (h t).symm
  obtain ⟨t, ht⟩ := hn
  have hd : t - c t ≠ 0 := sub_ne_zero.mpr ht
  intro x
  let q := (x.1 - x.2) / (t - c t)
  let d := x.1 - q * t
  refine ⟨d ⊗ₜ[F] (1 : E) + q ⊗ₜ[F] t, ?_⟩
  rw [map_add, tensorEvaluation_tmul, tensorEvaluation_tmul]
  apply Prod.ext
  · change d * 1 + q * t = x.1
    dsimp [d]
    ring
  · change d * c 1 + q * c t = x.2
    rw [map_one, mul_one]
    dsimp [d, q]
    field_simp [hd]
    ring

variable [IsQuadraticExtension F E]

/-- Quadratic degree makes the surjective evaluation bijective. -/
theorem tensorEvaluation_bijective (c : E ≃ₐ[F] E) (hc : c ≠ AlgEquiv.refl) :
    Function.Bijective (tensorEvaluation c) := by
  have hd : Module.finrank E (E ⊗[F] E) = Module.finrank E (E × E) := by
    rw [Module.finrank_baseChange, IsQuadraticExtension.finrank_eq_two F E,
      Module.finrank_prod, Module.finrank_self]
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mpr
    (tensorEvaluation_surjective c hc), tensorEvaluation_surjective c hc⟩

/-- `E ⊗[F] E ≃ E × E`, `x ⊗ y ↦ (x y, x c(y))`. -/
def tensorEquiv (c : E ≃ₐ[F] E) (hc : c ≠ AlgEquiv.refl) : E ⊗[F] E ≃ₐ[E] E × E :=
  AlgEquiv.ofBijective (tensorEvaluation c) (tensorEvaluation_bijective c hc)

@[simp] theorem tensorEquiv_tmul (c : E ≃ₐ[F] E) (hc : c ≠ AlgEquiv.refl) (x y : E) :
    tensorEquiv c hc (x ⊗ₜ[F] y) = (x * y, x * c y) := rfl

variable (R : Type u) [CommRing R] [Algebra F R] [Algebra E R] [IsScalarTower F E R]

/-- The splitting after scalar extension to an arbitrary `E`-algebra. -/
def algebraEquiv (c : E ≃ₐ[F] E) (hc : c ≠ AlgEquiv.refl) : R ⊗[F] E ≃ₐ[R] R × R :=
  ((Algebra.TensorProduct.cancelBaseChange F E R R E).symm.trans
      (Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[R] R) (tensorEquiv c hc))).trans
    ((Algebra.TensorProduct.prodRight E R R E E).trans
      (AlgEquiv.prodCongr (Algebra.TensorProduct.rid E R R)
        (Algebra.TensorProduct.rid E R R)))

@[simp] theorem algebraEquiv_tmul (c : E ≃ₐ[F] E) (hc : c ≠ AlgEquiv.refl) (r : R) (e : E) :
    algebraEquiv R c hc (r ⊗ₜ[F] e) = (r * algebraMap E R e, r * algebraMap E R (c e)) := by
  simp [algebraEquiv, Algebra.TensorProduct.prodRight_tmul, Algebra.smul_def, mul_comm]

end FieldSplitting

section Points
variable [IsQuadraticExtension F E]
  (R : Type u) [CommRing R] [Algebra F R] [Algebra E R] [IsScalarTower F E R]
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- `E ⊗[F] R ≃ R × R`, `e ⊗ r ↦ (e r, c(e) r)`, for an `E`-algebra `R`. -/
def tensorSplit (c : E ≃ₐ[F] E) (hc : c ≠ AlgEquiv.refl) : E ⊗[F] R ≃ₐ[R] R × R :=
  (Algebra.TensorProduct.commRight F R E).symm.trans (algebraEquiv R c hc)

@[simp] theorem tensorSplit_tmul (c : E ≃ₐ[F] E) (hc : c ≠ AlgEquiv.refl) (e : E) (r : R) :
    tensorSplit R c hc (e ⊗ₜ[F] r) = (r * algebraMap E R e, r * algebraMap E R (c e)) := by
  change algebraEquiv R c hc (r ⊗ₜ[F] e) = _
  exact algebraEquiv_tmul R c hc r e

/-- Under the splitting, conjugation of the `E`-factor exchanges the two factors. -/
theorem tensorSplit_scalarConjugation (c : E ≃ₐ[F] E) (hc : c ≠ AlgEquiv.refl)
    (x : E ⊗[F] R) :
    tensorSplit R c hc (scalarConjugation R c x) = (tensorSplit R c hc x).swap := by
  induction x using TensorProduct.inductionOn with
  | tmul e r => simp [conjugation_involutive c e]
  | add x y hx hy => simp [hx, hy]

/-- Entrywise splitting of `2 × 2` matrices over `E ⊗[F] R` into two matrices over `R`. -/
def matrixSplit (c : E ≃ₐ[F] E) (hc : c ≠ AlgEquiv.refl) :
    Matrix (Fin 2) (Fin 2) (E ⊗[F] R) ≃ₐ[R]
      Matrix (Fin 2) (Fin 2) R × Matrix (Fin 2) (Fin 2) R :=
  (tensorSplit R c hc).mapMatrix.trans (Langlands.Shimura.ComplexMatrix.prodAlgEquiv R R 2 R)

theorem matrixSplit_apply (c : E ≃ₐ[F] E) (hc : c ≠ AlgEquiv.refl)
    (X : Matrix (Fin 2) (Fin 2) (E ⊗[F] R)) :
    matrixSplit R c hc X =
      (fun i j => (tensorSplit R c hc (X i j)).1, fun i j => (tensorSplit R c hc (X i j)).2) :=
  rfl

/-- The matrix splitting carries the unitary involution to the exchange involution. -/
theorem matrixSplit_involution (c : E ≃ₐ[F] E) (hc : c ≠ AlgEquiv.refl)
    (X : Matrix (Fin 2) (Fin 2) (E ⊗[F] R)) :
    matrixSplit R c hc
        (matrixInvolution (scalarConjugation R c) (scalarConjugation_involutive R c) X) =
      (transposeInvolution R).exchange (matrixSplit R c hc X) := by
  rw [matrixSplit_apply, matrixSplit_apply]
  change (fun i j => (tensorSplit R c hc (adjoint (scalarConjugation R c) X i j)).1,
      fun i j => (tensorSplit R c hc (adjoint (scalarConjugation R c) X i j)).2) =
    (adjoint id (fun i j => (tensorSplit R c hc (X i j)).2),
      adjoint id (fun i j => (tensorSplit R c hc (X i j)).1))
  apply Prod.ext <;>
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [adjoint, tensorSplit_scalarConjugation]

/-- The points of `U(1,1)` over an `E`-algebra are `GL₂`, through the first factor. -/
def pointsSplitting (c : E ≃ₐ[F] E) (hc : c ≠ AlgEquiv.refl) :
    matrixPoints R c ≃* GL (Fin 2) R :=
  (Langlands.Shimura.AlgebraInvolution.unitaryEquiv
      (matrixInvolution (scalarConjugation R c) (scalarConjugation_involutive R c))
      (transposeInvolution R).exchange (matrixSplit R c hc)
      (matrixSplit_involution R c hc)).trans
    (exchangeUnitaryEquiv (transposeInvolution R))

/-- The splitting is the first coordinate of `E ⊗[F] R ≃ R × R`, entrywise. -/
theorem pointsSplitting_val (c : E ≃ₐ[F] E) (hc : c ≠ AlgEquiv.refl) (g : matrixPoints R c) :
    ((pointsSplitting R c hc g : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) =
      (g.val : Matrix (Fin 2) (Fin 2) (E ⊗[F] R)).map (fun x => (tensorSplit R c hc x).1) :=
  rfl

/-- The inverse splitting puts `h` in the first and `J (h⁻¹)ᵀ J` in the second factor. -/
theorem pointsSplitting_symm_val (c : E ≃ₐ[F] E) (hc : c ≠ AlgEquiv.refl)
    (h : GL (Fin 2) R) (i j : Fin 2) :
    (((pointsSplitting R c hc).symm h).val : Matrix (Fin 2) (Fin 2) (E ⊗[F] R)) i j =
      (tensorSplit R c hc).symm ((h : Matrix (Fin 2) (Fin 2) R) i j,
        (gram R * ((h⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R).transpose * gram R) i j) := by
  rw [← transposeInvolution_apply]
  rfl

end Points

section Coefficients
variable [IsQuadraticExtension F E]
  {R S : Type u} [CommRing R] [CommRing S] [Algebra F R] [Algebra F S]
  [Algebra E R] [Algebra E S] [IsScalarTower F E R] [IsScalarTower F E S]
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The first coordinate of the splitting commutes with `E`-compatible coefficient maps. -/
theorem tensorSplit_coefficientMap_fst (c : E ≃ₐ[F] E) (hc : c ≠ AlgEquiv.refl)
    (f : R →ₐ[F] S) (hf : ∀ e : E, f (algebraMap E R e) = algebraMap E S e)
    (x : E ⊗[F] R) :
    (tensorSplit S c hc (tensorCoefficientMap f x)).1 = f (tensorSplit R c hc x).1 := by
  induction x using TensorProduct.inductionOn with
  | tmul e r => simp [hf]
  | add x y hx hy => simp only [map_add, Prod.fst_add, hx, hy]

end Coefficients

section Scheme
open Langlands.Shimura.AlgebraInvolution.SchemeModel
attribute [local instance] sectionsSAlgebra sectionsScalarTower

variable [IsQuadraticExtension F E] {κ : Type u} [Fintype κ]
  (b : Module.Basis κ F (Matrix (Fin 2) (Fin 2) E)) (c : E ≃ₐ[F] E) (hc : c ≠ AlgEquiv.refl)

/-- The base change of `U(1,1)` along `Spec E ⟶ Spec F`. -/
abbrev baseChangeGroupScheme : Langlands.GroupScheme (Spec (CommRingCat.of E)) :=
  (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap F E)))).obj
    (groupScheme b c)

/-- Points of the base change over an `E`-scheme `T` are `GL₂(Γ(T, ⊤))`. -/
def basePointsEquiv (T : Over (Spec (CommRingCat.of E))) :
    (T ⟶ (baseChangeGroupScheme b c).X) ≃* GL (Fin 2) Γ(T.left, ⊤) :=
  (GroupScheme.baseChangePointsEquiv (scalarBaseMap F E) (groupScheme b c) T).trans
    ((pointsEquiv b c ((Over.map (scalarBaseMap F E)).obj T)).trans
      (pointsSplitting (restrictedSections F E T) c hc))

/-- Entrywise formula: first coordinate of the splitting of the `E ⊗[F] Γ(T, ⊤)` matrix. -/
theorem basePointsEquiv_apply (T : Over (Spec (CommRingCat.of E)))
    (x : T ⟶ (baseChangeGroupScheme b c).X) (i j : Fin 2) :
    (basePointsEquiv b c hc T x : Matrix (Fin 2) (Fin 2) Γ(T.left, ⊤)) i j =
      (tensorSplit (restrictedSections F E T) c hc
        (((pointsEquiv b c ((Over.map (scalarBaseMap F E)).obj T)
          (GroupScheme.baseChangePointsEquiv (scalarBaseMap F E) (groupScheme b c) T x)).val :
            Matrix (Fin 2) (Fin 2) (E ⊗[F] restrictedSections F E T)) i j)).1 :=
  rfl

/-- The `GL₂` description of points is natural in the `E`-scheme. -/
theorem basePointsEquiv_naturality {T T' : Over (Spec (CommRingCat.of E))} (a : T' ⟶ T)
    (x : T ⟶ (baseChangeGroupScheme b c).X) :
    basePointsEquiv b c hc T' (a ≫ x) =
      Matrix.GeneralLinearGroup.map a.left.appTop.hom (basePointsEquiv b c hc T x) := by
  apply Units.ext
  ext i j
  rw [basePointsEquiv_apply]
  change _ = a.left.appTop ((basePointsEquiv b c hc T x : Matrix (Fin 2) (Fin 2) _) i j)
  rw [basePointsEquiv_apply, GroupScheme.baseChangePointsEquiv_naturality,
    pointsEquiv_naturality, Matrix.map_apply]
  have key := tensorSplit_coefficientMap_fst (R := restrictedSections F E T)
    (S := restrictedSections F E T') c hc
    ((algΓ (CommRingCat.of F)).map ((Over.map (scalarBaseMap F E)).map a)).unop.hom
    (fun e => ((algΓ (CommRingCat.of E)).map a).unop.hom.commutes e)
  exact key _

/-- The splitting isomorphism `G_E ≅ GL₂` over `Spec E`. -/
def splittingIso :
    baseChangeGroupScheme b c ≅ GeneralLinear.groupScheme (Fin 2) (CommRingCat.of E) :=
  isoOfPointModels (fun T => GL (Fin 2) Γ(T.left, ⊤))
    (fun a => Matrix.GeneralLinearGroup.map a.left.appTop.hom)
    (basePointsEquiv b c hc) (GeneralLinear.pointsEquiv (Fin 2) (CommRingCat.of E))
    (basePointsEquiv_naturality b c hc)
    (fun {_ _} a y => GeneralLinear.pointsEquiv_naturality a y)

/-- On points, the splitting isomorphism is `basePointsEquiv`. -/
theorem splittingIso_hom_points (T : Over (Spec (CommRingCat.of E)))
    (x : T ⟶ (baseChangeGroupScheme b c).X) :
    GeneralLinear.pointsEquiv (Fin 2) (CommRingCat.of E) T
        (x ≫ (splittingIso b c hc).hom.hom.hom) = basePointsEquiv b c hc T x :=
  isoOfPointModels_hom _ _ _ _ (basePointsEquiv_naturality b c hc)
    (fun {_ _} a y => GeneralLinear.pointsEquiv_naturality a y) T x

/-- On points, the inverse splitting isomorphism is the inverse of `basePointsEquiv`. -/
theorem splittingIso_inv_points (T : Over (Spec (CommRingCat.of E)))
    (y : T ⟶ (GeneralLinear.groupScheme (Fin 2) (CommRingCat.of E)).X) :
    basePointsEquiv b c hc T (y ≫ (splittingIso b c hc).inv.hom.hom) =
      GeneralLinear.pointsEquiv (Fin 2) (CommRingCat.of E) T y :=
  isoOfPointModels_inv _ _ _ _ (basePointsEquiv_naturality b c hc)
    (fun {_ _} a y => GeneralLinear.pointsEquiv_naturality a y) T y

end Scheme

end Langlands.GroupScheme.QuasiSplitUnitary
