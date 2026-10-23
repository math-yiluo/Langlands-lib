import Langlands.Shimura.Unitary.Positivity
import Mathlib.Algebra.QuadraticAlgebra.Basic

noncomputable section

universe u v

namespace Langlands.Shimura

open CategoryTheory
open scoped QuadraticAlgebra
open scoped TensorProduct

namespace DeligneTorus

/-- The quadratic coordinate model for scalar extension of the complex numbers. -/
abbrev Complexification (S : Type u) [CommRing S] := QuadraticAlgebra S (-1) 0

variable {S : Type u} {T : Type v} [CommRing S] [CommRing T]

/-- Coefficient change in the quadratic model. -/
def map (f : S →+* T) : Complexification S →+* Complexification T where
  toFun z := ⟨f z.re, f z.im⟩
  map_one' := by ext <;> simp
  map_mul' z w := by ext <;> simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
  map_zero' := by ext <;> simp
  map_add' z w := by ext <;> simp

@[simp] theorem map_re (f : S →+* T) (z : Complexification S) : (map f z).re = f z.re := rfl
@[simp] theorem map_im (f : S →+* T) (z : Complexification S) : (map f z).im = f z.im := rfl

@[simp] theorem norm_map (f : S →+* T) (z : Complexification S) :
    QuadraticAlgebra.norm (map f z) = f (QuadraticAlgebra.norm z) := by
  simp [QuadraticAlgebra.norm_def]

/-- Deligne-torus points, using the actual units in the quadratic algebra. -/
abbrev Points (S : Type u) [CommRing S] := (Complexification S)ˣ

/-- The norm character on points. -/
def norm (S : Type u) [CommRing S] : Points S →* Sˣ :=
  Units.map QuadraticAlgebra.norm

/-- The restriction-of-scalars point functor in quadratic coordinates. -/
def functor : CommAlgCat.{u} ℝ ⥤ GrpCat.{u} where
  obj S := GrpCat.of (Points S)
  map f := GrpCat.ofHom (Units.map (map f.hom.toRingHom).toMonoidHom)
  map_id S := by
    apply GrpCat.hom_ext
    ext z : 2
    rfl
  map_comp f g := by
    apply GrpCat.hom_ext
    ext z : 2
    rfl

/-- Inversion is a natural group automorphism because the point groups are commutative. -/
def inversion : functor.{u} ⟶ functor.{u} where
  app S := GrpCat.ofHom (invMonoidHom : Points S →* Points S)
  naturality {S T} f := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro z
    exact (_root_.map_inv (Units.map (map f.hom.toRingHom).toMonoidHom) z).symm

variable (S) [Algebra ℝ S]

/-- The complex generator inside the quadratic algebra. -/
def complexMap : ℂ →ₐ[ℝ] Complexification S :=
  Complex.liftAux QuadraticAlgebra.omega (by ext <;> simp)

/-- The canonical map from the scalar extension of `ℂ` into quadratic coordinates. -/
def fromTensor : S ⊗[ℝ] ℂ →ₐ[S] Complexification S :=
  AlgHom.liftEquiv ℝ S ℂ (Complexification S) (complexMap S)

@[simp] theorem fromTensor_tmul (s : S) (z : ℂ) :
    fromTensor S (s ⊗ₜ[ℝ] z) = s • complexMap S z := rfl

/-- The quadratic generator is sent to `1 ⊗ i`. -/
def toTensor : Complexification S →ₐ[S] S ⊗[ℝ] ℂ :=
  QuadraticAlgebra.lift ⟨1 ⊗ₜ[ℝ] Complex.I, by
    simp [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.one_def,
      TensorProduct.smul_tmul', smul_eq_mul, TensorProduct.tmul_neg,
      TensorProduct.neg_tmul]⟩

@[simp] theorem toTensor_omega : toTensor S QuadraticAlgebra.omega = 1 ⊗ₜ[ℝ] Complex.I := by
  simp [toTensor]

theorem toTensor_complexMap (z : ℂ) : toTensor S (complexMap S z) = 1 ⊗ₜ[ℝ] z := by
  have h : ((toTensor S).restrictScalars ℝ).comp (complexMap S) =
      (Algebra.TensorProduct.includeRight : ℂ →ₐ[ℝ] S ⊗[ℝ] ℂ) := by
    apply Complex.algHom_ext
    simp [complexMap]
  exact AlgHom.congr_fun h z

/-- The quadratic model is the actual scalar extension `S ⊗[ℝ] ℂ`. -/
def tensorEquiv : Complexification S ≃ₐ[S] S ⊗[ℝ] ℂ :=
  AlgEquiv.ofAlgHom (toTensor S) (fromTensor S)
    (by
      apply Algebra.TensorProduct.ext'
      intro s z
      change toTensor S (s • complexMap S z) = s ⊗ₜ[ℝ] z
      rw [map_smul, toTensor_complexMap]
      simp [TensorProduct.smul_tmul', smul_eq_mul])
    (by
      apply QuadraticAlgebra.algHom_ext
      simp [fromTensor_tmul, complexMap])

@[simp] theorem toTensor_apply (z : Complexification S) :
    toTensor S z = z.re ⊗ₜ[ℝ] (1 : ℂ) + z.im ⊗ₜ[ℝ] Complex.I := by
  change z.re • (1 : S ⊗[ℝ] ℂ) + z.im • (1 ⊗ₜ[ℝ] Complex.I) = _
  simp [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul]

/-- The tensor identification respects change of real algebra. -/
theorem toTensor_natural [Algebra ℝ T] (f : S →ₐ[ℝ] T) (z : Complexification S) :
    AlgebraInvolution.changeCoefficients (A := ℂ) f (toTensor S z) =
      toTensor T (map f.toRingHom z) := by
  simp

/-- Formula for the canonical inclusion of complex scalars. -/
@[simp] theorem complexMap_re (z : ℂ) : (complexMap S z).re = algebraMap ℝ S z.re := by
  simp [complexMap, Complex.liftAux_apply,
    IsScalarTower.algebraMap_apply ℝ S (Complexification S), Algebra.smul_def]

@[simp] theorem complexMap_im (z : ℂ) : (complexMap S z).im = algebraMap ℝ S z.im := by
  simp [complexMap, Complex.liftAux_apply,
    IsScalarTower.algebraMap_apply ℝ S (Complexification S), Algebra.smul_def]

@[simp] theorem norm_complexMap (z : ℂ) :
    QuadraticAlgebra.norm (complexMap S z) = algebraMap ℝ S (Complex.normSq z) := by
  simp [QuadraticAlgebra.norm_def, Complex.normSq_apply]

omit [Algebra ℝ S] in
/-- Coefficient change preserves the norm character. -/
theorem norm_natural (f : S →+* T) (z : Points S) :
    norm T (Units.map (map f).toMonoidHom z) = Units.map f.toMonoidHom (norm S z) := by
  apply Units.ext
  exact norm_map f z

/-- At the real algebra itself, the quadratic algebra is the complex numbers. -/
def realEquiv : Complexification ℝ ≃ₐ[ℝ] ℂ :=
  (tensorEquiv ℝ).trans (Algebra.TensorProduct.lid ℝ ℂ)

@[simp] theorem realEquiv_complexMap (z : ℂ) : realEquiv (complexMap ℝ z) = z := by
  change Algebra.TensorProduct.lid ℝ ℂ (toTensor ℝ (complexMap ℝ z)) = z
  rw [toTensor_complexMap]
  simp

/-- Identify the real points with the actual nonzero complex numbers. -/
def realPointsEquiv : Points ℝ ≃* ℂˣ := Units.mapEquiv realEquiv.toMulEquiv

end DeligneTorus

namespace AlgebraInvolution.ComplexHom

variable {A : Type u} [Ring A] [Algebra ℝ A] {σ : AlgebraInvolution ℝ A}
variable (h : ComplexHom σ) (S : Type v) [CommRing S] [Algebra ℝ S]

/-- Extend a compatible complex homomorphism to every commutative real algebra. -/
def deligneAlgebraMap : DeligneTorus.Complexification S →ₐ[S] S ⊗[ℝ] A :=
  QuadraticAlgebra.lift ⟨1 ⊗ₜ[ℝ] h.hom Complex.I, by
    simp [Algebra.TensorProduct.tmul_mul_tmul, ← _root_.map_mul,
      Algebra.TensorProduct.one_def, TensorProduct.tmul_neg]⟩

@[simp] theorem deligneAlgebraMap_apply (z : DeligneTorus.Complexification S) :
    h.deligneAlgebraMap S z = z.re ⊗ₜ[ℝ] (1 : A) + z.im ⊗ₜ[ℝ] h.hom Complex.I := by
  change z.re • (1 : S ⊗[ℝ] A) + z.im • (1 ⊗ₜ[ℝ] h.hom Complex.I) = _
  simp [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul]

/-- The scalar-extended homomorphism respects the actual involutions. -/
theorem deligneAlgebraMap_star (z : DeligneTorus.Complexification S) :
    σ.baseChange S (h.deligneAlgebraMap S z) = h.deligneAlgebraMap S (star z) := by
  simp [h.star_compatible, TensorProduct.tmul_neg, TensorProduct.neg_tmul]

/-- The extended complex map on units, with its proved norm multiplier. -/
def delignePoints : DeligneTorus.Points S →* (σ.baseChange S).similitudes where
  toFun z := ⟨(Units.map (h.deligneAlgebraMap S).toMonoidHom z, DeligneTorus.norm S z), by
    rw [(σ.baseChange S).mem_similitudes_iff]
    change h.deligneAlgebraMap S (z : DeligneTorus.Complexification S) *
      σ.baseChange S (h.deligneAlgebraMap S z) =
      algebraMap S (S ⊗[ℝ] A) (QuadraticAlgebra.norm (z : DeligneTorus.Complexification S))
    rw [h.deligneAlgebraMap_star, ← _root_.map_mul,
      ← QuadraticAlgebra.algebraMap_norm_eq_mul_star, AlgHom.commutes]⟩
  map_one' := Subtype.ext (Prod.ext (_root_.map_one _) (_root_.map_one _))
  map_mul' z w := Subtype.ext (Prod.ext (_root_.map_mul _ z w) (_root_.map_mul _ z w))

@[simp] theorem delignePoints_multiplier (z : DeligneTorus.Points S) :
    (σ.baseChange S).multiplier (h.delignePoints S z) = DeligneTorus.norm S z := rfl

variable {S} {T : Type*} [CommRing T] [Algebra ℝ T]

/-- Scalar extension commutes with every morphism of real algebras. -/
theorem deligneAlgebraMap_natural (f : S →ₐ[ℝ] T) (z : DeligneTorus.Complexification S) :
    changeCoefficients (A := A) f (h.deligneAlgebraMap S z) =
      h.deligneAlgebraMap T (DeligneTorus.map f.toRingHom z) := by
  simp

/-- The Deligne-torus homomorphism as a natural transformation of group functors. -/
def deligneHom : DeligneTorus.functor.{u} ⟶ σ.similitudeFunctor where
  app S := GrpCat.ofHom (h.delignePoints S)
  naturality {S T} f := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro z
    apply Subtype.ext
    apply Prod.ext
    · apply Units.ext
      exact (h.deligneAlgebraMap_natural f.hom (Units.val (z : DeligneTorus.Points S))).symm
    · apply Units.ext
      exact DeligneTorus.norm_map f.hom.toRingHom (Units.val (z : DeligneTorus.Points S))

/-- Kottwitz's inverse convention, before specializing the complex homomorphism. -/
def inverseDeligneHom : DeligneTorus.functor.{u} ⟶ σ.similitudeFunctor :=
  DeligneTorus.inversion ≫ h.deligneHom

@[simp] theorem inverseDeligneHom_multiplier {S : CommAlgCat.{u} ℝ}
    (z : DeligneTorus.Points S) :
    (σ.baseChange S).multiplier ((h.inverseDeligneHom.app S).hom z) =
      (DeligneTorus.norm S z)⁻¹ := by
  change DeligneTorus.norm S z⁻¹ = (DeligneTorus.norm S z)⁻¹
  exact _root_.map_inv _ z

variable (S)

/-- On included complex scalars, the new map is the scalar extension of the old one. -/
theorem deligneAlgebraMap_complexMap (z : ℂ) :
    h.deligneAlgebraMap S (DeligneTorus.complexMap S z) = 1 ⊗ₜ[ℝ] h.hom z := by
  have heq : ((h.deligneAlgebraMap S).restrictScalars ℝ).comp
      (DeligneTorus.complexMap S) =
      (Algebra.TensorProduct.includeRight : A →ₐ[ℝ] S ⊗[ℝ] A).comp h.hom := by
    apply Complex.algHom_ext
    simp [DeligneTorus.complexMap]
  exact AlgHom.congr_fun heq z

/-- The real component recovers the underlying unit of `toSimilitudes`. -/
theorem delignePoints_real_underlying (z : ℂˣ) :
    Units.map (Algebra.TensorProduct.lid ℝ A).toMonoidHom
      ((σ.baseChange ℝ).underlyingUnit
        (h.delignePoints ℝ (Units.map (DeligneTorus.complexMap ℝ).toMonoidHom z))) =
      σ.underlyingUnit (h.toSimilitudes z) := by
  apply Units.ext
  change Algebra.TensorProduct.lid ℝ A
    (h.deligneAlgebraMap ℝ (DeligneTorus.complexMap ℝ (z : ℂ))) = h.hom (z : ℂ)
  rw [h.deligneAlgebraMap_complexMap]
  simp

/-- The real multiplier recovers the norm square of the original complex unit. -/
theorem delignePoints_real_multiplier (z : ℂˣ) :
    (σ.baseChange ℝ).multiplier
      (h.delignePoints ℝ (Units.map (DeligneTorus.complexMap ℝ).toMonoidHom z)) =
      σ.multiplier (h.toSimilitudes z) := by
  apply Units.ext
  change QuadraticAlgebra.norm (DeligneTorus.complexMap ℝ (z : ℂ)) = Complex.normSq (z : ℂ)
  simp

end AlgebraInvolution.ComplexHom

/-- The corrected Harris complex map on every commutative real algebra. -/
def harrisDeligneHom (n : ℕ) (I : Type u) [DecidableEq I] (distinguished : I) :=
  (harrisArchimedeanHom n I distinguished).deligneHom

/-- Kottwitz's inverse-of-`h₀` convention on every commutative real algebra. -/
def kottwitzDeligneHom (n : ℕ) (I : Type u) [DecidableEq I] (distinguished : I) :=
  (kottwitzHom n I distinguished).inverseDeligneHom

end Langlands.Shimura
