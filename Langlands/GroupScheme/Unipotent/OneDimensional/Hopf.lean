import Langlands.GroupScheme.AffineLinearEmbedding.Coordinate
import Langlands.GroupScheme.Unipotent.AdditiveQuotient
import Langlands.GroupScheme.Unipotent.OneDimensional.Cocycle
import Mathlib.RingTheory.Bialgebra.Primitive
import Mathlib.RingTheory.PolynomialAlgebra
import Mathlib.RingTheory.Flat.Basic

/-! # Rigidity, cocommutativity and exponent of one-dimensional unipotent coordinate rings -/

noncomputable section

universe u

open CategoryTheory Polynomial TensorProduct
open Algebra.TensorProduct (includeLeft includeRight productMap)

namespace Langlands.GroupScheme.Unipotent.OneDimensional

open AffineLinearEmbedding

section Rigid

variable {k A : Type*} [Field k] [CommRing A] [IsDomain A] [Algebra k A]

/-- In a domain with a `k`-point, integral elements are constants. -/
theorem eq_algebraMap_of_isIntegral (χ : A →ₐ[k] k) {a : A} (ha : IsIntegral k a) :
    a = algebraMap k A (χ a) := by
  by_contra h
  have h0 : a - algebraMap k A (χ a) ≠ 0 := sub_ne_zero.mpr h
  have hχ : χ (a - algebraMap k A (χ a)) = 0 := by simp
  exact transcendental_of_augmentation_eq_zero χ h0 hχ
    (ha.sub isIntegral_algebraMap).isAlgebraic

/-- An algebra map into a domain with a `k`-point that kills an element with
finite-dimensional quotient factors through the point. -/
theorem eq_comp_of_finite {C : Type*} [CommRing C] [Algebra k C] (χ : A →ₐ[k] k)
    (f : C →ₐ[k] A) {y : C} (hy : f y = 0) (hfin : Module.Finite k (C ⧸ Ideal.span {y})) :
    f = (Algebra.ofId k A).comp (χ.comp f) := by
  ext b
  have hI : ∀ z ∈ Ideal.span {y}, f z = 0 := by
    intro z hz
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    rw [map_mul, hy, mul_zero]
  let g : C ⧸ Ideal.span {y} →ₐ[k] A := Ideal.Quotient.liftₐ (Ideal.span {y}) f hI
  have hint : IsIntegral k (f b) := by
    have hg : f b = g (Ideal.Quotient.mkₐ k _ b) :=
      (AlgHom.congr_fun (Ideal.Quotient.liftₐ_comp (Ideal.span {y}) f hI) b).symm
    rw [hg]
    exact (Algebra.IsIntegral.isIntegral _).map g
  exact eq_algebraMap_of_isIntegral χ hint

end Rigid

section Injective

variable {k R S T : Type*} [Field k] [CommRing R] [Algebra k R] [CommRing S] [Algebra k S]
  [CommRing T] [Algebra k T]

/-- The algebra map `R[X] → S ⊗ T`, `∑ rᵢ Xⁱ ↦ ∑ φ(rᵢ) ⊗ yⁱ`. -/
def tensorEval (φ : R →ₐ[k] S) (y : T) : R[X] →ₐ[k] S ⊗[k] T :=
  eval₂AlgHom (includeLeft.comp φ) (1 ⊗ₜ y) fun _ => Commute.all _ _

theorem tensorEval_apply (φ : R →ₐ[k] S) (y : T) (c : R[X]) :
    tensorEval φ y c = c.eval₂ (includeLeft.comp φ).toRingHom (1 ⊗ₜ y) :=
  rfl

@[simp] theorem tensorEval_C (φ : R →ₐ[k] S) (y : T) (r : R) :
    tensorEval φ y (C r) = φ r ⊗ₜ 1 := by
  simp [tensorEval_apply]

@[simp] theorem tensorEval_X (φ : R →ₐ[k] S) (y : T) :
    tensorEval φ y (X : R[X]) = 1 ⊗ₜ y := by
  simp [tensorEval_apply]

/-- `tensorEval` factors through `R[X] ≃ R ⊗ k[X]`. -/
theorem tensorEval_eq_map (φ : R →ₐ[k] S) (y : T) :
    tensorEval φ y =
      (Algebra.TensorProduct.map φ (aeval y : k[X] →ₐ[k] T)).comp
        (polyEquivTensor k R).toAlgHom := by
  apply algHom_ext'
  · ext r
    simp [CAlgHom]
  · simp

/-- The map `R[X] → S ⊗ T` is injective when `φ` is injective and `y` is transcendental. -/
theorem tensorEval_injective (φ : R →ₐ[k] S) (hφ : Function.Injective φ) {y : T}
    (hy : Transcendental k y) : Function.Injective (tensorEval φ y) := by
  have hinj : Function.Injective
      (TensorProduct.map φ.toLinearMap (aeval y : k[X] →ₐ[k] T).toLinearMap) :=
    TensorProduct.map_injective_of_flat_flat _ _ hφ (transcendental_iff_injective.mp hy)
  intro c c' h
  rw [tensorEval_eq_map] at h
  exact (polyEquivTensor k R).injective (hinj h)

end Injective

section Points

variable {k : Type u} [Field k]
  {F : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} (CommRingCat.of k)}
  (e : (F ⋙ forget GrpCat).CorepresentableBy B)

/-- The algebra map classifying a point. -/
abbrev val {A : CommAlgCat.{u} (CommRingCat.of k)} (x : F.obj A) : B →ₐ[k] A :=
  (e.homEquiv.symm x).hom

theorem val_injective {A : CommAlgCat.{u} (CommRingCat.of k)} {x x' : F.obj A}
    (h : val e x = val e x') : x = x' := by
  rw [← pt_homEquiv_symm e x, ← pt_homEquiv_symm e x']
  exact congrArg (pt e) h

theorem val_pt {A : CommAlgCat.{u} (CommRingCat.of k)} (f : B →ₐ[k] A) : val e (pt e f) = f := by
  change (e.homEquiv.symm (e.homEquiv (CommAlgCat.ofHom f))).hom = f
  rw [Equiv.symm_apply_apply]
  rfl

theorem val_mul {A : CommAlgCat.{u} (CommRingCat.of k)} (x x' : F.obj A) :
    val e (x * x') = (productMap (val e x) (val e x')).comp (comul e) :=
  homEquiv_symm_mul e x x'

theorem val_one (A : CommAlgCat.{u} (CommRingCat.of k)) :
    val e (1 : F.obj A) = (Algebra.ofId k A).comp (counit e) :=
  homEquiv_symm_one e A

theorem val_map {A A' : CommAlgCat.{u} (CommRingCat.of k)} (g : A ⟶ A') (x : F.obj A) :
    val e (F.map g x) = g.hom.comp (val e x) :=
  homEquiv_symm_map e g x

/-- The universal point. -/
def univ : F.obj B :=
  pt e (AlgHom.id k B)

theorem val_univ : val e (univ e) = AlgHom.id k B :=
  val_pt e _

/-- A point whose classifying map, composed with a `k`-point, is the counit becomes trivial
after that `k`-point. -/
theorem map_eq_one {A : CommAlgCat.{u} (CommRingCat.of k)} (χ : A →ₐ[k] k) (x : F.obj A)
    (hχ : χ.comp (val e x) = counit e) :
    F.map (CommAlgCat.ofHom χ : A ⟶ CommAlgCat.of (CommRingCat.of k) (CommRingCat.of k)) x
      = 1 := by
  apply val_injective e
  rw [val_map, CommAlgCat.hom_ofHom, hχ, val_one]
  ext b
  rfl

/-- **Rigidity.** A point over a domain with a `k`-point, which is trivial at that `k`-point
and kills an element `y` with finite-dimensional quotient `B / yB`, is trivial. -/
theorem eq_one_of_val_eq_zero {A : CommAlgCat.{u} (CommRingCat.of k)} [IsDomain A]
    (χ : A →ₐ[k] k) (x : F.obj A) {y : B} (hxy : val e x y = 0)
    (hfin : Module.Finite k (B ⧸ Ideal.span {y}))
    (hχ : F.map (CommAlgCat.ofHom χ : A ⟶ CommAlgCat.of (CommRingCat.of k) (CommRingCat.of k)) x
      = 1) : x = 1 := by
  apply val_injective e
  have h := congrArg (val e) hχ
  rw [val_map, CommAlgCat.hom_ofHom, val_one] at h
  rw [eq_comp_of_finite χ (val e x) hxy hfin, val_one, h]
  ext b
  rfl

section Primitive

variable {e} {y : B} (hy : letI := bialgebra e; Bialgebra.IsPrimitiveElem k y)
include hy

theorem val_mul_apply {A : CommAlgCat.{u} (CommRingCat.of k)} (x x' : F.obj A) :
    val e (x * x') y = val e x y + val e x' y := by
  let := bialgebra e
  rw [val_mul, AlgHom.comp_apply,
    show AffineLinearEmbedding.comul e y = 1 ⊗ₜ[k] y + y ⊗ₜ[k] 1 from
      hy.comul_eq_tmul_add_tmul]
  simp only [map_add, Algebra.TensorProduct.productMap_apply_tmul, map_one, one_mul, mul_one]
  exact add_comm _ _

/-- A primitive element gives a homomorphism from points to the additive group. -/
def primHom (A : CommAlgCat.{u} (CommRingCat.of k)) : F.obj A →* Multiplicative A where
  toFun x := Multiplicative.ofAdd (val e x y)
  map_one' := by
    let := bialgebra e
    rw [val_one, AlgHom.comp_apply,
      show AffineLinearEmbedding.counit e y = 0 from hy.counit_eq_zero, map_zero, ofAdd_zero]
  map_mul' x x' := by
    rw [val_mul_apply hy, ofAdd_add]

theorem val_inv_apply {A : CommAlgCat.{u} (CommRingCat.of k)} (x : F.obj A) :
    val e x⁻¹ y = -val e x y :=
  congrArg Multiplicative.toAdd (map_inv (primHom hy A) x)

theorem val_pow_apply {A : CommAlgCat.{u} (CommRingCat.of k)} (x : F.obj A) (n : ℕ) :
    val e (x ^ n) y = n • val e x y :=
  congrArg Multiplicative.toAdd (map_pow (primHom hy A) x n)

end Primitive

/-- **Cocommutativity.** If the coordinate ring has domain square and some nonzero primitive
`y` has finite-dimensional quotient `B / yB`, then the comultiplication is cocommutative. -/
theorem comm_comp_comul [IsDomain (B ⊗[k] B)] {y : B}
    (hy : letI := bialgebra e; Bialgebra.IsPrimitiveElem k y)
    (hfin : Module.Finite k (B ⧸ Ideal.span {y})) :
    (Algebra.TensorProduct.comm k B B).toAlgHom.comp (comul e) = comul e := by
  let A := CommAlgCat.of (CommRingCat.of k) (B ⊗[k] B)
  let x₁ : F.obj A := pt e (A := A) includeLeft
  let x₂ : F.obj A := pt e (A := A) includeRight
  let χ : A →ₐ[k] k := productMap (counit e) (counit e)
  have h₁ : F.map (CommAlgCat.ofHom χ : A ⟶ CommAlgCat.of (CommRingCat.of k) (CommRingCat.of k))
      x₁ = 1 := map_eq_one e χ x₁ (by rw [val_pt]; exact Algebra.TensorProduct.productMap_left _ _)
  have h₂ : F.map (CommAlgCat.ofHom χ : A ⟶ CommAlgCat.of (CommRingCat.of k) (CommRingCat.of k))
      x₂ = 1 := map_eq_one e χ x₂ (by rw [val_pt]; exact Algebra.TensorProduct.productMap_right _ _)
  have hκ : x₁ * x₂ * x₁⁻¹ * x₂⁻¹ = 1 := by
    refine eq_one_of_val_eq_zero e (A := A) χ _ (y := y) ?_ hfin ?_
    · rw [val_mul_apply hy, val_mul_apply hy, val_mul_apply hy, val_inv_apply hy,
        val_inv_apply hy]
      ring
    · rw [map_mul, map_mul, map_mul, map_inv, map_inv, h₁, h₂]
      simp
  have hc : x₁ * x₂ = x₂ * x₁ := by
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hκ
    exact hκ
  have h := congrArg (val e) hc
  rw [val_mul, val_mul, val_pt, val_pt] at h
  have hid : productMap (includeLeft : B →ₐ[k] B ⊗[k] B) includeRight = AlgHom.id k _ := by
    ext <;> simp
  have hcomm : productMap (includeRight : B →ₐ[k] B ⊗[k] B) includeLeft =
      (Algebra.TensorProduct.comm k B B).toAlgHom := by
    ext <;> simp
  rw [hid, hcomm, AlgHom.id_comp] at h
  exact h.symm

/-- The `n`-th power of the universal point is classified by the `n`-fold convolution power
of the identity. -/
theorem val_univ_pow_succ (n : ℕ) :
    val e (univ e ^ (n + 1)) = (productMap (val e (univ e ^ n)) (AlgHom.id k B)).comp (comul e) := by
  rw [pow_succ, val_mul, val_univ]

/-- **Exponent `p`.** In characteristic `p`, if `B` is a domain and some primitive `y` has
finite-dimensional quotient `B / yB`, then the `p`-th power of the universal point is trivial. -/
theorem univ_pow_char [IsDomain B] (p : ℕ) [CharP k p] {y : B}
    (hy : letI := bialgebra e; Bialgebra.IsPrimitiveElem k y)
    (hfin : Module.Finite k (B ⧸ Ideal.span {y})) : univ e ^ p = 1 := by
  refine eq_one_of_val_eq_zero e (A := B) (counit e) _ (y := y) ?_ hfin ?_
  · rw [val_pow_apply hy, val_univ, AlgHom.id_apply, ← Nat.cast_smul_eq_nsmul k,
      CharP.cast_eq_zero k p, zero_smul]
  · rw [map_pow, map_eq_one e (counit e) (univ e) (by rw [val_univ]; rfl), one_pow]

end Points

end Langlands.GroupScheme.Unipotent.OneDimensional
