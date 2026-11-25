module

public import Langlands.RingTheory.WeilRestriction.PresentedAlgebra
public import Langlands.RingTheory.HopfAlgebra.PointGroup
public import Mathlib.RingTheory.Bialgebra.Convolution
public import Mathlib.RingTheory.Bialgebra.Equiv
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.TensorProduct.Maps

/-! # The bialgebra structure of a Weil restriction

Let `H` be a finitely presented commutative bialgebra over `B`, where `B` is a finite projective
`A`-algebra, and let `W = Langlands.Algebra.WeilRestriction A B H`. The points of `H` with values
in `B ⊗[A] T` form a monoid under convolution. Transporting the product along the representing
bijection `WeilRestriction.homEquiv` defines the comultiplication `WeilRestriction.comul` and the
counit `WeilRestriction.counit` of `W`, hence the bialgebra `WeilRestriction.instBialgebra`, and
`WeilRestriction.pointsMulEquiv` identifies the convolution monoid of points of `W` over `T` with
that of `H` over `B ⊗[A] T`, naturally in `T`.
-/

public noncomputable section

open WithConv Algebra.TensorProduct
open scoped TensorProduct

namespace Langlands.Algebra.WeilRestriction

section Associator

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
  {C : Type*} [Semiring C] [Algebra R C]

/- The associator `(A ⊗ B) ⊗ C ≃ A ⊗ (B ⊗ C)` on the three tensor inclusions. -/
private theorem assoc_comp_includeLeft_comp_includeLeft :
    (((Algebra.TensorProduct.assoc R R R A B C).toAlgHom.comp includeLeft).comp includeLeft :
      A →ₐ[R] A ⊗[R] (B ⊗[R] C)) = includeLeft := by
  ext a
  simp
  rfl

private theorem assoc_comp_includeLeft_comp_includeRight :
    (((Algebra.TensorProduct.assoc R R R A B C).toAlgHom.comp includeLeft).comp includeRight :
      B →ₐ[R] A ⊗[R] (B ⊗[R] C)) = includeRight.comp includeLeft := by
  ext b
  simp

private theorem assoc_comp_includeRight :
    ((Algebra.TensorProduct.assoc R R R A B C).toAlgHom.comp includeRight :
      C →ₐ[R] A ⊗[R] (B ⊗[R] C)) = includeRight.comp includeRight := by
  ext c
  simp
  rfl

end Associator

variable {A B H : Type*} [CommRing A] [CommRing B] [CommRing H] [Algebra A B]
  [Module.Finite A B] [Module.Projective A B] [Bialgebra B H] [Algebra.FinitePresentation B H]

local notation "W" => WeilRestriction A B H
variable {T U : Type*} [CommRing T] [Algebra A T] [CommRing U] [Algebra A U]

/- The product of two points of `W`, transported from the convolution of the points of `H` they
classify. -/
private def product (f g : W →ₐ[A] T) : W →ₐ[A] T :=
  let e := homEquiv A B H T
  e.symm (toConv (e f) * toConv (e g)).ofConv

private theorem post_product (k : T →ₐ[A] U) (f g : W →ₐ[A] T) :
    k.comp (product f g) = product (k.comp f) (k.comp g) := by
  apply (homEquiv A B H U).injective
  simp only [homEquiv_comp, product, Equiv.apply_symm_apply, AlgHom.comp_convMul_distrib]

private theorem product_assoc (f g h : W →ₐ[A] T) :
    product (product f g) h = product f (product g h) := by
  apply (homEquiv A B H T).injective
  simp only [product, Equiv.apply_symm_apply, toConv_ofConv, mul_assoc]

variable (A B H)

/-- The comultiplication of the Weil restriction: the product of the two tensor-factor points. -/
def comul : W →ₐ[A] W ⊗[A] W := product includeLeft includeRight

/-- The counit of the Weil restriction: it classifies the identity point of `H` over `B ⊗[A] A`. -/
def counit : W →ₐ[A] A :=
  let unitPoint : WithConv (H →ₐ[B] B ⊗[A] A) := 1
  (homEquiv A B H A).symm unitPoint.ofConv

variable {A B H}

/-- The counit followed by `A → T` classifies the identity point over `B ⊗[A] T`. -/
theorem homEquiv_ofId_comp_counit :
    homEquiv A B H T ((Algebra.ofId A T).comp (counit A B H)) =
      (1 : WithConv (H →ₐ[B] B ⊗[A] T)).ofConv := by
  rw [homEquiv_comp]
  unfold counit
  rw [Equiv.apply_symm_apply]
  exact congrArg ofConv ((AlgHom.mapValue (H := H)
    (lTensor (S := B) B (Algebra.ofId A T))).map_one)

private theorem product_one (f : W →ₐ[A] T) :
    product ((Algebra.ofId A T).comp (counit A B H)) f = f ∧
    product f ((Algebra.ofId A T).comp (counit A B H)) = f := by
  constructor <;> apply (homEquiv A B H T).injective <;>
    simp only [product, Equiv.apply_symm_apply, homEquiv_ofId_comp_counit, toConv_ofConv,
      one_mul, mul_one, ofConv_toConv]

private lemma comp_comul (f : W ⊗[A] W →ₐ[A] T) :
    f.comp (comul A B H) = product (f.comp includeLeft) (f.comp includeRight) :=
  post_product f _ _

variable (A B H) in
/-- Coassociativity of `comul`. -/
theorem assoc_comp_map_comul_comp_comul :
    (Algebra.TensorProduct.assoc A A A W W W).toAlgHom.comp
      ((Algebra.TensorProduct.map (comul A B H) (.id A W)).comp (comul A B H)) =
      (Algebra.TensorProduct.map (.id A W) (comul A B H)).comp (comul A B H) := by
  rw [← AlgHom.comp_assoc, comp_comul, comp_comul]
  simp only [AlgHom.comp_assoc, map_comp_includeLeft, map_comp_includeRight, AlgHom.comp_id]
  simp only [comp_comul, post_product, ← AlgHom.comp_assoc,
    assoc_comp_includeLeft_comp_includeLeft, assoc_comp_includeLeft_comp_includeRight,
    assoc_comp_includeRight]
  apply product_assoc

variable (A B H) in
/-- `counit` is a left counit for `comul`. -/
theorem map_counit_comp_comul :
    (Algebra.TensorProduct.map (counit A B H) (.id A W)).comp (comul A B H) =
      (Algebra.TensorProduct.lid A W).symm.toAlgHom := by
  rw [comp_comul, map_comp_includeLeft, map_comp_includeRight, AlgHom.comp_id]
  have eqn : (includeLeft : A →ₐ[A] A ⊗[A] W) = Algebra.ofId A _ := Subsingleton.elim _ _
  rw [eqn, (product_one _).1]
  rfl

variable (A B H) in
/-- `counit` is a right counit for `comul`. -/
theorem map_id_counit_comp_comul :
    (Algebra.TensorProduct.map (.id A W) (counit A B H)).comp (comul A B H) =
      (Algebra.TensorProduct.rid A A W).symm.toAlgHom := by
  rw [comp_comul, map_comp_includeLeft, map_comp_includeRight, AlgHom.comp_id]
  have eqn : (includeRight : A →ₐ[A] W ⊗[A] A) = Algebra.ofId A _ := Subsingleton.elim _ _
  rw [eqn, (product_one _).2]
  rfl

/-- The Weil restriction of a commutative bialgebra is a bialgebra. -/
instance instBialgebra : Bialgebra A W := by
  exact Bialgebra.ofAlgHom _ _ (assoc_comp_map_comul_comp_comul A B H)
    (map_counit_comp_comul A B H) (map_id_counit_comp_comul A B H)

variable (A B H) (T : Type*) [CommRing T] [Algebra A T]

/-- The representing bijection, as an isomorphism of convolution monoids of points. -/
def pointsMulEquiv : WithConv (W →ₐ[A] T) ≃* WithConv (H →ₐ[B] B ⊗[A] T) where
  toEquiv := ((WithConv.equiv _).trans (homEquiv A B H T)).trans (WithConv.equiv _).symm
  map_mul' f g := by
    apply WithConv.ofConv_injective
    change homEquiv A B H T (f * g).ofConv = _
    have mult : (f * g).ofConv = product f.ofConv g.ofConv := by
      rw [AlgHom.convMul_def, ofConv_toConv, ← AlgHom.comp_assoc, lmul'_comp_map]
      change (lift f.ofConv g.ofConv _).comp (comul A B H) = _
      unfold comul
      simp only [post_product, lift_comp_includeLeft, lift_comp_includeRight']
    rw [mult]
    exact (homEquiv A B H T).apply_symm_apply _

variable {A B H T}

/-- `pointsMulEquiv` is the representing bijection `homEquiv`. -/
@[simp] theorem pointsMulEquiv_apply (f : WithConv (W →ₐ[A] T)) :
    (pointsMulEquiv A B H T f).ofConv = homEquiv A B H T f.ofConv := by rfl

/-- The inverse of `pointsMulEquiv` is the inverse of `homEquiv`. -/
@[simp] theorem pointsMulEquiv_symm_apply (g : WithConv (H →ₐ[B] B ⊗[A] T)) :
    ((pointsMulEquiv A B H T).symm g).ofConv = (homEquiv A B H T).symm g.ofConv := by rfl

/-- Naturality of `pointsMulEquiv` in the test algebra. -/
theorem pointsMulEquiv_naturality {T' : Type*} [CommRing T'] [Algebra A T'] (h : T →ₐ[A] T')
    (f : WithConv (W →ₐ[A] T)) :
    pointsMulEquiv A B H T' (toConv (h.comp f.ofConv)) =
      toConv ((lTensor (S := B) B h).comp (pointsMulEquiv A B H T f).ofConv) := by
  apply WithConv.ext
  simpa only [pointsMulEquiv_apply, ofConv_toConv] using homEquiv_comp f.ofConv h

end Langlands.Algebra.WeilRestriction
