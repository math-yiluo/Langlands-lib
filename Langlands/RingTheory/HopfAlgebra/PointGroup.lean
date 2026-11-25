module

public import Mathlib.RingTheory.HopfAlgebra.Convolution

/-! # Convolution groups of algebra-valued points and change of values

For a Hopf algebra `H` over `R` whose underlying ring need not be commutative, and a commutative
`R`-algebra `A`, the convolution monoid `WithConv (H →ₐ[R] A)` is a group: the inverse of a point
`f` is `f` composed with the antipode (`AlgHom.antipodeComp`). It is commutative when `H` is
cocommutative. An algebra map `φ : A →ₐ[R] B` induces the monoid homomorphism `AlgHom.mapValue φ`
between the convolution monoids of points of a bialgebra.
-/

@[expose] public section

open WithConv

namespace AlgHom

variable {R H A : Type*} [CommSemiring R]

section Hopf

variable [Semiring H] [HopfAlgebra R H] [CommSemiring A] [Algebra R A]

/-- An algebra map to a commutative algebra, composed with the antipode of the source. -/
noncomputable def antipodeComp (f : H →ₐ[R] A) : H →ₐ[R] A :=
  (f.fromOpposite fun x y => Commute.all (f x) (f y)).comp (HopfAlgebra.antipodeAlgHomOp R H)

@[simp]
lemma antipodeComp_apply (f : H →ₐ[R] A) (h : H) :
    antipodeComp f h = f (HopfAlgebra.antipode R h) :=
  rfl

@[simp]
lemma toLinearMap_antipodeComp (f : H →ₐ[R] A) :
    (antipodeComp f).toLinearMap = f.toLinearMap ∘ₗ HopfAlgebra.antipode R :=
  rfl

/-- The convolution inverse of a point is its composite with the antipode. -/
noncomputable instance convInvOfSemiring : Inv (WithConv (H →ₐ[R] A)) where
  inv f := toConv (antipodeComp f.ofConv)

@[simp]
lemma _root_.WithConv.algHom_inv_apply (f : WithConv (H →ₐ[R] A)) (h : H) :
    f⁻¹ h = f.ofConv (HopfAlgebra.antipode R h) :=
  rfl

/-- The points of a Hopf algebra with values in a commutative algebra form a group. -/
noncomputable instance convGroupOfSemiring : Group (WithConv (H →ₐ[R] A)) where
  inv_mul_cancel f := by
    apply WithConv.ext
    apply AlgHom.toLinearMap_injective
    change (toConv (f.ofConv.toLinearMap ∘ₗ HopfAlgebra.antipode R) *
      toConv f.ofConv.toLinearMap : WithConv (H →ₗ[R] A)).ofConv = _
    have eqn := LinearMap.algHom_comp_convMul_distrib f.ofConv
      (toConv (HopfAlgebra.antipode R)) (toConv (LinearMap.id (R := R) (M := H)))
    change _ = (1 : WithConv (H →ₗ[R] A)).ofConv
    simpa using eqn.symm

end Hopf

section Bialgebra

variable [Semiring H] [Bialgebra R H] [CommSemiring A] [Algebra R A]
variable {B : Type*} [CommSemiring B] [Algebra R B]

/-- Post-composition with an algebra map of value algebras, as a homomorphism of convolution
monoids of points. -/
noncomputable def mapValue (φ : A →ₐ[R] B) :
    WithConv (H →ₐ[R] A) →* WithConv (H →ₐ[R] B) where
  toFun f := toConv (φ.comp f.ofConv)
  map_one' := WithConv.ext <| AlgHom.ext fun h => φ.commutes (Coalgebra.counit h)
  map_mul' f g := WithConv.ext (φ.comp_convMul_distrib f g)

@[simp]
lemma mapValue_apply (φ : A →ₐ[R] B) (f : WithConv (H →ₐ[R] A)) :
    mapValue φ f = toConv (φ.comp f.ofConv) :=
  rfl

@[simp]
lemma mapValue_id :
    mapValue (H := H) (AlgHom.id R A) = MonoidHom.id (WithConv (H →ₐ[R] A)) :=
  MonoidHom.ext fun f => WithConv.ext (AlgHom.id_comp f.ofConv)

end Bialgebra

section CommHopf

variable [Semiring H] [HopfAlgebra R H] [Coalgebra.IsCocomm R H] [CommSemiring A] [Algebra R A]

/-- The points of a cocommutative Hopf algebra form a commutative group. -/
noncomputable instance convCommGroupOfSemiring : CommGroup (WithConv (H →ₐ[R] A)) where
  mul_comm f g := mul_comm f g

end CommHopf

end AlgHom
