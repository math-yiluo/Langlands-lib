import Langlands.Shimura.Unitary.Deligne
import Mathlib.Algebra.Group.Prod

noncomputable section

universe u v

namespace Langlands.Shimura.DeligneTorus

open CategoryTheory
open scoped QuadraticAlgebra TensorProduct

variable (S : Type u) [CommRing S] [Algebra ℂ S]

private abbrev scalarI : S := algebraMap ℂ S Complex.I
private abbrev half : S := algebraMap ℂ S (1 / 2)

private theorem scalarI_sq : scalarI S * scalarI S = -1 := by
  rw [← map_mul, Complex.I_mul_I, map_neg, map_one]

private theorem half_two : half S * 2 = 1 := by
  have h := congrArg (algebraMap ℂ S) (show (1 / 2 : ℂ) * 2 = 1 by norm_num)
  simpa only [map_mul, map_ofNat, map_one] using h

/-- Evaluation at the two complex roots of the quadratic relation. -/
def splitHom : Complexification S →ₐ[S] S × S :=
  (QuadraticAlgebra.lift ⟨scalarI S, by simp [scalarI_sq]⟩).prod
    (QuadraticAlgebra.lift ⟨-scalarI S, by simp [scalarI_sq]⟩)

@[simp] theorem splitHom_apply (z : Complexification S) :
    splitHom S z = (z.re + z.im * scalarI S, z.re - z.im * scalarI S) := by
  ext <;> simp [splitHom, QuadraticAlgebra.lift, sub_eq_add_neg]

/-- The quadratic algebra splits over every complex algebra, including nonreduced ones. -/
def splitEquiv : Complexification S ≃ₐ[S] S × S :=
  { splitHom S with
    invFun := fun p => ⟨half S * (p.1 + p.2), -(scalarI S * half S) * (p.1 - p.2)⟩
    left_inv := by
      intro z
      change (⟨half S * ((splitHom S z).1 + (splitHom S z).2),
        -(scalarI S * half S) * ((splitHom S z).1 - (splitHom S z).2)⟩ :
        Complexification S) = z
      rw [splitHom_apply]
      apply QuadraticAlgebra.ext
      · dsimp
        linear_combination z.re * half_two S
      · dsimp
        linear_combination -(2 * half S * z.im) * scalarI_sq S + z.im * half_two S
    right_inv := by
      intro p
      change splitHom S ⟨half S * (p.1 + p.2),
        -(scalarI S * half S) * (p.1 - p.2)⟩ = p
      rw [splitHom_apply]
      apply Prod.ext <;> dsimp
      · linear_combination -(half S * (p.1 - p.2)) * scalarI_sq S + p.1 * half_two S
      · linear_combination (half S * (p.1 - p.2)) * scalarI_sq S + p.2 * half_two S }

@[simp] theorem splitEquiv_apply (z : Complexification S) :
    splitEquiv S z = (z.re + z.im * algebraMap ℂ S Complex.I,
      z.re - z.im * algebraMap ℂ S Complex.I) := splitHom_apply S z

@[simp] theorem splitEquiv_symm_apply (p : S × S) :
    (splitEquiv S).symm p =
      (⟨algebraMap ℂ S (1 / 2) * (p.1 + p.2),
        -(algebraMap ℂ S Complex.I * algebraMap ℂ S (1 / 2)) * (p.1 - p.2)⟩ :
        Complexification S) := rfl

/-- The actual scalar extension of the complex numbers has the same splitting. -/
def tensorSplitEquiv [Algebra ℝ S] :=
  (tensorEquiv S).symm.trans (splitEquiv S)

/-- Splitting identifies units with two independent scalar units. -/
def splitPointsEquiv : Points S ≃* Sˣ × Sˣ :=
  (Units.mapEquiv (splitEquiv S).toMulEquiv).trans MulEquiv.prodUnits

@[simp] theorem splitPointsEquiv_fst (z : Points S) :
    ((splitPointsEquiv S z).1 : S) =
      (z : Complexification S).re + (z : Complexification S).im * algebraMap ℂ S Complex.I :=
  congrArg Prod.fst (splitEquiv_apply S z)

@[simp] theorem splitPointsEquiv_snd (z : Points S) :
    ((splitPointsEquiv S z).2 : S) =
      (z : Complexification S).re - (z : Complexification S).im * algebraMap ℂ S Complex.I :=
  congrArg Prod.snd (splitEquiv_apply S z)

/-- Quadratic conjugation interchanges the two factors; it does not conjugate the base. -/
theorem splitEquiv_star (z : Complexification S) :
    splitEquiv S (star z) = (splitEquiv S z).swap := by
  ext <;> simp [splitEquiv_apply, sub_eq_add_neg]

/-- The quadratic norm becomes the product of the two split coordinates. -/
theorem splitEquiv_norm (z : Complexification S) :
    QuadraticAlgebra.norm z = (splitEquiv S z).1 * (splitEquiv S z).2 := by
  simp only [QuadraticAlgebra.norm_def, splitEquiv_apply, zero_mul, add_zero,
    neg_mul, one_mul, sub_neg_eq_add]
  linear_combination z.im ^ 2 * scalarI_sq S

/-- The norm character is multiplication on the two scalar unit groups. -/
theorem splitPointsEquiv_norm (z : Points S) :
    norm S z = (splitPointsEquiv S z).1 * (splitPointsEquiv S z).2 := by
  apply Units.ext
  exact splitEquiv_norm S z

variable {S} {T : Type v} [CommRing T] [Algebra ℂ T]

/-- Splitting commutes with every complex-algebra homomorphism. -/
theorem splitEquiv_natural (f : S →ₐ[ℂ] T) (z : Complexification S) :
    splitEquiv T (map f.toRingHom z) = Prod.map f f (splitEquiv S z) := by
  ext <;> simp [splitEquiv_apply, AlgHom.commutes]

/-- The unit-group splitting is natural in the complex algebra. -/
theorem splitPointsEquiv_natural (f : S →ₐ[ℂ] T) (z : Points S) :
    splitPointsEquiv T (Units.map (map f.toRingHom).toMonoidHom z) =
      Prod.map (Units.map f.toMonoidHom) (Units.map f.toMonoidHom) (splitPointsEquiv S z) := by
  apply Prod.ext <;> apply Units.ext
  · exact congrArg Prod.fst (splitEquiv_natural f z)
  · exact congrArg Prod.snd (splitEquiv_natural f z)

/-- The Deligne quadratic-unit functor evaluated on complex algebras. -/
def complexFunctor : CommAlgCat.{u} ℂ ⥤ GrpCat.{u} where
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

/-- The functor of two independent invertible scalars on complex algebras. -/
def splitFunctor : CommAlgCat.{u} ℂ ⥤ GrpCat.{u} where
  obj S := GrpCat.of (Sˣ × Sˣ)
  map f := GrpCat.ofHom ((Units.map f.hom.toMonoidHom).prodMap
    (Units.map f.hom.toMonoidHom))
  map_id S := by
    apply GrpCat.hom_ext
    ext z <;> rfl
  map_comp f g := by
    apply GrpCat.hom_ext
    ext z <;> rfl

/-- A natural multiplicative splitting over all commutative complex test algebras. -/
def splitFunctorIso : complexFunctor.{u} ≅ splitFunctor.{u} :=
  NatIso.ofComponents (fun S => (splitPointsEquiv S).toGrpIso) (by
    intro S T f
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro z
    exact splitPointsEquiv_natural f.hom z)

end Langlands.Shimura.DeligneTorus
