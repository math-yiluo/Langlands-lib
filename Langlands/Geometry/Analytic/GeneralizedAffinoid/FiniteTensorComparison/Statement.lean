import Langlands.Geometry.Analytic.GeneralizedAffinoid.AffinoidPushout
import Langlands.Geometry.Analytic.FullRecognitionFiniteMorphisms
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Algebraic comparison for finite Banach affinoid pushouts -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.AffinoidPushout

open scoped TensorProduct

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : PresentedAffinoidAlgebra K}
  (f : BoundedAlgHom K A B) (g : BoundedAlgHom K A C)

/-- The ordinary relative tensor product of the two actual bounded maps,
with the changed base as the left tensor factor. -/
def algebraicBaseChange : Type u :=
  letI : Algebra A C := g.toAlgHom.toRingHom.toAlgebra
  letI : Algebra A B := f.toAlgHom.toRingHom.toAlgebra
  C ⊗[A] B

instance algebraicBaseChangeCommRing : CommRing (algebraicBaseChange f g) := by
  letI : Algebra A C := g.toAlgHom.toRingHom.toAlgebra
  letI : Algebra A B := f.toAlgHom.toRingHom.toAlgebra
  change CommRing (C ⊗[A] B)
  infer_instance

/-- The changed-base factor map into the ordinary tensor product. -/
def tensorLeft : C →+* algebraicBaseChange f g := by
  letI : Algebra A C := g.toAlgHom.toRingHom.toAlgebra
  letI : Algebra A B := f.toAlgHom.toRingHom.toAlgebra
  exact Algebra.TensorProduct.includeLeftRingHom

/-- The finite-map target factor map into the ordinary tensor product. -/
def tensorRight : B →+* algebraicBaseChange f g := by
  letI : Algebra A C := g.toAlgHom.toRingHom.toAlgebra
  letI : Algebra A B := f.toAlgHom.toRingHom.toAlgebra
  exact Algebra.TensorProduct.includeRight.toRingHom

omit [CompleteSpace K] in
/-- The tensor factor maps agree on the original base algebra. -/
theorem tensorLeft_comp_baseMap :
    (tensorLeft f g).comp g.toAlgHom.toRingHom =
      (tensorRight f g).comp f.toAlgHom.toRingHom := by
  let : Algebra A C := g.toAlgHom.toRingHom.toAlgebra
  let : Algebra A B := f.toAlgHom.toRingHom.toAlgebra
  exact Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap

/-- The canonical map from the ordinary relative tensor product into the
actual closed-quotient affinoid pushout. -/
def tensorComparison : algebraicBaseChange f g →+* algebra f g := by
  letI : Algebra A C := g.toAlgHom.toRingHom.toAlgebra
  letI : Algebra A B := f.toAlgHom.toRingHom.toAlgebra
  letI : Algebra A (algebra f g) := ((leftMap f g).comp f).toAlgHom.toRingHom.toAlgebra
  let a : C →ₐ[A] algebra f g :=
    { (rightMap f g).toAlgHom.toRingHom with
      commutes' := fun x => congrArg (fun h : BoundedAlgHom K A (algebra f g) => h x)
        (condition f g).symm }
  let b : B →ₐ[A] algebra f g :=
    { (leftMap f g).toAlgHom.toRingHom with commutes' := fun _ => rfl }
  exact (Algebra.TensorProduct.lift a b (fun _ _ => Commute.all _ _)).toRingHom

omit [CompleteSpace K] in
@[simp]
theorem tensorComparison_tensorLeft (a : C) :
    tensorComparison f g (tensorLeft f g a) = rightMap f g a := by
  change rightMap f g a * leftMap f g 1 = _
  simp

omit [CompleteSpace K] in
@[simp]
theorem tensorComparison_tensorRight (b : B) :
    tensorComparison f g (tensorRight f g b) = leftMap f g b := by
  change rightMap f g 1 * leftMap f g b = _
  simp

omit [CompleteSpace K] in
/-- Evaluation of the comparison on products of the two factor maps. -/
theorem tensorComparison_mul (a : C) (b : B) :
    tensorComparison f g (tensorLeft f g a * tensorRight f g b) =
      rightMap f g a * leftMap f g b := by
  rw [map_mul, tensorComparison_tensorLeft, tensorComparison_tensorRight]

/-- The proposed algebraic comparison for arbitrary finite Banach first maps.
No strict-radius or nontrivial-valuation assumption is imposed. -/
def FiniteTensorComparisonStatement (K : Type u) [NormedField K]
    [IsUltrametricDist K] [CompleteSpace K] : Prop :=
  ∀ (A B C : PresentedAffinoidAlgebra K)
    (f : BoundedAlgHom K A B) (g : BoundedAlgHom K A C),
      f.IsFiniteBanach → Function.Bijective (tensorComparison f g)

omit [CompleteSpace K] in
/-- Induction over the ordinary tensor product through products of the two
actual factor maps. -/
@[elab_as_elim]
theorem algebraicBaseChange_induction {motive : algebraicBaseChange f g → Prop}
    (m : algebraicBaseChange f g)
    (mul : ∀ (x : C) (y : B), motive (tensorLeft f g x * tensorRight f g y))
    (add : ∀ m m', motive m → motive m' → motive (m + m')) : motive m := by
  let : Algebra A C := g.toAlgHom.toRingHom.toAlgebra
  let : Algebra A B := f.toAlgHom.toRingHom.toAlgebra
  change C ⊗[A] B at m
  induction m using TensorProduct.inductionOn with
  | tmul x y =>
    have h : (x ⊗ₜ[A] y : C ⊗[A] B) = tensorLeft f g x * tensorRight f g y := by
      change _ = (x ⊗ₜ[A] (1 : B)) * ((1 : C) ⊗ₜ[A] y)
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [h]
    exact mul x y
  | add m m' hm hm' => exact add m m' hm hm'

omit [CompleteSpace K] in
theorem tensorRight_apply_map (x : A) :
    tensorRight f g (f x) = tensorLeft f g (g x) :=
  (RingHom.congr_fun (tensorLeft_comp_baseMap f g) x).symm

omit [CompleteSpace K] in
/-- The bounded pushout criterion: if the ordinary tensor product is
isomorphic to a complete ultrametric normed algebra in which both factor maps
are bounded, and the comparison is bounded for that norm, then the comparison
is bijective. -/
theorem bijective_tensorComparison_of_normedModel {E : Type v} [NormedCommRing E]
    [IsUltrametricDist E] [NormedAlgebra K E] [CompleteSpace E]
    (ι : algebraicBaseChange f g ≃+* E)
    (hK : ∀ k : K, ι (tensorLeft f g (algebraMap K C k)) = algebraMap K E k)
    (hleft : ∃ D > 0, ∀ x : C, ‖ι (tensorLeft f g x)‖ ≤ D * ‖x‖)
    (hright : ∃ C > 0, ∀ y : B, ‖ι (tensorRight f g y)‖ ≤ C * ‖y‖)
    (hτ : ∃ C > 0, ∀ z : E, ‖tensorComparison f g (ι.symm z)‖ ≤ C * ‖z‖) :
    Function.Bijective (tensorComparison f g) := by
  let a : BoundedAlgHom K C E :=
    { toAlgHom :=
        { toRingHom := ι.toRingHom.comp (tensorLeft f g)
          commutes' := hK }
      bounded := hleft }
  let b : BoundedAlgHom K B E :=
    { toAlgHom :=
        { toRingHom := ι.toRingHom.comp (tensorRight f g)
          commutes' := fun k => by
            change ι (tensorRight f g (algebraMap K B k)) = _
            rw [← f.toAlgHom.commutes k]
            change ι (tensorRight f g (f (algebraMap K A k))) = _
            rw [tensorRight_apply_map, ← hK]
            congr 2
            exact g.toAlgHom.commutes k }
      bounded := hright }
  have hab : a.comp g = b.comp f := by
    apply BoundedAlgHom.ext
    intro x
    change ι (tensorLeft f g (g x)) = ι (tensorRight f g (f x))
    rw [tensorRight_apply_map]
  let h := lift f g E b a hab.symm
  have hCcomp : ∀ x, h (rightMap f g x) = a x := fun x =>
    congrArg (fun χ : BoundedAlgHom K C E => χ x)
      (lift_comp_rightMap f g E b a hab.symm)
  have hCbase : ∀ y, h (leftMap f g y) = b y := fun y =>
    congrArg (fun χ : BoundedAlgHom K B E => χ y) (lift_comp_leftMap f g E b a hab.symm)
  have hCτ : ∀ m, h (tensorComparison f g m) = ι m := by
    intro m
    induction m using algebraicBaseChange_induction f g with
    | mul x y =>
      rw [tensorComparison_mul, map_mul, hCcomp, hCbase, map_mul]
      rfl
    | add m m' hm hm' => rw [map_add, map_add, hm, hm', map_add]
  let τ' : BoundedAlgHom K E (algebra f g) :=
    { toAlgHom :=
        { toRingHom := (tensorComparison f g).comp ι.symm.toRingHom
          commutes' := fun k => by
            change tensorComparison f g (ι.symm (algebraMap K E k)) = _
            rw [← hK, RingEquiv.symm_apply_apply, tensorComparison_tensorLeft]
            exact (rightMap f g).toAlgHom.commutes k }
      bounded := hτ }
  have hτ'C : τ'.comp h = BoundedAlgHom.id K (algebra f g) := by
    apply hom_ext f g (algebra f g)
    · apply BoundedAlgHom.ext
      intro y
      change tensorComparison f g (ι.symm (h (leftMap f g y))) = leftMap f g y
      rw [hCbase]
      change tensorComparison f g (ι.symm (ι (tensorRight f g y))) = _
      rw [RingEquiv.symm_apply_apply, tensorComparison_tensorRight]
    · apply BoundedAlgHom.ext
      intro x
      change tensorComparison f g (ι.symm (h (rightMap f g x))) = rightMap f g x
      rw [hCcomp]
      change tensorComparison f g (ι.symm (ι (tensorLeft f g x))) = _
      rw [RingEquiv.symm_apply_apply, tensorComparison_tensorLeft]
  constructor
  · intro m m' h
    apply ι.injective
    rw [← hCτ, ← hCτ, h]
  · intro y
    exact ⟨ι.symm (h y), congrArg (fun χ : BoundedAlgHom K _ _ => χ y) hτ'C⟩


end Langlands.Analytic.PresentedAffinoidAlgebra.AffinoidPushout
