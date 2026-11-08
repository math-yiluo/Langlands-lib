import Langlands.Automorphic.OperatorSubquotientArchimedean
import Langlands.Automorphic.TensorHorizontal

/-!
# Tensor coefficients on actual automorphic operator quotients

The coefficient representation is specified explicitly. This internal
underlying-space construction provides no coefficient differential or cohomology.
-/

noncomputable section

universe uF v w

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Langlands.Automorphic

open Langlands.Global TensorProduct

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}

local instance quotientTensorHorizontalRationalGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance quotientTensorHorizontalContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance quotientTensorHorizontalSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance quotientTensorHorizontalFormGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance quotientTensorHorizontalStableGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance quotientTensorHorizontalRealizationGroup (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

namespace OperatorSubquotient

variable (Q : OperatorSubquotient F n)
  {V : Type v} [AddCommGroup V] [Module ℂ V]
  {W : Type w} [AddCommGroup W] [Module ℂ W]

/-- The diagonal full-compact action on the actual quotient tensored with coefficients. -/
def tensorCompactRepresentation
    (τ : Representation ℂ (standardInfiniteCompact F n) V) :
    Representation ℂ (standardInfiniteCompact F n) (Q.Space ⊗[ℂ] V) :=
  Q.compactRepresentation.tprod τ

/-- Finite adelic translation acts on the actual quotient tensor factor alone. -/
def tensorFiniteRepresentation (V : Type v) [AddCommGroup V] [Module ℂ V] :
    Representation ℂ (FiniteAdelicGL F n) (Q.Space ⊗[ℂ] V) :=
  Q.finiteRepresentation.tprod (Representation.trivial ℂ (FiniteAdelicGL F n) V)

@[simp] theorem tensorCompactRepresentation_tmul
    (τ : Representation ℂ (standardInfiniteCompact F n) V)
    (k : standardInfiniteCompact F n) (f : Q.Space) (v : V) :
    Q.tensorCompactRepresentation τ k (f ⊗ₜ[ℂ] v) =
      Q.compactRepresentation k f ⊗ₜ[ℂ] τ k v := rfl

@[simp] theorem tensorFiniteRepresentation_tmul
    (d : FiniteAdelicGL F n) (f : Q.Space) (v : V) :
    Q.tensorFiniteRepresentation V d (f ⊗ₜ[ℂ] v) =
      Q.finiteRepresentation d f ⊗ₜ[ℂ] v := rfl

/-- The two quotient tensor actions commute, with no finiteness hypothesis on coefficients. -/
theorem tensorFiniteRepresentation_compact
    (τ : Representation ℂ (standardInfiniteCompact F n) V)
    (d : FiniteAdelicGL F n) (k : standardInfiniteCompact F n)
    (t : Q.Space ⊗[ℂ] V) :
    Q.tensorFiniteRepresentation V d (Q.tensorCompactRepresentation τ k t) =
      Q.tensorCompactRepresentation τ k (Q.tensorFiniteRepresentation V d t) := by
  have h : Q.tensorFiniteRepresentation V d ∘ₗ Q.tensorCompactRepresentation τ k =
      Q.tensorCompactRepresentation τ k ∘ₗ Q.tensorFiniteRepresentation V d :=
    TensorProduct.ext' fun f v =>
      congrArg (· ⊗ₜ[ℂ] τ k v) (Q.finiteRepresentation_compactRepresentation d k f)
  exact LinearMap.congr_fun h t

/-- Each finite translation is an intertwiner for the diagonal compact action. -/
def tensorFiniteCompactIntertwiner
    (τ : Representation ℂ (standardInfiniteCompact F n) V) (d : FiniteAdelicGL F n) :
    (Q.tensorCompactRepresentation τ).IntertwiningMap (Q.tensorCompactRepresentation τ) where
  toLinearMap := Q.tensorFiniteRepresentation V d
  isIntertwining' k :=
    LinearMap.ext (Q.tensorFiniteRepresentation_compact τ d k)

/-- Actual horizontal full-compact-equivariant alternating maps with quotient tensor values. -/
def tensorHorizontalSubmodule
    (τ : Representation ℂ (standardInfiniteCompact F n) V) (q : ℕ) :
    Submodule ℂ ((ArchimedeanGL.ReducedComplexLieAlgebra F n) [⋀^Fin q]→ₗ[ℂ]
      (Q.Space ⊗[ℂ] V)) :=
  ArchimedeanGL.horizontalEquivariantSubmodule F n (Q.tensorCompactRepresentation τ) q

/-- Postcomposition descends the finite adelic action to the quotient horizontal spaces. -/
def tensorHorizontalFiniteRepresentation
    (τ : Representation ℂ (standardInfiniteCompact F n) V) (q : ℕ) :
    Representation ℂ (FiniteAdelicGL F n) (Q.tensorHorizontalSubmodule τ q) where
  toFun d := ArchimedeanGL.horizontalMapCoefficients F n q
    (Q.tensorFiniteCompactIntertwiner τ d)
  map_one' := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply AlternatingMap.ext
    intro x
    change Q.tensorFiniteRepresentation V 1 (f.val x) = f.val x
    simp
  map_mul' d e := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply AlternatingMap.ext
    intro x
    change Q.tensorFiniteRepresentation V (d * e) (f.val x) =
      Q.tensorFiniteRepresentation V d (Q.tensorFiniteRepresentation V e (f.val x))
    simp only [map_mul, Module.End.mul_apply]

@[simp] theorem tensorHorizontalFiniteRepresentation_apply
    (τ : Representation ℂ (standardInfiniteCompact F n) V) (q : ℕ)
    (d : FiniteAdelicGL F n) (f : Q.tensorHorizontalSubmodule τ q)
    (x : Fin q → ArchimedeanGL.ReducedComplexLieAlgebra F n) :
    (Q.tensorHorizontalFiniteRepresentation τ q d f).val x =
      Q.tensorFiniteRepresentation V d (f.val x) := rfl

/-- Finite translation also restricts to the full-compact fixed quotient tensor vectors. -/
def tensorInvariantsFiniteRepresentation
    (τ : Representation ℂ (standardInfiniteCompact F n) V) :
    Representation ℂ (FiniteAdelicGL F n) (Q.tensorCompactRepresentation τ).invariants where
  toFun d :=
    { toFun := fun t => ⟨Q.tensorFiniteRepresentation V d t.val, by
        intro k
        exact (Q.tensorFiniteRepresentation_compact τ d k t.val).symm.trans
          (congrArg (Q.tensorFiniteRepresentation V d) (t.property k))⟩
      map_add' := fun _ _ => Subtype.ext (map_add _ _ _)
      map_smul' := fun _ _ => Subtype.ext (map_smul _ _ _) }
  map_one' := by
    apply LinearMap.ext
    intro t
    apply Subtype.ext
    change Q.tensorFiniteRepresentation V 1 t.val = t.val
    simp only [map_one, Module.End.one_apply]
  map_mul' d e := by
    apply LinearMap.ext
    intro t
    apply Subtype.ext
    change Q.tensorFiniteRepresentation V (d * e) t.val =
      Q.tensorFiniteRepresentation V d (Q.tensorFiniteRepresentation V e t.val)
    simp only [map_mul, Module.End.mul_apply]

@[simp] theorem tensorInvariantsFiniteRepresentation_apply
    (τ : Representation ℂ (standardInfiniteCompact F n) V)
    (d : FiniteAdelicGL F n) (t : (Q.tensorCompactRepresentation τ).invariants) :
    (Q.tensorInvariantsFiniteRepresentation τ d t).val =
      Q.tensorFiniteRepresentation V d t.val := rfl

/-- Empty-tuple evaluation identifies degree zero equivariantly for finite adeles. -/
def tensorHorizontalDegreeZeroEquiv
    (τ : Representation ℂ (standardInfiniteCompact F n) V) :
    (Q.tensorHorizontalFiniteRepresentation τ 0).Equiv
      (Q.tensorInvariantsFiniteRepresentation τ) :=
  Representation.Equiv.mk
    (ArchimedeanGL.horizontalDegreeZeroEquiv F n (Q.tensorCompactRepresentation τ))
    (fun _ => by
      apply LinearMap.ext
      intro f
      rfl)

@[simp] theorem tensorHorizontalDegreeZeroEquiv_apply
    (τ : Representation ℂ (standardInfiniteCompact F n) V)
    (f : Q.tensorHorizontalSubmodule τ 0) :
    (Q.tensorHorizontalDegreeZeroEquiv τ f).val = f.val 0 := rfl

/-! ### The canonical projection from the numerator -/

/-- The canonical quotient projection tensored with the identity of the coefficients. -/
def tensorCompactProjection (τ : Representation ℂ (standardInfiniteCompact F n) V) :
    (Q.upper.tensorCompactRepresentation τ).IntertwiningMap
      (Q.tensorCompactRepresentation τ) :=
  Q.compactProjection.tensor (Representation.IntertwiningMap.id τ)

@[simp] theorem tensorCompactProjection_tmul
    (τ : Representation ℂ (standardInfiniteCompact F n) V) (f : Q.upper.Space) (v : V) :
    Q.tensorCompactProjection τ (f ⊗ₜ[ℂ] v) = Q.projection f ⊗ₜ[ℂ] v := rfl

/-- The tensor projection is the right tensor of the canonical module quotient map. -/
theorem tensorCompactProjection_toLinearMap
    (τ : Representation ℂ (standardInfiniteCompact F n) V) :
    (Q.tensorCompactProjection τ).toLinearMap =
      LinearMap.rTensor V Q.lower.toSubmodule.mkQ := rfl

/-- The tensor projection also intertwines the finite tensor actions. -/
theorem tensorCompactProjection_finite
    (τ : Representation ℂ (standardInfiniteCompact F n) V)
    (d : FiniteAdelicGL F n) (t : Q.upper.Space ⊗[ℂ] V) :
    Q.tensorCompactProjection τ (Q.upper.tensorFiniteRepresentation V d t) =
      Q.tensorFiniteRepresentation V d (Q.tensorCompactProjection τ t) := by
  induction t using TensorProduct.inductionOn with
  | tmul f v => rfl
  | add a b ha hb => simp only [map_add, ha, hb]

theorem tensorCompactProjection_surjective
    (τ : Representation ℂ (standardInfiniteCompact F n) V) :
    Function.Surjective (Q.tensorCompactProjection τ) :=
  LinearMap.rTensor_surjective V (Submodule.mkQ_surjective Q.lower.toSubmodule)

/-- Right exactness: the kernel is exactly the denominator tensored with the coefficients. -/
theorem tensorCompactProjection_ker
    (τ : Representation ℂ (standardInfiniteCompact F n) V) :
    LinearMap.ker (Q.tensorCompactProjection τ).toLinearMap =
      LinearMap.range (LinearMap.rTensor V Q.lower.toSubmodule.subtype) :=
  rTensor_mkQ V Q.lower.toSubmodule

/-- The quotient tensor space is the numerator tensor space modulo the denominator tensor. -/
def tensorQuotientEquiv (V : Type v) [AddCommGroup V] [Module ℂ V] :
    ((Q.upper.Space ⊗[ℂ] V) ⧸
        LinearMap.range (LinearMap.rTensor V Q.lower.toSubmodule.subtype)) ≃ₗ[ℂ]
      Q.Space ⊗[ℂ] V :=
  rTensor.equiv V (LinearMap.exact_subtype_mkQ Q.lower.toSubmodule)
    (Submodule.mkQ_surjective Q.lower.toSubmodule)

@[simp] theorem tensorQuotientEquiv_mk (f : Q.upper.Space) (v : V) :
    Q.tensorQuotientEquiv V (Submodule.Quotient.mk (f ⊗ₜ[ℂ] v)) =
      Q.projection f ⊗ₜ[ℂ] v := rfl

/-- The tensor projection induces the projection of horizontal finite representations. -/
def tensorHorizontalProjection
    (τ : Representation ℂ (standardInfiniteCompact F n) V) (q : ℕ) :
    (Q.upper.tensorHorizontalFiniteRepresentation τ q).IntertwiningMap
      (Q.tensorHorizontalFiniteRepresentation τ q) where
  toLinearMap := ArchimedeanGL.horizontalMapCoefficients F n q (Q.tensorCompactProjection τ)
  isIntertwining' d := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply AlternatingMap.ext
    intro x
    exact Q.tensorCompactProjection_finite τ d (f.val x)

@[simp] theorem tensorHorizontalProjection_apply
    (τ : Representation ℂ (standardInfiniteCompact F n) V) (q : ℕ)
    (f : Q.upper.tensorHorizontalSubmodule τ q)
    (x : Fin q → ArchimedeanGL.ReducedComplexLieAlgebra F n) :
    (Q.tensorHorizontalProjection τ q f).val x = Q.tensorCompactProjection τ (f.val x) := rfl

/-! ### Whole-operator quotient intertwiners and equivalences -/

variable {Q} {T : OperatorSubquotient F n}
  {τ : Representation ℂ (standardInfiniteCompact F n) V}
  {υ : Representation ℂ (standardInfiniteCompact F n) W}

/-- Forget a whole-operator quotient intertwiner to the actual compact actions. -/
def compactRestrictionMap (L : Q.representation.IntertwiningMap T.representation) :
    Q.compactRepresentation.IntertwiningMap T.compactRepresentation where
  toLinearMap := L.toLinearMap
  isIntertwining' k := L.isIntertwining' (compactOperator F n k)

@[simp] theorem compactRestrictionMap_apply
    (L : Q.representation.IntertwiningMap T.representation) (f : Q.Space) :
    compactRestrictionMap L f = L f := rfl

/-- Forget a whole-operator quotient equivalence to the actual compact actions. -/
def Equivalence.compactRestriction (e : Q.Equivalence T) :
    Q.compactRepresentation.Equiv T.compactRepresentation :=
  Representation.Equiv.mk e.toLinearEquiv
    (fun k => e.toIntertwiningMap.isIntertwining' (compactOperator F n k))

@[simp] theorem Equivalence.compactRestriction_apply (e : Q.Equivalence T) (f : Q.Space) :
    e.compactRestriction f = e f := rfl

/-- Tensor a whole-operator quotient intertwiner with a compact coefficient intertwiner. -/
def tensorCompactMap (L : Q.representation.IntertwiningMap T.representation)
    (A : τ.IntertwiningMap υ) :
    (Q.tensorCompactRepresentation τ).IntertwiningMap (T.tensorCompactRepresentation υ) :=
  (compactRestrictionMap L).tensor A

@[simp] theorem tensorCompactMap_tmul (L : Q.representation.IntertwiningMap T.representation)
    (A : τ.IntertwiningMap υ) (f : Q.Space) (v : V) :
    tensorCompactMap L A (f ⊗ₜ[ℂ] v) = L f ⊗ₜ[ℂ] A v := rfl

theorem tensorCompactMap_finite (L : Q.representation.IntertwiningMap T.representation)
    (A : τ.IntertwiningMap υ) (d : FiniteAdelicGL F n) (t : Q.Space ⊗[ℂ] V) :
    tensorCompactMap L A (Q.tensorFiniteRepresentation V d t) =
      T.tensorFiniteRepresentation W d (tensorCompactMap L A t) := by
  induction t using TensorProduct.inductionOn with
  | tmul f v =>
      simp only [tensorFiniteRepresentation_tmul, tensorCompactMap_tmul]
      exact congrArg (· ⊗ₜ[ℂ] A v)
        (Representation.IntertwiningMap.isIntertwining _ _ L (finiteOperator F n d) f)
  | add a b ha hb => simp only [map_add, ha, hb]

/-- Quotient intertwiners induce intertwiners of the horizontal finite representations. -/
def tensorHorizontalMap (q : ℕ) (L : Q.representation.IntertwiningMap T.representation)
    (A : τ.IntertwiningMap υ) :
    (Q.tensorHorizontalFiniteRepresentation τ q).IntertwiningMap
      (T.tensorHorizontalFiniteRepresentation υ q) where
  toLinearMap := ArchimedeanGL.horizontalMapCoefficients F n q (tensorCompactMap L A)
  isIntertwining' d := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply AlternatingMap.ext
    intro x
    exact tensorCompactMap_finite L A d (f.val x)

@[simp] theorem tensorHorizontalMap_apply
    (q : ℕ) (L : Q.representation.IntertwiningMap T.representation) (A : τ.IntertwiningMap υ)
    (f : Q.tensorHorizontalSubmodule τ q)
    (x : Fin q → ArchimedeanGL.ReducedComplexLieAlgebra F n) :
    (tensorHorizontalMap q L A f).val x = tensorCompactMap L A (f.val x) := rfl

/-- Quotient and coefficient equivalences preserve the tensor compact representations. -/
def tensorCompactEquiv (e : Q.Equivalence T) (a : τ.Equiv υ) :
    (Q.tensorCompactRepresentation τ).Equiv (T.tensorCompactRepresentation υ) :=
  Representation.Equiv.mk (TensorProduct.congr e.toLinearEquiv a.toLinearEquiv)
    (tensorCompactMap e.toIntertwiningMap a.toIntertwiningMap).isIntertwining'

@[simp] theorem tensorCompactEquiv_tmul (e : Q.Equivalence T) (a : τ.Equiv υ)
    (f : Q.Space) (v : V) :
    tensorCompactEquiv e a (f ⊗ₜ[ℂ] v) = e f ⊗ₜ[ℂ] a v := rfl

/-- Quotient and compact coefficient equivalences transport horizontal finite actions. -/
def tensorHorizontalEquiv (q : ℕ) (e : Q.Equivalence T) (a : τ.Equiv υ) :
    (Q.tensorHorizontalFiniteRepresentation τ q).Equiv
      (T.tensorHorizontalFiniteRepresentation υ q) :=
  Representation.Equiv.mk
    (ArchimedeanGL.horizontalCoefficientEquiv F n q (tensorCompactEquiv e a))
    (tensorHorizontalMap q e.toIntertwiningMap a.toIntertwiningMap).isIntertwining'

@[simp] theorem tensorHorizontalEquiv_apply (q : ℕ)
    (e : Q.Equivalence T) (a : τ.Equiv υ)
    (f : Q.tensorHorizontalSubmodule τ q)
    (x : Fin q → ArchimedeanGL.ReducedComplexLieAlgebra F n) :
    (tensorHorizontalEquiv q e a f).val x =
      TensorProduct.congr e.toLinearEquiv a.toLinearEquiv (f.val x) := rfl

end OperatorSubquotient
end Langlands.Automorphic
