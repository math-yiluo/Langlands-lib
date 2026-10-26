import Langlands.Automorphic.OperatorCompactCompatibility
import Langlands.Global.ArchimedeanHorizontal

/-!
# Tensor coefficients on actual automorphic horizontal spaces

The coefficient representation is specified explicitly. This internal
underlying-space construction provides no coefficient differential or cohomology.
-/

noncomputable section

universe u v w

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Langlands.Automorphic

open Langlands.Global TensorProduct

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance tensorHorizontalRationalAddCommGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance tensorHorizontalContinuousAddCommGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance tensorHorizontalSmoothAddCommGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance tensorHorizontalFormsAddCommGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance tensorHorizontalStableAddCommGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

namespace OperatorRealization

variable (S T : OperatorRealization F n)

local instance tensorHorizontalSpaceAddCommGroup : AddCommGroup S.Space :=
  Submodule.addCommGroup _
local instance tensorHorizontalTargetAddCommGroup : AddCommGroup T.Space :=
  Submodule.addCommGroup _

variable {V : Type v} [AddCommGroup V] [Module ℂ V]
  {W : Type w} [AddCommGroup W] [Module ℂ W]

/-- The diagonal full-compact action on the actual realization tensored with coefficients. -/
def tensorCompactRepresentation
    (τ : Representation ℂ (standardInfiniteCompact F n) V) :
    Representation ℂ (standardInfiniteCompact F n) (S.Space ⊗[ℂ] V) :=
  S.compactRepresentation.tprod τ

/-- Finite adelic translation acts on the actual automorphic tensor factor alone. -/
def tensorFiniteRepresentation (V : Type v) [AddCommGroup V] [Module ℂ V] :
    Representation ℂ (FiniteAdelicGL F n) (S.Space ⊗[ℂ] V) :=
  S.finiteRepresentation.tprod (Representation.trivial ℂ (FiniteAdelicGL F n) V)

@[simp] theorem tensorCompactRepresentation_tmul
    (τ : Representation ℂ (standardInfiniteCompact F n) V)
    (k : standardInfiniteCompact F n) (f : S.Space) (v : V) :
    S.tensorCompactRepresentation τ k (f ⊗ₜ[ℂ] v) =
      S.compactRepresentation k f ⊗ₜ[ℂ] τ k v := rfl

@[simp] theorem tensorFiniteRepresentation_tmul
    (d : FiniteAdelicGL F n) (f : S.Space) (v : V) :
    S.tensorFiniteRepresentation V d (f ⊗ₜ[ℂ] v) =
      S.finiteRepresentation d f ⊗ₜ[ℂ] v := rfl

/-- The two actual tensor actions commute, with no finiteness hypothesis on coefficients. -/
theorem tensorFiniteRepresentation_compact
    (τ : Representation ℂ (standardInfiniteCompact F n) V)
    (d : FiniteAdelicGL F n) (k : standardInfiniteCompact F n)
    (t : S.Space ⊗[ℂ] V) :
    S.tensorFiniteRepresentation V d (S.tensorCompactRepresentation τ k t) =
      S.tensorCompactRepresentation τ k (S.tensorFiniteRepresentation V d t) := by
  induction t using TensorProduct.inductionOn with
  | tmul f v =>
      simp only [tensorCompactRepresentation_tmul, tensorFiniteRepresentation_tmul,
        S.finiteRepresentation_compactRepresentation]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- Each finite translation is an intertwiner for the diagonal compact action. -/
def tensorFiniteCompactIntertwiner
    (τ : Representation ℂ (standardInfiniteCompact F n) V) (d : FiniteAdelicGL F n) :
    (S.tensorCompactRepresentation τ).IntertwiningMap (S.tensorCompactRepresentation τ) where
  toLinearMap := S.tensorFiniteRepresentation V d
  isIntertwining' k :=
    LinearMap.ext (S.tensorFiniteRepresentation_compact τ d k)

/-- Actual horizontal full-compact-equivariant alternating maps with tensor coefficients. -/
def tensorHorizontalSubmodule
    (τ : Representation ℂ (standardInfiniteCompact F n) V) (q : ℕ) :
    Submodule ℂ ((ArchimedeanGL.ReducedComplexLieAlgebra F n) [⋀^Fin q]→ₗ[ℂ]
      (S.Space ⊗[ℂ] V)) :=
  ArchimedeanGL.horizontalEquivariantSubmodule F n (S.tensorCompactRepresentation τ) q

/-- Postcomposition descends the finite adelic action to the actual horizontal spaces. -/
def tensorHorizontalFiniteRepresentation
    (τ : Representation ℂ (standardInfiniteCompact F n) V) (q : ℕ) :
    Representation ℂ (FiniteAdelicGL F n) (S.tensorHorizontalSubmodule τ q) where
  toFun d := ArchimedeanGL.horizontalMapCoefficients F n q
    (S.tensorFiniteCompactIntertwiner τ d)
  map_one' := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply AlternatingMap.ext
    intro x
    change S.tensorFiniteRepresentation V 1 (f.val x) = f.val x
    simp
  map_mul' d e := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply AlternatingMap.ext
    intro x
    change S.tensorFiniteRepresentation V (d * e) (f.val x) =
      S.tensorFiniteRepresentation V d (S.tensorFiniteRepresentation V e (f.val x))
    simp only [map_mul, Module.End.mul_apply]

@[simp] theorem tensorHorizontalFiniteRepresentation_apply
    (τ : Representation ℂ (standardInfiniteCompact F n) V) (q : ℕ)
    (d : FiniteAdelicGL F n) (f : S.tensorHorizontalSubmodule τ q)
    (x : Fin q → ArchimedeanGL.ReducedComplexLieAlgebra F n) :
    (S.tensorHorizontalFiniteRepresentation τ q d f).val x =
      S.tensorFiniteRepresentation V d (f.val x) := rfl

/-- Finite translation also restricts to the full-compact fixed tensor vectors. -/
def tensorInvariantsFiniteRepresentation
    (τ : Representation ℂ (standardInfiniteCompact F n) V) :
    Representation ℂ (FiniteAdelicGL F n) (S.tensorCompactRepresentation τ).invariants where
  toFun d :=
    { toFun := fun t => ⟨S.tensorFiniteRepresentation V d t.val, by
        intro k
        exact (S.tensorFiniteRepresentation_compact τ d k t.val).symm.trans
          (congrArg (S.tensorFiniteRepresentation V d) (t.property k))⟩
      map_add' := fun _ _ => Subtype.ext (map_add _ _ _)
      map_smul' := fun _ _ => Subtype.ext (map_smul _ _ _) }
  map_one' := by
    apply LinearMap.ext
    intro t
    apply Subtype.ext
    change S.tensorFiniteRepresentation V 1 t.val = t.val
    simp only [map_one, Module.End.one_apply]
  map_mul' d e := by
    apply LinearMap.ext
    intro t
    apply Subtype.ext
    change S.tensorFiniteRepresentation V (d * e) t.val =
      S.tensorFiniteRepresentation V d (S.tensorFiniteRepresentation V e t.val)
    simp only [map_mul, Module.End.mul_apply]

/-- Empty-tuple evaluation identifies degree zero equivariantly for finite adeles. -/
def tensorHorizontalDegreeZeroEquiv
    (τ : Representation ℂ (standardInfiniteCompact F n) V) :
    (S.tensorHorizontalFiniteRepresentation τ 0).Equiv
      (S.tensorInvariantsFiniteRepresentation τ) :=
  Representation.Equiv.mk
    (ArchimedeanGL.horizontalDegreeZeroEquiv F n (S.tensorCompactRepresentation τ))
    (fun _ => by
      apply LinearMap.ext
      intro f
      rfl)

@[simp] theorem tensorHorizontalDegreeZeroEquiv_apply
    (τ : Representation ℂ (standardInfiniteCompact F n) V)
    (f : S.tensorHorizontalSubmodule τ 0) :
    (S.tensorHorizontalDegreeZeroEquiv τ f).val = f.val 0 := rfl

variable {S T}
  {τ : Representation ℂ (standardInfiniteCompact F n) V}
  {υ : Representation ℂ (standardInfiniteCompact F n) W}

/-- Tensor a genuine full automorphic intertwiner with a compact coefficient intertwiner. -/
def tensorCompactMap (L : S.Intertwiner T) (A : τ.IntertwiningMap υ) :
    (S.tensorCompactRepresentation τ).IntertwiningMap (T.tensorCompactRepresentation υ) :=
  L.compactRestriction.tensor A

@[simp] theorem tensorCompactMap_tmul (L : S.Intertwiner T) (A : τ.IntertwiningMap υ)
    (f : S.Space) (v : V) :
    tensorCompactMap L A (f ⊗ₜ[ℂ] v) = L f ⊗ₜ[ℂ] A v := rfl

theorem tensorCompactMap_finite (L : S.Intertwiner T) (A : τ.IntertwiningMap υ)
    (d : FiniteAdelicGL F n) (t : S.Space ⊗[ℂ] V) :
    tensorCompactMap L A (S.tensorFiniteRepresentation V d t) =
      T.tensorFiniteRepresentation W d (tensorCompactMap L A t) := by
  induction t using TensorProduct.inductionOn with
  | tmul f v =>
      simp only [tensorFiniteRepresentation_tmul, tensorCompactMap_tmul, L.finite]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- Genuine intertwiners induce intertwiners of the horizontal finite adelic representations. -/
def tensorHorizontalMap (q : ℕ) (L : S.Intertwiner T) (A : τ.IntertwiningMap υ) :
    (S.tensorHorizontalFiniteRepresentation τ q).IntertwiningMap
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
    (q : ℕ) (L : S.Intertwiner T) (A : τ.IntertwiningMap υ)
    (f : S.tensorHorizontalSubmodule τ q)
    (x : Fin q → ArchimedeanGL.ReducedComplexLieAlgebra F n) :
    (tensorHorizontalMap q L A f).val x = tensorCompactMap L A (f.val x) := rfl

/-- Tensor equivalences preserve the compact representations. -/
def tensorCompactEquiv (e : S.Equivalence T) (a : τ.Equiv υ) :
    (S.tensorCompactRepresentation τ).Equiv (T.tensorCompactRepresentation υ) :=
  Representation.Equiv.mk (TensorProduct.congr e.toLinearEquiv a.toLinearEquiv)
    (tensorCompactMap e.toIntertwiningMap a.toIntertwiningMap).isIntertwining'

/-- Full automorphic and compact coefficient equivalences transport horizontal finite actions. -/
def tensorHorizontalEquiv (q : ℕ) (e : S.Equivalence T) (a : τ.Equiv υ) :
    (S.tensorHorizontalFiniteRepresentation τ q).Equiv
      (T.tensorHorizontalFiniteRepresentation υ q) :=
  Representation.Equiv.mk
    (ArchimedeanGL.horizontalCoefficientEquiv F n q (tensorCompactEquiv e a))
    (tensorHorizontalMap q e.toIntertwiningMap a.toIntertwiningMap).isIntertwining'

@[simp] theorem tensorHorizontalEquiv_apply (q : ℕ)
    (e : S.Equivalence T) (a : τ.Equiv υ)
    (f : S.tensorHorizontalSubmodule τ q)
    (x : Fin q → ArchimedeanGL.ReducedComplexLieAlgebra F n) :
    (tensorHorizontalEquiv q e a f).val x =
      TensorProduct.congr e.toLinearEquiv a.toLinearEquiv (f.val x) := rfl

end OperatorRealization
end Langlands.Automorphic
