import Langlands.Representation.Induction.BinaryProduct
import Langlands.Representation.Induction.SplitStagesComparison
import Langlands.Representation.Induction.CompactQuotientProof
import Langlands.Representation.Parabolic.QuotientCompactProof
import Langlands.Representation.Derivative.MirabolicProductRestrictionFactors

/-!
# Compact induction from the binary parabolic is the binary product

For positive ranks `a` and `b`, the binary product `A × B` of smooth
representations of `GL_a(F)` and `GL_b(F)` is smooth induction of
`δ_P^(1/2) (A ⊠ B)` from the upper block parabolic `P` of shape `(a, b)`. Since
`P \ GL_(a+b)(F)` is compact, compact induction from `P` of the same coefficient
is the same representation. Any coefficient `κ` on a space `W` with a linear
identification `W ≃ A ⊗ B` carrying `κ(q)` to `δ_P^(1/2)(q) A(q₀) ⊗ B(q₁)` gives
compact induction from `P` isomorphic to `A × B`, naturally in `(A, B)`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open scoped TensorProduct

namespace Langlands.PadicField.TopologicalData

open GeneralLinear

universe uF uV uW uW'

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
variable {a b : ℕ} (ha : 0 < a) (hb : 0 < b)

/-- The two factor carriers of `(A, B)` on the binary shape. -/
abbrev binaryPositiveFactors
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)) : Fin 2 → Type uV :=
  letI := T.topology
  fun i => ((T.binaryPairFamilyFunctor ha hb).obj X i : Type uV)

/-- The block tensor of `(A, B)` is `A ⊗ B`. -/
abbrev binaryPositiveTensorEquiv
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)) :
    PiTensorProduct ℂ (T.binaryPositiveFactors ha hb X) ≃ₗ[ℂ] (X.1 ⊗[ℂ] X.2) :=
  FiniteTensor.binaryLinearEquiv ℂ (T.binaryPositiveFactors ha hb X)

/-- The inducing coefficient `δ_P^(1/2) (A ⊠ B)` of the binary product, on the
block tensor. -/
abbrev binaryPositiveCoefficient
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)) :
    Representation ℂ ((BlockShape.binary a b ha hb).parabolic F.Carrier)
      (PiTensorProduct ℂ (T.binaryPositiveFactors ha hb X)) :=
  letI := T.topology
  twist (T.parabolicHalfModulus (BlockShape.binary a b ha hb))
    (((BlockShape.binary a b ha hb).blockTensor
        (fun i => ((T.binaryPairFamilyFunctor ha hb).obj X i).representation)).comp
      ((BlockShape.binary a b ha hb).leviProjection F.Carrier))

/-- On `A ⊗ B` the inducing coefficient acts by `δ_P^(1/2)(q) A(q₀) ⊗ B(q₁)`. -/
theorem binaryPositiveCoefficient_tensor
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier))
    (q : (BlockShape.binary a b ha hb).parabolic F.Carrier)
    (x : PiTensorProduct ℂ (T.binaryPositiveFactors ha hb X)) :
    letI := T.topology
    T.binaryPositiveTensorEquiv ha hb X (T.binaryPositiveCoefficient ha hb X q x) =
      (T.parabolicHalfModulus (BlockShape.binary a b ha hb) q : ℂ) •
        TensorProduct.map
          (X.1.representation ((BlockShape.binary a b ha hb).leviProjection F.Carrier q (0 : Fin 2)))
          (X.2.representation ((BlockShape.binary a b ha hb).leviProjection F.Carrier q (1 : Fin 2)))
          (T.binaryPositiveTensorEquiv ha hb X x) := by
  let _ := T.topology
  change FiniteTensor.binaryLinearEquiv ℂ (T.binaryPositiveFactors ha hb X)
      ((T.parabolicHalfModulus (BlockShape.binary a b ha hb) q : ℂ) •
        FiniteTensor.external
          (fun i => ((T.binaryPairFamilyFunctor ha hb).obj X i).representation)
          ((BlockShape.binary a b ha hb).leviProjection F.Carrier q) x) = _
  exact (map_smul (FiniteTensor.binaryLinearEquiv ℂ (T.binaryPositiveFactors ha hb X)) _ _).trans
    (congrArg _ (FiniteTensor.binaryLinearEquiv_external (R := ℂ)
      (V := T.binaryPositiveFactors ha hb X)
      (H := fun i : Fin 2 => GeneralLinear ((BlockShape.binary a b ha hb).size i) F.Carrier)
      (fun i => ((T.binaryPairFamilyFunctor ha hb).obj X i).representation)
      ((BlockShape.binary a b ha hb).leviProjection F.Carrier q) x))

/-- The coefficient map of a pair of morphisms: the external tensor of the two maps. -/
def binaryPositiveCoefficientMap
    {X Y : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)}
    (f : letI := T.topology; X ⟶ Y) :
    (T.binaryPositiveCoefficient ha hb X).IntertwiningMap
      (T.binaryPositiveCoefficient ha hb Y) :=
  letI := T.topology
  twistIntertwining _
    { toLinearMap := (FiniteTensor.externalMap
        (fun i => SmoothRep.hom ((T.binaryPairFamilyFunctor ha hb).map f i))).toLinearMap
      isIntertwining' := fun q => (FiniteTensor.externalMap
        (fun i => SmoothRep.hom ((T.binaryPairFamilyFunctor ha hb).map f i))).isIntertwining'
          ((BlockShape.binary a b ha hb).leviProjection F.Carrier q) }

/-- On `A ⊗ B` the coefficient map of `(f₁, f₂)` is `f₁ ⊗ f₂`. -/
theorem binaryPositiveCoefficientMap_tensor
    {X Y : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)}
    (f : letI := T.topology; X ⟶ Y) (x : PiTensorProduct ℂ (T.binaryPositiveFactors ha hb X)) :
    letI := T.topology
    T.binaryPositiveTensorEquiv ha hb Y (T.binaryPositiveCoefficientMap ha hb f x) =
      TensorProduct.map (SmoothRep.hom f.1).toLinearMap (SmoothRep.hom f.2).toLinearMap
        (T.binaryPositiveTensorEquiv ha hb X x) := by
  let _ := T.topology
  exact FiniteTensor.binaryLinearEquiv_externalMap
    (fun i => SmoothRep.hom ((T.binaryPairFamilyFunctor ha hb).map f i)) x

/-- Compact induction of the inducing coefficient from the binary parabolic is the
binary product: the inclusion of compactly supported functions is bijective since
`P \ GL_(a+b)(F)` is compact. -/
def binaryPositiveCompactEquiv
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (a + b)
    Representation.Equiv
      (Induction.compactInduced ((BlockShape.binary a b ha hb).parabolic F.Carrier)
        (T.binaryPositiveCoefficient ha hb X))
      ((T.binaryPositiveProductFunctor ha hb).obj X).representation :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (a + b)
  letI : CompactSpace (Induction.LeftQuotient
      ((BlockShape.binary a b ha hb).parabolic F.Carrier)) :=
    Parabolic.parabolicQuotientCompact F T (BlockShape.binary a b ha hb)
  (Induction.compactInclusion ((BlockShape.binary a b ha hb).parabolic F.Carrier)
      (T.binaryPositiveCoefficient ha hb X)).ofBijective
    (Induction.compactInclusion_bijective_of_compactSpace _ _)

/-- The identification forgets compact support. -/
theorem binaryPositiveCompactEquiv_apply
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier))
    (u : letI := T.topology
      letI := T.generalLinearTopologicalGroup (a + b)
      Induction.CompactFunctions ((BlockShape.binary a b ha hb).parabolic F.Carrier)
        (T.binaryPositiveCoefficient ha hb X)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (a + b)
    T.binaryPositiveCompactEquiv ha hb X u = u.val := rfl

/-- The identification is natural in `(A, B)`. -/
theorem binaryPositiveCompactEquiv_natural
    {X Y : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)}
    (f : letI := T.topology; X ⟶ Y)
    (u : letI := T.topology
      letI := T.generalLinearTopologicalGroup (a + b)
      Induction.CompactFunctions ((BlockShape.binary a b ha hb).parabolic F.Carrier)
        (T.binaryPositiveCoefficient ha hb X)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (a + b)
    T.binaryPositiveCompactEquiv ha hb Y
        (Induction.compactInducedMap ((BlockShape.binary a b ha hb).parabolic F.Carrier)
          (T.binaryPositiveCoefficientMap ha hb f) u) =
      SmoothRep.hom ((T.binaryPositiveProductFunctor ha hb).map f)
        (T.binaryPositiveCompactEquiv ha hb X u) := rfl

section Coefficient

variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- A coefficient identified with `A ⊗ B`, with `κ(q)` carried to
`δ_P^(1/2)(q) A(q₀) ⊗ B(q₁)`, is equivalent to the inducing coefficient. -/
def binaryPositiveCoefficientEquivOf
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier))
    (κ : Representation ℂ ((BlockShape.binary a b ha hb).parabolic F.Carrier) W)
    (e : letI := T.topology; W ≃ₗ[ℂ] (X.1 ⊗[ℂ] X.2))
    (he : letI := T.topology; ∀ (q : (BlockShape.binary a b ha hb).parabolic F.Carrier) (w : W),
      e (κ q w) = (T.parabolicHalfModulus (BlockShape.binary a b ha hb) q : ℂ) •
        TensorProduct.map
          (X.1.representation ((BlockShape.binary a b ha hb).leviProjection F.Carrier q (0 : Fin 2)))
          (X.2.representation ((BlockShape.binary a b ha hb).leviProjection F.Carrier q (1 : Fin 2)))
          (e w)) :
    κ.Equiv (T.binaryPositiveCoefficient ha hb X) where
  toLinearEquiv := e.trans (T.binaryPositiveTensorEquiv ha hb X).symm
  isIntertwining' q := by
    let _ := T.topology
    apply LinearMap.ext
    intro w
    change (T.binaryPositiveTensorEquiv ha hb X).symm (e (κ q w)) =
      T.binaryPositiveCoefficient ha hb X q ((T.binaryPositiveTensorEquiv ha hb X).symm (e w))
    apply (T.binaryPositiveTensorEquiv ha hb X).injective
    rw [LinearEquiv.apply_symm_apply, binaryPositiveCoefficient_tensor,
      LinearEquiv.apply_symm_apply, he]

@[simp]
theorem binaryPositiveCoefficientEquivOf_apply
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier))
    (κ : Representation ℂ ((BlockShape.binary a b ha hb).parabolic F.Carrier) W)
    (e : letI := T.topology; W ≃ₗ[ℂ] (X.1 ⊗[ℂ] X.2))
    (he : letI := T.topology; ∀ (q : (BlockShape.binary a b ha hb).parabolic F.Carrier) (w : W),
      e (κ q w) = (T.parabolicHalfModulus (BlockShape.binary a b ha hb) q : ℂ) •
        TensorProduct.map
          (X.1.representation ((BlockShape.binary a b ha hb).leviProjection F.Carrier q (0 : Fin 2)))
          (X.2.representation ((BlockShape.binary a b ha hb).leviProjection F.Carrier q (1 : Fin 2)))
          (e w))
    (w : W) :
    T.binaryPositiveCoefficientEquivOf ha hb X κ e he w =
      (T.binaryPositiveTensorEquiv ha hb X).symm (e w) := rfl

/-- Compact induction from the binary parabolic of a coefficient identified with
`δ_P^(1/2) (A ⊠ B)` on `A ⊗ B` is the binary product `A × B`. -/
def binaryPositiveCompactEquivOf
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier))
    (κ : Representation ℂ ((BlockShape.binary a b ha hb).parabolic F.Carrier) W)
    (e : letI := T.topology; W ≃ₗ[ℂ] (X.1 ⊗[ℂ] X.2))
    (he : letI := T.topology; ∀ (q : (BlockShape.binary a b ha hb).parabolic F.Carrier) (w : W),
      e (κ q w) = (T.parabolicHalfModulus (BlockShape.binary a b ha hb) q : ℂ) •
        TensorProduct.map
          (X.1.representation ((BlockShape.binary a b ha hb).leviProjection F.Carrier q (0 : Fin 2)))
          (X.2.representation ((BlockShape.binary a b ha hb).leviProjection F.Carrier q (1 : Fin 2)))
          (e w)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (a + b)
    Representation.Equiv
      (Induction.compactInduced ((BlockShape.binary a b ha hb).parabolic F.Carrier) κ)
      ((T.binaryPositiveProductFunctor ha hb).obj X).representation :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (a + b)
  (Induction.compactInducedEquiv ((BlockShape.binary a b ha hb).parabolic F.Carrier)
      (T.binaryPositiveCoefficientEquivOf ha hb X κ e he)).trans
    (T.binaryPositiveCompactEquiv ha hb X)

/-- The value of the identification at `x` is `e(u(x))`, read in the block tensor. -/
theorem binaryPositiveCompactEquivOf_eval
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier))
    (κ : Representation ℂ ((BlockShape.binary a b ha hb).parabolic F.Carrier) W)
    (e : letI := T.topology; W ≃ₗ[ℂ] (X.1 ⊗[ℂ] X.2))
    (he : letI := T.topology; ∀ (q : (BlockShape.binary a b ha hb).parabolic F.Carrier) (w : W),
      e (κ q w) = (T.parabolicHalfModulus (BlockShape.binary a b ha hb) q : ℂ) •
        TensorProduct.map
          (X.1.representation ((BlockShape.binary a b ha hb).leviProjection F.Carrier q (0 : Fin 2)))
          (X.2.representation ((BlockShape.binary a b ha hb).leviProjection F.Carrier q (1 : Fin 2)))
          (e w))
    (u : letI := T.topology
      letI := T.generalLinearTopologicalGroup (a + b)
      Induction.CompactFunctions ((BlockShape.binary a b ha hb).parabolic F.Carrier) κ)
    (x : GeneralLinear (a + b) F.Carrier) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (a + b)
    Induction.eval ((BlockShape.binary a b ha hb).parabolic F.Carrier)
        (T.binaryPositiveCoefficient ha hb X)
        (T.binaryPositiveCompactEquivOf ha hb X κ e he u) x =
      (T.binaryPositiveTensorEquiv ha hb X).symm
        (e (Induction.eval ((BlockShape.binary a b ha hb).parabolic F.Carrier) κ u.val x)) :=
  rfl

variable {W' : Type uW'} [AddCommGroup W'] [Module ℂ W']

/-- The identification is natural for a coefficient intertwiner lying over a pair
of morphisms `f = (f₁, f₂)`, i.e. carried to `f₁ ⊗ f₂` on `A ⊗ B`. -/
theorem binaryPositiveCompactEquivOf_natural
    {X Y : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)}
    (f : letI := T.topology; X ⟶ Y)
    (κ : Representation ℂ ((BlockShape.binary a b ha hb).parabolic F.Carrier) W)
    (e : letI := T.topology; W ≃ₗ[ℂ] (X.1 ⊗[ℂ] X.2))
    (he : letI := T.topology; ∀ (q : (BlockShape.binary a b ha hb).parabolic F.Carrier) (w : W),
      e (κ q w) = (T.parabolicHalfModulus (BlockShape.binary a b ha hb) q : ℂ) •
        TensorProduct.map
          (X.1.representation ((BlockShape.binary a b ha hb).leviProjection F.Carrier q (0 : Fin 2)))
          (X.2.representation ((BlockShape.binary a b ha hb).leviProjection F.Carrier q (1 : Fin 2)))
          (e w))
    (κ' : Representation ℂ ((BlockShape.binary a b ha hb).parabolic F.Carrier) W')
    (e' : letI := T.topology; W' ≃ₗ[ℂ] (Y.1 ⊗[ℂ] Y.2))
    (he' : letI := T.topology; ∀ (q : (BlockShape.binary a b ha hb).parabolic F.Carrier) (w : W'),
      e' (κ' q w) = (T.parabolicHalfModulus (BlockShape.binary a b ha hb) q : ℂ) •
        TensorProduct.map
          (Y.1.representation ((BlockShape.binary a b ha hb).leviProjection F.Carrier q (0 : Fin 2)))
          (Y.2.representation ((BlockShape.binary a b ha hb).leviProjection F.Carrier q (1 : Fin 2)))
          (e' w))
    (t : κ.IntertwiningMap κ')
    (ht : letI := T.topology; ∀ w, e' (t w) =
      TensorProduct.map (SmoothRep.hom f.1).toLinearMap (SmoothRep.hom f.2).toLinearMap (e w))
    (u : letI := T.topology
      letI := T.generalLinearTopologicalGroup (a + b)
      Induction.CompactFunctions ((BlockShape.binary a b ha hb).parabolic F.Carrier) κ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (a + b)
    T.binaryPositiveCompactEquivOf ha hb Y κ' e' he'
        (Induction.compactInducedMap ((BlockShape.binary a b ha hb).parabolic F.Carrier) t u) =
      SmoothRep.hom ((T.binaryPositiveProductFunctor ha hb).map f)
        (T.binaryPositiveCompactEquivOf ha hb X κ e he u) := by
  let _ := T.topology
  let _ := T.generalLinearTopologicalGroup (a + b)
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change (T.binaryPositiveTensorEquiv ha hb Y).symm
      (e' (t (Induction.eval ((BlockShape.binary a b ha hb).parabolic F.Carrier) κ u.val x))) =
    T.binaryPositiveCoefficientMap ha hb f ((T.binaryPositiveTensorEquiv ha hb X).symm
      (e (Induction.eval ((BlockShape.binary a b ha hb).parabolic F.Carrier) κ u.val x)))
  apply (T.binaryPositiveTensorEquiv ha hb Y).injective
  rw [LinearEquiv.apply_symm_apply, binaryPositiveCoefficientMap_tensor,
    LinearEquiv.apply_symm_apply, ht]

end Coefficient

end Langlands.PadicField.TopologicalData
