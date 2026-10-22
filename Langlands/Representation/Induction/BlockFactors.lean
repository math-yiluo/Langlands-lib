import Langlands.Representation.Induction.Parabolic
import Langlands.Representation.Tensor.Finite

/-!
# Normalized induction of block factors

For representations `σ_1, …, σ_r` of the diagonal blocks `GL_{n_i}`, the actual
block Levi acts on their external tensor product, and normalized parabolic
induction from the standard upper block parabolic gives the representation
`i(σ_1, …, σ_r)` of `GL_n`.
-/

noncomputable section

open CategoryTheory
open scoped NNReal

namespace Langlands.GeneralLinear.BlockShape

universe uF uV uW uX

section Tensor

variable {F : Type uF} [CommRing F]
variable {n : ℕ} (B : BlockShape n)
variable {V : Fin B.length → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

/-- The actual block Levi acting on the tensor product of the block factors,
each block on its own factor. -/
abbrev blockTensor (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (V i)) :
    Representation ℂ (B.Levi F) (PiTensorProduct ℂ V) :=
  FiniteTensor.external σ

theorem blockTensor_tprod (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (V i))
    (m : B.Levi F) (v : ∀ i, V i) :
    B.blockTensor σ m (PiTensorProduct.tprod ℂ v) =
      PiTensorProduct.tprod ℂ (fun i => σ i (m i) (v i)) :=
  FiniteTensor.external_tprod σ m v

end Tensor

variable {F : Type uF} [CommRing F] [TopologicalSpace F] [IsTopologicalRing F]
variable {n : ℕ} (B : BlockShape n)
variable {V : Fin B.length → Type uV} {W : Fin B.length → Type uW}
  {X : Fin B.length → Type uX}
variable [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
variable [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]

/-- `i(σ_1, …, σ_r)` for a supplied normalizing Levi character: normalized
parabolic induction of the block tensor product. -/
def productInducedOf (χ : Induction.SmoothCharacter ℂ (B.Levi F))
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (V i)) :
    Representation ℂ (GeneralLinear n F)
      (Induction.SmoothFunctions (B.parabolic F)
        (B.inducingRepresentation χ (B.blockTensor σ))) :=
  B.normalizedInducedOf χ (B.blockTensor σ)

theorem productInducedOf_eq (χ : Induction.SmoothCharacter ℂ (B.Levi F))
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (V i)) :
    B.productInducedOf χ σ = B.normalizedInducedOf χ (B.blockTensor σ) := rfl

/-- The covariance `f (p g) = χ (m) • (σ_1(m_1) ⊗ ⋯ ⊗ σ_r(m_r)) (f g)`, where
`m = (m_1, …, m_r)` is the actual Levi projection of `p`. -/
theorem productInducedOf_covariant (χ : Induction.SmoothCharacter ℂ (B.Levi F))
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (V i))
    (f : Induction.SmoothFunctions (B.parabolic F)
      (B.inducingRepresentation χ (B.blockTensor σ)))
    (p : B.parabolic F) (g : GeneralLinear n F) :
    Induction.eval (B.parabolic F) (B.inducingRepresentation χ (B.blockTensor σ)) f
        ((p : GeneralLinear n F) * g) =
      (χ.toMonoidHom (B.leviProjection F p) : ℂ) •
        B.blockTensor σ (B.leviProjection F p)
          (Induction.eval (B.parabolic F) (B.inducingRepresentation χ (B.blockTensor σ)) f g) :=
  f.1.2 p g

/-- The group acts by right translation. -/
@[simp]
theorem productInducedOf_apply (χ : Induction.SmoothCharacter ℂ (B.Levi F))
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (V i)) (g : GeneralLinear n F)
    (f : Induction.SmoothFunctions (B.parabolic F)
      (B.inducingRepresentation χ (B.blockTensor σ)))
    (x : GeneralLinear n F) :
    Induction.eval (B.parabolic F) (B.inducingRepresentation χ (B.blockTensor σ))
        (B.productInducedOf χ σ g f) x =
      Induction.eval (B.parabolic F) (B.inducingRepresentation χ (B.blockTensor σ)) f
        (x * g) := rfl

theorem isSmooth_productInducedOf (χ : Induction.SmoothCharacter ℂ (B.Levi F))
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (V i)) :
    IsSmooth (B.productInducedOf χ σ) :=
  B.isSmooth_normalizedInducedOf χ _

/-- The induced map of a family of actual block intertwiners. -/
def productInducedOfMap (χ : Induction.SmoothCharacter ℂ (B.Levi F))
    {σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (V i)}
    {τ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (W i)}
    (f : ∀ i, (σ i).IntertwiningMap (τ i)) :
    (B.productInducedOf χ σ).IntertwiningMap (B.productInducedOf χ τ) :=
  B.normalizedInducedOfMap χ (FiniteTensor.externalMap f)

@[simp]
theorem productInducedOfMap_apply (χ : Induction.SmoothCharacter ℂ (B.Levi F))
    {σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (V i)}
    {τ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (W i)}
    (f : ∀ i, (σ i).IntertwiningMap (τ i))
    (φ : Induction.SmoothFunctions (B.parabolic F)
      (B.inducingRepresentation χ (B.blockTensor σ)))
    (x : GeneralLinear n F) :
    Induction.eval (B.parabolic F) (B.inducingRepresentation χ (B.blockTensor τ))
        (B.productInducedOfMap χ f φ) x =
      FiniteTensor.externalMap f
        (Induction.eval (B.parabolic F) (B.inducingRepresentation χ (B.blockTensor σ)) φ x) :=
  rfl

@[simp]
theorem productInducedOfMap_id (χ : Induction.SmoothCharacter ℂ (B.Levi F))
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (V i)) :
    B.productInducedOfMap χ (fun i => Representation.IntertwiningMap.id (σ i)) =
      Representation.IntertwiningMap.id (B.productInducedOf χ σ) := by
  rw [productInducedOfMap, FiniteTensor.externalMap_id, normalizedInducedOfMap_id]
  rfl

theorem productInducedOfMap_comp (χ : Induction.SmoothCharacter ℂ (B.Levi F))
    {σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (V i)}
    {τ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (W i)}
    {υ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (X i)}
    (f : ∀ i, (σ i).IntertwiningMap (τ i)) (g : ∀ i, (τ i).IntertwiningMap (υ i)) :
    B.productInducedOfMap χ (fun i => (g i).comp (f i)) =
      (B.productInducedOfMap χ g).comp (B.productInducedOfMap χ f) := by
  rw [productInducedOfMap, FiniteTensor.externalMap_comp, normalizedInducedOfMap_comp]
  rfl

/-- `i(σ_1, …, σ_r)` as a functor from families of smooth block representations:
the external tensor functor followed by normalized parabolic induction. -/
def productInductionFunctorOf (χ : Induction.SmoothCharacter ℂ (B.Levi F)) :
    (∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F)) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F) :=
  FiniteTensor.externalFunctor ⋙ B.normalizedInductionFunctorOf χ

@[simp]
theorem productInductionFunctorOf_obj (χ : Induction.SmoothCharacter ℂ (B.Levi F))
    (A : ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F)) :
    ((B.productInductionFunctorOf χ).obj A).representation =
      B.productInducedOf χ (fun i => (A i).representation) := rfl

end Langlands.GeneralLinear.BlockShape

namespace Langlands.PadicField.TopologicalData

universe uF uV uW uX

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
variable (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)
variable {V : Fin B.length → Type uV} {W : Fin B.length → Type uW}
  {X : Fin B.length → Type uX}
variable [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
variable [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]

private theorem isTopologicalRing :
    letI := T.topology
    IsTopologicalRing F.Carrier := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  infer_instance

/-- Henniart's `i(σ_1, …, σ_r)` for an actual p-adic field: normalized parabolic
induction, from the standard upper block parabolic with the successive block
sizes, of the tensor product of the block representations. -/
def normalizedProductInduced
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Representation ℂ (GeneralLinear n F.Carrier)
      (Induction.SmoothFunctions (B.parabolic F.Carrier)
        (twist (T.parabolicHalfModulus B)
          ((B.blockTensor σ).comp (B.leviProjection F.Carrier)))) :=
  T.normalizedParabolicInduced B (B.blockTensor σ)

theorem normalizedProductInduced_eq
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i)) :
    T.normalizedProductInduced B σ = T.normalizedParabolicInduced B (B.blockTensor σ) := rfl

/-- The covariance `f (p g) = δ_P(m)^(1/2) (σ_1(m_1) ⊗ ⋯ ⊗ σ_r(m_r)) (f g)`,
with `m = (m_1, …, m_r)` the Levi part of `p`. -/
theorem normalizedProductInduced_covariant
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i))
    (f : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      Induction.SmoothFunctions (B.parabolic F.Carrier)
        (twist (T.parabolicHalfModulus B)
          ((B.blockTensor σ).comp (B.leviProjection F.Carrier))))
    (g : B.parabolic F.Carrier) (x : GeneralLinear n F.Carrier) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Induction.eval (B.parabolic F.Carrier)
        (twist (T.parabolicHalfModulus B)
          ((B.blockTensor σ).comp (B.leviProjection F.Carrier)))
        f ((g : GeneralLinear n F.Carrier) * x) =
      ((NNReal.sqrt (T.leviModulus B (B.leviProjection F.Carrier g) : ℝ≥0) : ℝ) : ℂ) •
        B.blockTensor σ (B.leviProjection F.Carrier g)
          (Induction.eval (B.parabolic F.Carrier)
            (twist (T.parabolicHalfModulus B)
              ((B.blockTensor σ).comp (B.leviProjection F.Carrier))) f x) :=
  T.normalizedParabolicInduced_covariant B (B.blockTensor σ) f g x

theorem isSmooth_normalizedProductInduced
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    IsSmooth (T.normalizedProductInduced B σ) :=
  T.isSmooth_normalizedParabolicInduced B (B.blockTensor σ)

/-- The compactly supported variant of `normalizedProductInduced`. -/
def normalizedProductCompactInduced
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Representation ℂ (GeneralLinear n F.Carrier)
      (Induction.CompactFunctions (B.parabolic F.Carrier)
        (twist (T.parabolicHalfModulus B)
          ((B.blockTensor σ).comp (B.leviProjection F.Carrier)))) :=
  T.normalizedParabolicCompactInduced B (B.blockTensor σ)

/-- The canonical inclusion of the compactly supported variant. -/
def normalizedProductCompactInclusion
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (T.normalizedProductCompactInduced B σ).IntertwiningMap
      (T.normalizedProductInduced B σ) :=
  T.normalizedParabolicCompactInclusion B (B.blockTensor σ)

/-- The induced map of a family of actual block intertwiners. -/
def normalizedProductInducedMap
    {σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i)}
    {τ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (W i)}
    (f : ∀ i, (σ i).IntertwiningMap (τ i)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (T.normalizedProductInduced B σ).IntertwiningMap (T.normalizedProductInduced B τ) :=
  T.normalizedParabolicInducedMap B (FiniteTensor.externalMap f)

theorem normalizedProductInducedMap_id
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    T.normalizedProductInducedMap B (fun i => Representation.IntertwiningMap.id (σ i)) =
      Representation.IntertwiningMap.id (T.normalizedProductInduced B σ) := by
  let := T.topology
  let := T.isTopologicalRing
  exact B.productInducedOfMap_id (T.leviHalfCharacter B) σ

theorem normalizedProductInducedMap_comp
    {σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i)}
    {τ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (W i)}
    {υ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (X i)}
    (f : ∀ i, (σ i).IntertwiningMap (τ i)) (g : ∀ i, (τ i).IntertwiningMap (υ i)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    T.normalizedProductInducedMap B (fun i => (g i).comp (f i)) =
      (T.normalizedProductInducedMap B g).comp (T.normalizedProductInducedMap B f) := by
  let := T.topology
  let := T.isTopologicalRing
  exact B.productInducedOfMap_comp (T.leviHalfCharacter B) f g

/-- `i(σ_1, …, σ_r)` as a functor from families of smooth block representations
to smooth representations of `GL_n(F)`. -/
def normalizedProductInductionFunctor :
    letI := T.topology
    (∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier)) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier) :=
  letI := T.topology
  letI := T.isTopologicalRing
  B.productInductionFunctorOf (T.leviHalfCharacter B)

theorem normalizedProductInductionFunctor_obj
    (A : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier)) :
    letI := T.topology
    ((T.normalizedProductInductionFunctor B).obj A).representation =
      T.normalizedProductInduced B (fun i => (A i).representation) := rfl

end Langlands.PadicField.TopologicalData

namespace Langlands.PadicField

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
variable {n : ℕ} (B : GeneralLinear.BlockShape n)
variable {V : Fin B.length → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

/-- `i(σ_1, …, σ_r)` for the canonical realization of every algebraic p-adic field. -/
abbrev canonicalNormalizedProductInduced
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i)) :=
  F.canonicalTopologicalData.normalizedProductInduced B σ

/-- The canonical block-factor induction functor. -/
abbrev canonicalNormalizedProductInductionFunctor :
    letI := F.canonicalTopologicalData.topology
    (∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier)) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.normalizedProductInductionFunctor B

end Langlands.PadicField
