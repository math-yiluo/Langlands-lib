import Langlands.Representation.Induction.BinaryProduct
import Langlands.Representation.Induction.SingleBlock

/-! Evaluation and the actual unit for normalized products in rank zero. -/

noncomputable section

open CategoryTheory

namespace Langlands.GeneralLinear.BlockShape

theorem isEmpty_blockIndex_rankZero (B : BlockShape 0) : IsEmpty (Fin B.length) :=
  ⟨fun i => Fin.elim0 (B.index i ⟨0, B.positive i⟩)⟩

end Langlands.GeneralLinear.BlockShape

namespace Langlands.PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
variable (T : F.TopologicalData) (B : GeneralLinear.BlockShape 0)
variable {V : Fin B.length → Type uV}
variable [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

/-- Evaluation at identity identifies the actual empty normalized product with
the trivial action on its actual tensor carrier. -/
def emptyProductEvaluationEquiv
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i)) :
    letI := T.topology
    (T.normalizedProductInduced B σ).Equiv
      (Representation.trivial ℂ (GeneralLinear 0 F.Carrier) (PiTensorProduct ℂ V)) := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup 0
  have hP : B.parabolic F.Carrier = ⊤ := by
    apply top_unique
    intro g _
    rw [Subsingleton.elim g 1]
    exact (B.parabolic F.Carrier).one_mem
  exact Induction.smoothInducedTopEquiv (B.parabolic F.Carrier) hP
    (twist (T.parabolicHalfModulus B)
      ((B.blockTensor σ).comp (B.leviProjection F.Carrier)))
    (Representation.trivial ℂ (GeneralLinear 0 F.Carrier) (PiTensorProduct ℂ V))
    (by intro g; rw [Subsingleton.elim g 1, map_one]; rfl)
    BinaryTensor.isSmooth_trivial

@[simp]
theorem emptyProductEvaluationEquiv_apply
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i))
    (f : letI := T.topology
      Induction.SmoothFunctions (B.parabolic F.Carrier)
        (twist (T.parabolicHalfModulus B)
          ((B.blockTensor σ).comp (B.leviProjection F.Carrier)))) :
    T.emptyProductEvaluationEquiv B σ f = f.1.1 1 := rfl

@[simp]
theorem emptyProductEvaluationEquiv_symm_eval
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i))
    (v : PiTensorProduct ℂ V) (g : GeneralLinear 0 F.Carrier) :
    ((T.emptyProductEvaluationEquiv B σ).symm v).1.1 g = v := rfl

/-- The actual empty normalized product is the saturated binary product unit. -/
def emptyProductUnitEquiv
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i)) :
    letI := T.topology
    (T.normalizedProductInduced B σ).Equiv
      (T.binaryProductUnit.{uF, max uF uV}).representation := by
  letI := T.topology
  letI := B.isEmpty_blockIndex_rankZero
  refine (T.emptyProductEvaluationEquiv B σ).trans
    (Representation.Equiv.mk
      ((PiTensorProduct.isEmptyEquiv (R := ℂ) (s := V) (Fin B.length)).trans
        (ULift.moduleEquiv (R := ℂ) (M := ℂ)).symm) ?_)
  intro g
  ext v
  rfl

@[simp]
theorem emptyProductUnitEquiv_apply
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i))
    (f : letI := T.topology
      Induction.SmoothFunctions (B.parabolic F.Carrier)
        (twist (T.parabolicHalfModulus B)
          ((B.blockTensor σ).comp (B.leviProjection F.Carrier)))) :
    letI := B.isEmpty_blockIndex_rankZero
    T.emptyProductUnitEquiv B σ f =
      ULift.up ((PiTensorProduct.isEmptyEquiv (R := ℂ) (s := V)
        (Fin B.length)) (f.1.1 1)) := rfl

@[simp]
theorem emptyProductUnitEquiv_symm_eval
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i))
    (z : ULift.{max uF uV} ℂ) (g : GeneralLinear 0 F.Carrier) :
    letI := B.isEmpty_blockIndex_rankZero
    ((T.emptyProductUnitEquiv B σ).symm z).1.1 g =
      (PiTensorProduct.isEmptyEquiv (R := ℂ) (s := V) (Fin B.length)).symm z.down := rfl

theorem emptyProductUnitEquiv_naturality
    {W : Fin B.length → Type uV}
    [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    {σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i)}
    {τ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (W i)}
    (f : ∀ i, (σ i).IntertwiningMap (τ i))
    (v : letI := T.topology
      Induction.SmoothFunctions (B.parabolic F.Carrier)
        (twist (T.parabolicHalfModulus B)
          ((B.blockTensor σ).comp (B.leviProjection F.Carrier)))) :
    T.emptyProductUnitEquiv B τ (T.normalizedProductInducedMap B f v) =
      T.emptyProductUnitEquiv B σ v := by
  let := T.topology
  let := B.isEmpty_blockIndex_rankZero
  have h :
      (PiTensorProduct.isEmptyEquiv (R := ℂ) (s := W) (Fin B.length)).toLinearMap.comp
        (FiniteTensor.externalMap f).toLinearMap =
      (PiTensorProduct.isEmptyEquiv (R := ℂ) (s := V) (Fin B.length)).toLinearMap := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro w
    simp [FiniteTensor.externalMap_tprod]
  change ULift.up
      ((PiTensorProduct.isEmptyEquiv (R := ℂ) (s := W) (Fin B.length))
        (FiniteTensor.externalMap f (v.1.1 1))) =
    ULift.up ((PiTensorProduct.isEmptyEquiv (R := ℂ) (s := V) (Fin B.length)) (v.1.1 1))
  exact congrArg ULift.up (DFunLike.congr_fun h (v.1.1 1))

/-- The smooth isomorphism retains the original factor universe and the
induced carrier universe `max uF uV`. -/
def emptyProductUnitIso
    (A : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier)) :
    letI := T.topology
    (T.normalizedProductInductionFunctor B).obj A ≅
      T.binaryProductUnit.{uF, max uF uV} :=
  letI := T.topology
  SmoothRep.mkIso (T.emptyProductUnitEquiv B (fun i => (A i).representation))

end Langlands.PadicField.TopologicalData
