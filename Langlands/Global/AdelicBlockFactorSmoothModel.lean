import Langlands.Global.AdelicParabolicInductionTopology
import Langlands.Representation.Induction.BlockFactors
import Langlands.Representation.Smooth.SmallRealizationProof
import Mathlib.LinearAlgebra.PiTensorProduct.Basis

/-!
# Smooth adelic block-factor sections in a genuine normed tensor model

A supplied linear equivalence identifies the algebraic indexed tensor with a
normed complex space. No norm on the indexed tensor is selected implicitly.
-/

noncomputable section

universe uF uV uE uW uK

namespace Langlands.Global.AdelicBlockFactorSmoothModel

open NumberField IsDedekindDomain
open Langlands.GeneralLinear AdelicBlockParabolic
open scoped BigOperators

variable (F : Type uF) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)
variable {V : Fin B.length → Type uV}
variable [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (σ : ∀ i, Representation ℂ (AdelicGL F (B.size i)) (V i))
variable (e : PiTensorProduct ℂ V ≃ₗ[ℂ] E)

/-- The genuine block tensor action, transported to the supplied normed model. -/
abbrev coefficientAction : Representation ℂ (FullLevi F B) E :=
  Langlands.transportRepresentation (B.blockTensor σ) e

/-- The supplied identification is an actual equivalence of Levi representations. -/
abbrev coefficientEquiv : (B.blockTensor σ).Equiv (coefficientAction F B σ e) :=
  Langlands.transportRepresentationEquiv (B.blockTensor σ) e

@[simp]
theorem coefficientAction_apply (m : FullLevi F B) (v : E) :
    coefficientAction F B σ e m v = e (B.blockTensor σ m (e.symm v)) := rfl

/-- The transported action still acts on pure tensors one block at a time. -/
theorem coefficientAction_tprod (m : FullLevi F B) (v : ∀ i, V i) :
    coefficientAction F B σ e m (e (PiTensorProduct.tprod ℂ v)) =
      e (PiTensorProduct.tprod ℂ (fun i => σ i (m i) (v i))) := by
  rw [coefficientAction_apply, e.symm_apply_apply, BlockShape.blockTensor_tprod]

/-- Actual coefficient transport on all covariant tensor-valued sections. -/
def sectionEquiv :
    (AdelicParabolicInduction.rightAction F B (B.blockTensor σ)).Equiv
      (AdelicParabolicInduction.rightAction F B (coefficientAction F B σ e)) :=
  Representation.Equiv.mk
    { (AdelicParabolicInduction.sectionMap F B
        (coefficientEquiv F B σ e).toIntertwiningMap).toLinearMap with
      invFun := AdelicParabolicInduction.sectionMap F B
        (coefficientEquiv F B σ e).symm.toIntertwiningMap
      left_inv := by
        intro f
        ext x
        exact e.symm_apply_apply (f.val x)
      right_inv := by
        intro f
        ext x
        exact e.apply_symm_apply (f.val x) }
    (AdelicParabolicInduction.sectionMap F B
      (coefficientEquiv F B σ e).toIntertwiningMap).isIntertwining'

@[simp]
theorem sectionEquiv_apply
    (f : AdelicParabolicInduction.Sections F B (B.blockTensor σ)) (x : AdelicGL F n) :
    (sectionEquiv F B σ e f).val x = e (f.val x) := rfl

@[simp]
theorem sectionEquiv_symm_apply
    (f : AdelicParabolicInduction.Sections F B (coefficientAction F B σ e))
    (x : AdelicGL F n) :
    ((sectionEquiv F B σ e).symm f).val x = e.symm (f.val x) := rfl

/-- Coefficient transport preserves the common finite stabilizer in both directions. -/
def finiteSectionEquiv :
    (AdelicParabolicInduction.finiteSmoothInduced F B (B.blockTensor σ)).Equiv
      (AdelicParabolicInduction.finiteSmoothInduced F B
        (coefficientAction F B σ e)) :=
  Representation.Equiv.mk
    { (AdelicParabolicInduction.finiteSmoothInducedMap F B
        (coefficientEquiv F B σ e).toIntertwiningMap).toLinearMap with
      invFun := AdelicParabolicInduction.finiteSmoothInducedMap F B
        (coefficientEquiv F B σ e).symm.toIntertwiningMap
      left_inv := by
        intro f
        ext x
        exact e.symm_apply_apply (f.val.val x)
      right_inv := by
        intro f
        ext x
        exact e.apply_symm_apply (f.val.val x) }
    (AdelicParabolicInduction.finiteSmoothInducedMap F B
      (coefficientEquiv F B σ e).toIntertwiningMap).isIntertwining'

@[simp]
theorem finiteSectionEquiv_apply
    (f : AdelicParabolicInduction.FiniteSmoothSections F B (B.blockTensor σ))
    (x : AdelicGL F n) :
    (finiteSectionEquiv F B σ e f).val.val x = e (f.val.val x) := rfl

/-- Actual covariant sections with finite smoothness and real-smooth normed-model slices. -/
abbrev SmoothSections :=
  AdelicParabolicInduction.SmoothSections F B (coefficientAction F B σ e)

/-- Actual full adelic right translation on these sections. -/
abbrev smoothInduced : Representation ℂ (AdelicGL F n) (SmoothSections F B σ e) :=
  AdelicParabolicInduction.smoothInduced F B (coefficientAction F B σ e)

/-- Faithfully recover the original algebraic tensor-valued section. -/
def toTensorSections :
    (smoothInduced F B σ e).IntertwiningMap
      (AdelicParabolicInduction.rightAction F B (B.blockTensor σ)) :=
  (sectionEquiv F B σ e).symm.toIntertwiningMap.comp
    (AdelicParabolicInduction.smoothInclusion F B (coefficientAction F B σ e))

@[simp]
theorem toTensorSections_apply (f : SmoothSections F B σ e) (x : AdelicGL F n) :
    (toTensorSections F B σ e f).val x = e.symm (f.val.val x) := rfl

theorem toTensorSections_injective : Function.Injective (toTensorSections F B σ e) :=
  (sectionEquiv F B σ e).symm.toLinearEquiv.injective.comp
    (AdelicParabolicInduction.smoothInclusion_injective F B
      (coefficientAction F B σ e))

/-- The recovered algebraic section has the same common finite stabilizer. -/
theorem toTensorSections_finiteSmooth (f : SmoothSections F B σ e) :
    toTensorSections F B σ e f ∈
      AdelicParabolicInduction.finiteSmoothSubrepresentation F B (B.blockTensor σ) :=
  ((finiteSectionEquiv F B σ e).symm
    ⟨f.val, f.property.2⟩).property

/-- Real smoothness is imposed after the explicit normed-model identification. -/
theorem toTensorSections_infiniteSmooth (f : SmoothSections F B σ e)
    (b : FiniteAdelicGL F n) :
    (fun a => e ((toTensorSections F B σ e f).val (AdelicGL.pair F n a b))) ∈
      ArchimedeanGL.vectorSmoothFunctions F n E := by
  have h := (AdelicParabolicInduction.mem_infiniteSmoothSubrepresentation F B
    (coefficientAction F B σ e) f.val).mp f.property.1 b
  change (fun a => f.val.val (AdelicGL.pair F n a b)) ∈
    ArchimedeanGL.vectorSmoothFunctions F n E at h
  simpa only [toTensorSections_apply, e.apply_symm_apply] using h

/-- Construct a smooth model section from a genuine regular algebraic tensor section. -/
def ofTensorSection
    (f : AdelicParabolicInduction.Sections F B (B.blockTensor σ))
    (hfinite : f ∈
      AdelicParabolicInduction.finiteSmoothSubrepresentation F B (B.blockTensor σ))
    (hinfinite : ∀ b : FiniteAdelicGL F n,
      (fun a => e (f.val (AdelicGL.pair F n a b))) ∈
        ArchimedeanGL.vectorSmoothFunctions F n E) : SmoothSections F B σ e :=
  ⟨sectionEquiv F B σ e f,
    (AdelicParabolicInduction.mem_infiniteSmoothSubrepresentation F B
      (coefficientAction F B σ e) _).mpr hinfinite,
    (finiteSectionEquiv F B σ e ⟨f, hfinite⟩).property⟩

@[simp]
theorem toTensorSections_ofTensorSection
    (f : AdelicParabolicInduction.Sections F B (B.blockTensor σ))
    (hfinite : f ∈
      AdelicParabolicInduction.finiteSmoothSubrepresentation F B (B.blockTensor σ))
    (hinfinite : ∀ b : FiniteAdelicGL F n,
      (fun a => e (f.val (AdelicGL.pair F n a b))) ∈
        ArchimedeanGL.vectorSmoothFunctions F n E) :
    toTensorSections F B σ e (ofTensorSection F B σ e f hfinite hinfinite) = f :=
  (sectionEquiv F B σ e).symm_apply_apply f

/-- Exact image criterion, without a topology on the algebraic tensor. -/
theorem mem_range_toTensorSections
    (f : AdelicParabolicInduction.Sections F B (B.blockTensor σ)) :
    f ∈ Set.range (toTensorSections F B σ e) ↔
      f ∈ AdelicParabolicInduction.finiteSmoothSubrepresentation F B (B.blockTensor σ) ∧
        ∀ b : FiniteAdelicGL F n,
          (fun a => e (f.val (AdelicGL.pair F n a b))) ∈
            ArchimedeanGL.vectorSmoothFunctions F n E := by
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨toTensorSections_finiteSmooth F B σ e s,
      toTensorSections_infiniteSmooth F B σ e s⟩
  · rintro ⟨hfinite, hinfinite⟩
    exact ⟨ofTensorSection F B σ e f hfinite hinfinite,
      toTensorSections_ofTensorSection F B σ e f hfinite hinfinite⟩

/-- The actual normed-model sections with the published compact-open topology. -/
abbrev CompactOpenSections :=
  AdelicParabolicInduction.CompactOpenSections F B (coefficientAction F B σ e)

section ModelChange

variable {W : Type uW} [NormedAddCommGroup W] [NormedSpace ℂ W]
variable (e' : PiTensorProduct ℂ V ≃ₗ[ℂ] W)

/-- The actual coefficient identification between two supplied normed models. -/
def modelChange :
    (coefficientAction F B σ e).Equiv (coefficientAction F B σ e') :=
  (coefficientEquiv F B σ e).symm.trans (coefficientEquiv F B σ e')

@[simp]
theorem modelChange_apply (v : E) :
    modelChange F B σ e e' v = e' (e.symm v) := rfl

@[simp]
theorem modelChange_symm_apply (w : W) :
    (modelChange F B σ e e').symm w = e (e'.symm w) := rfl

variable (h : Continuous (modelChange F B σ e e'))
variable (hInv : Continuous (modelChange F B σ e e').symm)

/-- Compatible continuous models give actual continuously equivalent smooth sections. -/
def compactOpenModelEquiv :
    CompactOpenSections F B σ e ≃L[ℂ] CompactOpenSections F B σ e' where
  toLinearEquiv :=
    { (AdelicParabolicInduction.CompactOpenSections.mapCLM F B
        (modelChange F B σ e e').toIntertwiningMap h).toLinearMap with
      invFun := AdelicParabolicInduction.CompactOpenSections.mapCLM F B
        (modelChange F B σ e e').symm.toIntertwiningMap hInv
      left_inv := by
        intro f
        apply AdelicParabolicInduction.CompactOpenSections.toContinuousMap_injective
          F B (coefficientAction F B σ e)
        ext x
        exact (modelChange F B σ e e').symm_apply_apply
          (AdelicParabolicInduction.CompactOpenSections.toContinuousMap F B
            (coefficientAction F B σ e) f x)
      right_inv := by
        intro f
        apply AdelicParabolicInduction.CompactOpenSections.toContinuousMap_injective
          F B (coefficientAction F B σ e')
        ext x
        exact (modelChange F B σ e e').apply_symm_apply
          (AdelicParabolicInduction.CompactOpenSections.toContinuousMap F B
            (coefficientAction F B σ e') f x) }
  continuous_toFun := (AdelicParabolicInduction.CompactOpenSections.mapCLM F B
    (modelChange F B σ e e').toIntertwiningMap h).continuous
  continuous_invFun := (AdelicParabolicInduction.CompactOpenSections.mapCLM F B
    (modelChange F B σ e e').symm.toIntertwiningMap hInv).continuous

@[simp]
theorem compactOpenModelEquiv_apply (f : CompactOpenSections F B σ e)
    (x : AdelicGL F n) :
    AdelicParabolicInduction.CompactOpenSections.toContinuousMap F B
      (coefficientAction F B σ e') (compactOpenModelEquiv F B σ e e' h hInv f) x =
      e' (e.symm (AdelicParabolicInduction.CompactOpenSections.toContinuousMap F B
        (coefficientAction F B σ e) f x)) := rfl

theorem compactOpenModelEquiv_rightAction (g : AdelicGL F n)
    (f : CompactOpenSections F B σ e) :
    compactOpenModelEquiv F B σ e e' h hInv
      (AdelicParabolicInduction.CompactOpenSections.rightAction F B
        (coefficientAction F B σ e) g f) =
      AdelicParabolicInduction.CompactOpenSections.rightAction F B
        (coefficientAction F B σ e') g
          (compactOpenModelEquiv F B σ e e' h hInv f) :=
  AdelicParabolicInduction.CompactOpenSections.mapCLM_rightAction F B
    (modelChange F B σ e e').toIntertwiningMap h g f

/-- Changing compatible normed models preserves the actual algebraic section. -/
theorem toTensorSections_modelChange (f : CompactOpenSections F B σ e) :
    toTensorSections F B σ e'
      (AdelicParabolicInduction.CompactOpenSections.toSmooth F B
        (coefficientAction F B σ e') (compactOpenModelEquiv F B σ e e' h hInv f)) =
      toTensorSections F B σ e
        (AdelicParabolicInduction.CompactOpenSections.toSmooth F B
          (coefficientAction F B σ e) f) := by
  ext x
  exact e'.symm_apply_apply
    (e.symm (AdelicParabolicInduction.CompactOpenSections.toContinuousMap F B
      (coefficientAction F B σ e) f x))

end ModelChange

section Coordinates

variable {κ : Fin B.length → Type uK} [∀ i, Fintype (κ i)]

/-- A concrete normed model for finite coordinate factors, from the actual tensor basis. -/
def coordinateEquiv :
    PiTensorProduct ℂ (fun i => κ i → ℂ) ≃ₗ[ℂ] ((∀ i, κ i) → ℂ) := by
  classical
  exact (Basis.piTensorProduct (fun i => Pi.basisFun ℂ (κ i))).equivFun

@[simp]
theorem coordinateEquiv_tprod (v : ∀ i, κ i → ℂ) (p : ∀ i, κ i) :
    coordinateEquiv B (PiTensorProduct.tprod ℂ v) p = ∏ i, v i (p i) := by
  classical
  simp [coordinateEquiv, Module.Basis.equivFun_apply,
    Basis.piTensorProduct_repr_tprod_apply]

end Coordinates

end Langlands.Global.AdelicBlockFactorSmoothModel
