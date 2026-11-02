import Langlands.Representation.Aubert.ProductLeviGrothendieck
import Langlands.Representation.Tensor.FiniteEquivalences
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! Finite length and separate exactness of the actual product-Levi tensor functor. -/

noncomputable section

open CategoryTheory
open scoped TensorProduct

namespace Langlands.Aubert.ProductLeviTensorProof

universe uF uV

section Linear

variable (V : Fin 2 → Type uV)
  [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

/-- The indexed binary tensor carrier as the ordinary two-factor tensor carrier. -/
def binaryEquiv : PiTensorProduct ℂ V ≃ₗ[ℂ] (V 0 ⊗[ℂ] V 1) :=
  (FiniteTensor.headTailLinearEquiv ℂ V).trans
    (TensorProduct.congr (LinearEquiv.refl ℂ (V 0))
      (PiTensorProduct.subsingletonEquiv
        (R := ℂ) (s := fun j : Fin 1 => V j.succ) 0))

@[simp]
theorem binaryEquiv_tprod (v : ∀ i, V i) :
    binaryEquiv V (PiTensorProduct.tprod ℂ v) = v 0 ⊗ₜ[ℂ] v 1 := by
  simp [binaryEquiv]

variable {V}
variable {W : Fin 2 → Type uV}
  [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

theorem binaryEquiv_map (f : ∀ i, V i →ₗ[ℂ] W i) (x : PiTensorProduct ℂ V) :
    binaryEquiv W (PiTensorProduct.map f x) =
      TensorProduct.map (f 0) (f 1) (binaryEquiv V x) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c v =>
    simp only [map_smul, PiTensorProduct.map_tprod, binaryEquiv_tprod,
      TensorProduct.map_tmul]
  | add x y hx hy =>
    simp only [map_add, hx, hy]

end Linear

section Transport

variable {U V W U' V' W' : Type uV}
  [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] [AddCommGroup U'] [Module ℂ U']
  [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']

/-- Transport the three linear short-exactness conditions through a diagram
whose vertical maps are actual linear equivalences. -/
theorem shortExact_of_equiv
    (eU : U ≃ₗ[ℂ] U') (eV : V ≃ₗ[ℂ] V') (eW : W ≃ₗ[ℂ] W')
    (f : U →ₗ[ℂ] V) (g : V →ₗ[ℂ] W)
    (i : U' →ₗ[ℂ] V') (q : V' →ₗ[ℂ] W')
    (hf : ∀ x, eV (f x) = i (eU x))
    (hg : ∀ x, eW (g x) = q (eV x))
    (hi : Function.Injective i) (hq : Function.Surjective q)
    (he : Function.Exact i q) :
    Function.Injective f ∧ Function.Surjective g ∧
      LinearMap.range f = LinearMap.ker g := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y h
    apply eU.injective
    apply hi
    rw [← hf, ← hf, h]
  · intro z
    obtain ⟨y, hy⟩ := hq (eW z)
    refine ⟨eV.symm y, eW.injective ?_⟩
    rw [hg, eV.apply_symm_apply, hy]
  · apply Eq.symm
    apply LinearMap.exact_iff.mp
    intro y
    constructor
    · intro hy
      have hqz : q (eV y) = 0 := by rw [← hg, hy, map_zero]
      obtain ⟨x, hx⟩ := (he (eV y)).mp hqz
      refine ⟨eU.symm x, eV.injective ?_⟩
      rw [hf, eU.apply_symm_apply, hx]
    · rintro ⟨x, rfl⟩
      apply eW.injective
      rw [hg, hf, he.apply_apply_eq_zero, map_zero]

end Transport

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
variable {a b : ℕ} (ha : 0 < a) (hb : 0 < b)

/-- The carrier comparison for the actual functor on an actual input pair. -/
def carrierEquiv
    (X : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier) ×
        SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier)) :
    letI := T.topology
    (binaryProductLeviTensorFunctor F T ha hb).obj X ≃ₗ[ℂ] (X.1 ⊗[ℂ] X.2) :=
  letI := T.topology
  binaryEquiv (fun i => (T.binaryPairFamilyFunctor ha hb).obj X i)

/-- Naturality for both supplied arrows and both variable positions. -/
theorem carrierEquiv_naturality
    {X Y : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier) ×
        SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier)}
    (f : letI := T.topology; X ⟶ Y) :
    letI := T.topology
    ∀ x, carrierEquiv F T ha hb Y
        (SmoothRep.hom ((binaryProductLeviTensorFunctor F T ha hb).map f) x) =
      TensorProduct.map (SmoothRep.hom f.1).toLinearMap (SmoothRep.hom f.2).toLinearMap
        (carrierEquiv F T ha hb X x) := by
  let := T.topology
  intro x
  exact binaryEquiv_map
    (fun i => (SmoothRep.hom ((T.binaryPairFamilyFunctor ha hb).map f i)).toLinearMap) x

theorem preservesFiniteLength :
    letI := T.topology
    SmoothRep.PreservesFiniteLength₂
      (binaryProductLeviTensorFunctor.{uF, uV} F T ha hb) := by
  let := T.topology
  intro A B hA hB
  let X := (T.binaryPairFamilyFunctor ha hb).obj (A, B)
  have hXl : ∀ i, (X i).HasFiniteLength := by
    intro i
    fin_cases i
    · exact hA
    · exact hB
  have hXa : ∀ i, (X i).IsAdmissible := by
    intro i
    exact glFiniteLengthAdmissibility F T _ (X i) (hXl i)
  have hmatch := FiniteTensor.padicExternalTensorFactors p F T (a + b) (by omega)
    (GeneralLinear.BlockShape.binary a b ha hb) X X hXa hXa
    (fun i => Classification.ProductLengthProof.selfMatching_of_finiteLength (hXl i))
  obtain ⟨m, s, _, hs, _, _⟩ := hmatch
  exact LengthCriterionProof.isFiniteLength_of_hasCompositionSeriesLength ⟨s, hs⟩

set_option maxHeartbeats 800000 in
theorem preservesShortExactLeft :
    letI := T.topology
    SmoothRep.PreservesFiniteLengthShortExactLeft
      (binaryProductLeviTensorFunctor.{uF, uV} F T ha hb) := by
  let := T.topology
  intro D A B C f g h
  exact shortExact_of_equiv
    (carrierEquiv F T ha hb (A.val, D.val))
    (carrierEquiv F T ha hb (B.val, D.val))
    (carrierEquiv F T ha hb (C.val, D.val))
    _ _ (f.toLinearMap.rTensor D.val) (g.toLinearMap.rTensor D.val)
    (carrierEquiv_naturality F T ha hb
      (CategoryTheory.Prod.mkHom (SmoothRep.ofHom f) (𝟙 D.val)))
    (carrierEquiv_naturality F T ha hb
      (CategoryTheory.Prod.mkHom (SmoothRep.ofHom g) (𝟙 D.val)))
    (Module.Flat.rTensor_preserves_injective_linearMap f.toLinearMap h.1)
    (LinearMap.rTensor_surjective D.val h.2.1)
    (rTensor_exact D.val (LinearMap.exact_iff.mpr h.2.2.symm) h.2.1)

set_option maxHeartbeats 800000 in
theorem preservesShortExactRight :
    letI := T.topology
    SmoothRep.PreservesFiniteLengthShortExactRight
      (binaryProductLeviTensorFunctor.{uF, uV} F T ha hb) := by
  let := T.topology
  intro D A B C f g h
  exact shortExact_of_equiv
    (carrierEquiv F T ha hb (D.val, A.val))
    (carrierEquiv F T ha hb (D.val, B.val))
    (carrierEquiv F T ha hb (D.val, C.val))
    _ _ (f.toLinearMap.lTensor D.val) (g.toLinearMap.lTensor D.val)
    (carrierEquiv_naturality F T ha hb
      (CategoryTheory.Prod.mkHom (𝟙 D.val) (SmoothRep.ofHom f)))
    (carrierEquiv_naturality F T ha hb
      (CategoryTheory.Prod.mkHom (𝟙 D.val) (SmoothRep.ofHom g)))
    (Module.Flat.lTensor_preserves_injective_linearMap f.toLinearMap h.1)
    (LinearMap.lTensor_surjective D.val h.2.1)
    (lTensor_exact D.val (LinearMap.exact_iff.mpr h.2.2.symm) h.2.1)

end Langlands.Aubert.ProductLeviTensorProof

namespace Langlands.Aubert

universe uF uV

/-- Finite-length preservation and separate exactness for the actual external
tensor functor to the positive binary product Levi. -/
theorem productLeviTensorPrerequisites {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    ProductLeviTensorPrerequisitesStatement.{uF, uV} F T ha hb :=
  ⟨ProductLeviTensorProof.preservesFiniteLength F T ha hb,
    ProductLeviTensorProof.preservesShortExactLeft F T ha hb,
    ProductLeviTensorProof.preservesShortExactRight F T ha hb⟩

end Langlands.Aubert
