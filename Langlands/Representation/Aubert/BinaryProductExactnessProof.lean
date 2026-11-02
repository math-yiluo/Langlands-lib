import Langlands.Representation.Aubert.GradedGrothendieck
import Langlands.Representation.Parabolic.InductionExactnessProof
import Langlands.Representation.Tensor.FiniteEquivalences
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! Exactness of the actual binary normalized product in every natural rank. -/

noncomputable section

open CategoryTheory
open scoped TensorProduct

namespace Langlands.Aubert.BinaryProductExactness

universe uA uB uC uD uE uX uY uZ

section Linear

variable {A : Type uA} {B : Type uB} {C : Type uC}
  {X : Type uX} {Y : Type uY} {Z : Type uZ}
  [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
  [AddCommGroup C] [Module ℂ C] [AddCommGroup X] [Module ℂ X]
  [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Z] [Module ℂ Z]

/-- Transport all three linear exactness conditions through commuting equivalences. -/
theorem exact_of_equiv (eA : X ≃ₗ[ℂ] A) (eB : Y ≃ₗ[ℂ] B) (eC : Z ≃ₗ[ℂ] C)
    (f : A →ₗ[ℂ] B) (g : B →ₗ[ℂ] C) (f' : X →ₗ[ℂ] Y) (g' : Y →ₗ[ℂ] Z)
    (hf : ∀ x, eB (f' x) = f (eA x)) (hg : ∀ y, eC (g' y) = g (eB y))
    (h : Function.Injective f ∧ Function.Surjective g ∧
      LinearMap.range f = LinearMap.ker g) :
    Function.Injective f' ∧ Function.Surjective g' ∧
      LinearMap.range f' = LinearMap.ker g' := by
  refine ⟨?_, ?_, le_antisymm ?_ ?_⟩
  · intro x y hxy
    apply eA.injective
    apply h.1
    simpa only [← hf] using congrArg eB hxy
  · intro z
    obtain ⟨y, hy⟩ := h.2.1 (eC z)
    refine ⟨eB.symm y, eC.injective ?_⟩
    rw [hg, LinearEquiv.apply_symm_apply, hy]
  · rintro _ ⟨x, rfl⟩
    change g' (f' x) = 0
    apply eC.injective
    rw [hg, hf, map_zero]
    have hx : f (eA x) ∈ LinearMap.ker g := by
      rw [← h.2.2]
      exact ⟨_, rfl⟩
    exact hx
  · intro y hy
    have hgy : g (eB y) = 0 := by
      rw [← hg, show g' y = 0 from hy, map_zero]
    have hy' : eB y ∈ LinearMap.range f := by
      rw [h.2.2]
      exact hgy
    obtain ⟨x, hx⟩ := hy'
    refine ⟨eA.symm x, eB.injective ?_⟩
    rw [hf, LinearEquiv.apply_symm_apply, hx]

/-- Tensoring on the right with any complex vector space preserves exactness. -/
theorem rTensor_exact (D : Type uD) [AddCommGroup D] [Module ℂ D]
    (f : A →ₗ[ℂ] B) (g : B →ₗ[ℂ] C)
    (h : Function.Injective f ∧ Function.Surjective g ∧
      LinearMap.range f = LinearMap.ker g) :
    Function.Injective (f.rTensor D) ∧ Function.Surjective (g.rTensor D) ∧
      LinearMap.range (f.rTensor D) = LinearMap.ker (g.rTensor D) :=
  ⟨Module.Flat.rTensor_preserves_injective_linearMap f h.1,
    LinearMap.rTensor_surjective D h.2.1,
    (_root_.rTensor_exact D (LinearMap.exact_iff.mpr h.2.2.symm)
      h.2.1).linearMap_ker_eq.symm⟩

/-- Tensoring on the left with any complex vector space preserves exactness. -/
theorem lTensor_exact (D : Type uD) [AddCommGroup D] [Module ℂ D]
    (f : A →ₗ[ℂ] B) (g : B →ₗ[ℂ] C)
    (h : Function.Injective f ∧ Function.Surjective g ∧
      LinearMap.range f = LinearMap.ker g) :
    Function.Injective (f.lTensor D) ∧ Function.Surjective (g.lTensor D) ∧
      LinearMap.range (f.lTensor D) = LinearMap.ker (g.lTensor D) :=
  ⟨Module.Flat.lTensor_preserves_injective_linearMap f h.1,
    LinearMap.lTensor_surjective D h.2.1,
    (_root_.lTensor_exact D (LinearMap.exact_iff.mpr h.2.2.symm)
      h.2.1).linearMap_ker_eq.symm⟩

end Linear

section TensorModel

variable {G : Type uA} {H : Type uB} {K : Type uC}
  [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
  [Group K] [TopologicalSpace K]

/-- A bifunctor with the natural binary tensor carrier is exact in each variable. -/
theorem tensorModel_exact
    (Φ : (SmoothRep.{0, uA, uX} ℂ G × SmoothRep.{0, uB, uY} ℂ H) ⥤
      SmoothRep.{0, uC, uZ} ℂ K)
    (e : ∀ X, Φ.obj X ≃ₗ[ℂ] X.1 ⊗[ℂ] X.2)
    (he : ∀ {X Y} (f : X ⟶ Y) (v : Φ.obj X),
      e Y (SmoothRep.hom (Φ.map f) v) =
        TensorProduct.map (SmoothRep.hom f.1).toLinearMap
          (SmoothRep.hom f.2).toLinearMap (e X v)) :
    SmoothRep.PreservesFiniteLengthShortExactLeft Φ ∧
      SmoothRep.PreservesFiniteLengthShortExactRight Φ := by
  constructor
  · intro D A B C f g h
    exact exact_of_equiv (e (A.val, D.val)) (e (B.val, D.val)) (e (C.val, D.val))
      (f.toLinearMap.rTensor D.val) (g.toLinearMap.rTensor D.val) _ _
      (fun v => he (CategoryTheory.Prod.mkHom (SmoothRep.ofHom f) (𝟙 D.val)) v)
      (fun v => he (CategoryTheory.Prod.mkHom (SmoothRep.ofHom g) (𝟙 D.val)) v)
      (rTensor_exact D.val f.toLinearMap g.toLinearMap h)
  · intro D A B C f g h
    exact exact_of_equiv (e (D.val, A.val)) (e (D.val, B.val)) (e (D.val, C.val))
      (f.toLinearMap.lTensor D.val) (g.toLinearMap.lTensor D.val) _ _
      (fun v => he (CategoryTheory.Prod.mkHom (𝟙 D.val) (SmoothRep.ofHom f)) v)
      (fun v => he (CategoryTheory.Prod.mkHom (𝟙 D.val) (SmoothRep.ofHom g)) v)
      (lTensor_exact D.val f.toLinearMap g.toLinearMap h)

end TensorModel

section PairTensor

variable (V : Fin 2 → Type uX) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
variable (W : Fin 2 → Type uY) [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

/-- Split a literal two-factor indexed tensor into the ordinary binary tensor. -/
def pairSplit : PiTensorProduct ℂ V ≃ₗ[ℂ] (V 0 ⊗[ℂ] V 1) :=
  (FiniteTensor.headTailLinearEquiv ℂ V).trans
    (TensorProduct.congr (LinearEquiv.refl ℂ (V 0))
      (PiTensorProduct.subsingletonEquiv (R := ℂ) (s := fun j : Fin 1 => V j.succ) 0))

@[simp]
theorem pairSplit_tprod (v : ∀ i, V i) :
    pairSplit V (PiTensorProduct.tprod ℂ v) = v 0 ⊗ₜ[ℂ] v 1 := by
  simp only [pairSplit, LinearEquiv.trans_apply, FiniteTensor.headTailLinearEquiv_tprod,
    TensorProduct.congr_tmul, LinearEquiv.refl_apply,
    PiTensorProduct.subsingletonEquiv_apply_tprod]
  rfl

theorem pairSplit_map (f : ∀ i, V i →ₗ[ℂ] W i) (v : PiTensorProduct ℂ V) :
    pairSplit W (PiTensorProduct.map f v) =
      TensorProduct.map (f 0) (f 1) (pairSplit V v) := by
  have h :
      (pairSplit W).toLinearMap.comp (PiTensorProduct.map f) =
        (TensorProduct.map (f 0) (f 1)).comp (pairSplit V).toLinearMap := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro w
    change pairSplit W (PiTensorProduct.map f (PiTensorProduct.tprod ℂ w)) =
      TensorProduct.map (f 0) (f 1) (pairSplit V (PiTensorProduct.tprod ℂ w))
    rw [PiTensorProduct.map_tprod, pairSplit_tprod, pairSplit_tprod, TensorProduct.map_tmul]
  exact LinearMap.congr_fun h v

end PairTensor

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The literal positive-rank product is separately exact, using its actual maps. -/
theorem positive_exact {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    letI := T.topology
    SmoothRep.PreservesFiniteLengthShortExactLeft
        (T.binaryPositiveProductFunctor.{uF, uV} ha hb) ∧
      SmoothRep.PreservesFiniteLengthShortExactRight
        (T.binaryPositiveProductFunctor.{uF, uV} ha hb) := by
  let := T.topology
  let Φ := T.binaryPairFamilyFunctor.{uF, uV} ha hb ⋙ FiniteTensor.externalFunctor
  have hTensor :
      SmoothRep.PreservesFiniteLengthShortExactLeft Φ ∧
        SmoothRep.PreservesFiniteLengthShortExactRight Φ :=
    tensorModel_exact Φ
      (fun X => pairSplit (fun i => ((T.binaryPairFamilyFunctor ha hb).obj X i : Type uV)))
      (by
        intro X Y f v
        exact pairSplit_map _ _
          (fun i => (SmoothRep.hom ((T.binaryPairFamilyFunctor ha hb).map f i)).toLinearMap) v)
  constructor
  · intro D A B C f g h
    obtain ⟨hi, hq, hex⟩ := hTensor.1 D A B C f g h
    obtain ⟨hi', hex', hq'⟩ := Parabolic.normalizedInductionExactness F T
      (GeneralLinear.BlockShape.binary a b ha hb)
      (Φ.obj (A.val, D.val)) (Φ.obj (B.val, D.val)) (Φ.obj (C.val, D.val))
      (Φ.obj (A.val, D.val)).representation
      (Φ.obj (B.val, D.val)).representation
      (Φ.obj (C.val, D.val)).representation
      (SmoothRep.hom (Φ.map (CategoryTheory.Prod.mkHom (SmoothRep.ofHom f) (𝟙 D.val))))
      (SmoothRep.hom (Φ.map (CategoryTheory.Prod.mkHom (SmoothRep.ofHom g) (𝟙 D.val))))
      (Φ.obj (A.val, D.val)).isSmooth (Φ.obj (B.val, D.val)).isSmooth
      (Φ.obj (C.val, D.val)).isSmooth hi hq hex
    exact ⟨hi', hq', hex'⟩
  · intro D A B C f g h
    obtain ⟨hi, hq, hex⟩ := hTensor.2 D A B C f g h
    obtain ⟨hi', hex', hq'⟩ := Parabolic.normalizedInductionExactness F T
      (GeneralLinear.BlockShape.binary a b ha hb)
      (Φ.obj (D.val, A.val)) (Φ.obj (D.val, B.val)) (Φ.obj (D.val, C.val))
      (Φ.obj (D.val, A.val)).representation
      (Φ.obj (D.val, B.val)).representation
      (Φ.obj (D.val, C.val)).representation
      (SmoothRep.hom (Φ.map (CategoryTheory.Prod.mkHom (𝟙 D.val) (SmoothRep.ofHom f))))
      (SmoothRep.hom (Φ.map (CategoryTheory.Prod.mkHom (𝟙 D.val) (SmoothRep.ofHom g))))
      (Φ.obj (D.val, A.val)).isSmooth (Φ.obj (D.val, B.val)).isSmooth
      (Φ.obj (D.val, C.val)).isSmooth hi hq hex
    exact ⟨hi', hq', hex'⟩

end Langlands.Aubert.BinaryProductExactness

namespace Langlands.Aubert

universe uF uV

/-- The actual binary normalized product preserves finite-length short exact
sequences in both variables, at every pair of natural ranks. -/
theorem binaryProductExactness {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) :
    BinaryProductExactnessStatement.{uF, uV} F T := by
  let := T.topology
  intro a b
  by_cases ha : a = 0
  · exact BinaryProductExactness.tensorModel_exact _
      (fun X => (T.binaryLeftZeroTensorEquiv ha X).toLinearEquiv)
      (fun f v => T.binaryLeftZeroTensorEquiv_naturality ha f v)
  · by_cases hb : b = 0
    · exact BinaryProductExactness.tensorModel_exact _
        (fun X => (T.binaryRightZeroTensorEquiv hb X).toLinearEquiv)
        (fun f v => T.binaryRightZeroTensorEquiv_naturality hb f v)
    · rw [T.binaryNormalizedProductFunctor_of_pos
        (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hb)]
      exact BinaryProductExactness.positive_exact F T _ _

end Langlands.Aubert
