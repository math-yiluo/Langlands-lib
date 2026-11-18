import Langlands.Algebra.SemisimpleScalarExtensionStatement
import Langlands.Algebra.CentralSimpleScalarExtension
import Mathlib.Algebra.Algebra.Subalgebra.Pi
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.SimpleRing.Field
import Mathlib.RingTheory.TensorProduct.Pi

/-! # Semisimplicity after scalar extension -/

namespace Langlands.Algebra

universe uk uK uA

open scoped TensorProduct
open Algebra.TensorProduct

/-- The centre of a product is the product of the centres. -/
private def centerPiEquiv (k : Type*) [Field k] {ι : Type*} (B : ι → Type*)
    [∀ i, Ring (B i)] [∀ i, Algebra k (B i)] :
    Subalgebra.center k (∀ i, B i) ≃ₐ[k] ∀ i, Subalgebra.center k (B i) where
  toFun z i := ⟨z.val i, by
    let f : ∀ i, B i := z.val
    have hf : f ∈ Subalgebra.center k (∀ i, B i) := z.property
    rw [Subalgebra.center_pi] at hf
    exact hf i (Set.mem_univ i)⟩
  invFun z := ⟨fun i => (z i).val, by
    rw [Subalgebra.center_pi]
    exact fun i _ => (z i).property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- A separable algebraic extension gives a reduced tensor over any extension field. -/
private theorem isReduced_tensor_of_isSeparable (k K Z : Type*)
    [Field k] [Field K] [Field Z] [Algebra k K] [Algebra k Z] [Algebra.IsSeparable k K] :
    IsReduced (Z ⊗[k] K) := by
  apply IsReduced.tensorProduct_of_flat_of_forall_fg
  intro D hD
  obtain ⟨s, rfl⟩ := hD
  rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
    (fun x _ => Algebra.IsAlgebraic.isAlgebraic (R := k) x)]
  let L := IntermediateField.adjoin k (s : Set K)
  change IsReduced (Z ⊗[k] L)
  have : FiniteDimensional k L :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsSeparable.isIntegral k x
  have : Algebra.IsSeparable k L := Algebra.IsSeparable.of_algHom k K L.val
  have : Algebra.FormallyUnramified k L := Algebra.FormallyUnramified.of_isSeparable k L
  exact Algebra.FormallyUnramified.isReduced_of_field Z (Z ⊗[k] L)

/-- A central simple algebra extends to a product of simple Artinian rings when its extended
centre is reduced. -/
private theorem isSemisimpleRing_baseChange_of_centerField (k K Z B : Type*)
    [Field k] [Field K] [Field Z] [Ring B] [Algebra k K] [Algebra k Z] [Algebra k B]
    [Algebra Z B] [IsScalarTower k Z B] [FiniteDimensional k Z] [FiniteDimensional Z B]
    [Algebra.IsCentral Z B] [IsSimpleRing B]
    (h : Algebra.IsSeparable k K ∨ Algebra.FormallyEtale k Z) :
    IsSemisimpleRing (K ⊗[k] B) := by
  classical
  let C := Z ⊗[k] K
  let algebraKC : Algebra K C := rightAlgebra
  have : Module.Finite K C := Module.Finite.equiv (commRight k K Z).toLinearEquiv
  have : IsArtinianRing C := IsArtinianRing.of_finite K C
  have : IsReduced C := by
    rcases h with hsep | hetale
    · exact isReduced_tensor_of_isSeparable k K Z
    · have : IsReduced (K ⊗[k] Z) :=
        Algebra.FormallyUnramified.isReduced_of_field K _
      let flip := Algebra.TensorProduct.comm k Z K
      exact isReduced_of_injective flip flip.injective
  let F (i : MaximalSpectrum C) := C ⧸ i.asIdeal
  let fieldF (i : MaximalSpectrum C) : Field (F i) :=
    IsArtinianRing.fieldOfSubtypeIsMaximal C i
  let algebraZC : Algebra Z C := inferInstanceAs (Algebra Z (Z ⊗[k] K))
  let algebraZF (i : MaximalSpectrum C) : Algebra Z (F i) :=
    inferInstanceAs (Algebra Z (C ⧸ i.asIdeal))
  have (i : MaximalSpectrum C) : IsScalarTower Z C (F i) :=
    inferInstanceAs (IsScalarTower Z C (C ⧸ i.asIdeal))
  let fintypeSpectrum : Fintype (MaximalSpectrum C) := Fintype.ofFinite _
  let e := (IsArtinianRing.equivPi C).restrictScalars Z
  let eProd : C ⊗[Z] B ≃ₐ[Z] ∀ i, F i ⊗[Z] B :=
    (Algebra.TensorProduct.congr e (.refl : B ≃ₐ[Z] B)).trans <|
      (Algebra.TensorProduct.comm Z (∀ i, F i) B).trans <|
        (piRight Z Z B F).trans <| AlgEquiv.piCongrRight fun i =>
          Algebra.TensorProduct.comm Z B (F i)
  have (i : MaximalSpectrum C) : IsSemisimpleRing (F i ⊗[Z] B) := by
    have := Langlands.CentralSimple.isSimpleRing_baseChange Z B (F i)
    have : IsArtinianRing (F i ⊗[Z] B) := IsArtinianRing.of_finite (F i) _
    infer_instance
  have : IsSemisimpleRing (C ⊗[Z] B) := eProd.symm.toRingEquiv.isSemisimpleRing
  let eBase : C ⊗[Z] B ≃+* K ⊗[k] B :=
    (Algebra.TensorProduct.comm Z C B).toRingEquiv.trans <|
      (Algebra.TensorProduct.assoc k Z Z B Z K).symm.toRingEquiv.trans <|
        (Algebra.TensorProduct.congr (Algebra.TensorProduct.rid Z Z B)
          (.refl : K ≃ₐ[k] K)).toRingEquiv.trans <|
            (Algebra.TensorProduct.comm k B K).toRingEquiv
  exact eBase.isSemisimpleRing

/-- Use the actual centre of a finite-dimensional simple algebra as its central field. -/
private theorem isSemisimpleRing_baseChange_simple (k K B : Type*)
    [Field k] [Field K] [Ring B] [Algebra k K] [Algebra k B]
    [FiniteDimensional k B] [IsSimpleRing B]
    (h : Algebra.IsSeparable k K ∨ Algebra.FormallyEtale k (Subalgebra.center k B)) :
    IsSemisimpleRing (K ⊗[k] B) := by
  let Z := ↥(Subring.center B)
  let fieldZ : Field Z := (IsSimpleRing.isField_center B).toField
  let algebraKZ : Algebra k Z := (Subalgebra.center k B).algebra
  let algebraZB : Algebra Z B := inferInstanceAs (Algebra (Subring.center B) B)
  have : IsScalarTower k Z B := IsScalarTower.of_algebraMap_eq' rfl
  have : FiniteDimensional k Z :=
    inferInstanceAs (Module.Finite k (Subalgebra.center k B))
  have : FiniteDimensional Z B := Module.Finite.of_restrictScalars_finite k Z B
  have : Algebra.IsCentral Z B := ⟨fun x hx => Algebra.mem_bot.mpr ⟨⟨x, hx⟩, rfl⟩⟩
  exact isSemisimpleRing_baseChange_of_centerField k K Z B h

/-- Finite-dimensional semisimple algebras stay semisimple in both cases of the scalar-extension
statement. -/
theorem semisimpleScalarExtension : SemisimpleScalarExtensionStatement.{uk,uK,uA} := by
  classical
  intro k K A _ _ _ _ _ _ hA h
  obtain ⟨n, D, d, hRing, hAlg, hFinite, hSize, ⟨e⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing_finite k A
  let B (i : Fin n) := Matrix (Fin (d i)) (Fin (d i)) (D i)
  have (i : Fin n) : NeZero (d i) := hSize i
  have (i : Fin n) : IsSimpleRing (B i) := inferInstance
  have (i : Fin n) : FiniteDimensional k (B i) := inferInstance
  have (i : Fin n) : IsSemisimpleRing (K ⊗[k] B i) := by
    apply isSemisimpleRing_baseChange_simple
    rcases h with hsep | hetale
    · exact Or.inl hsep
    · right
      let eCenter := (Subalgebra.equivMapOfInjective (Subalgebra.center k A)
        e.toAlgHom e.injective).trans (Subalgebra.equivOfEq _ _ (Subalgebra.map_center_eq e))
      have hPi : Algebra.FormallyEtale k (∀ j, Subalgebra.center k (B j)) :=
        Algebra.FormallyEtale.of_equiv (eCenter.trans (centerPiEquiv k B))
      exact ((Algebra.FormallyEtale.pi_iff (R := k) (fun j => Subalgebra.center k (B j))).mp hPi) i
  let eTensor : K ⊗[k] A ≃ₐ[K] ∀ i, K ⊗[k] B i :=
    (Algebra.TensorProduct.congr (.refl : K ≃ₐ[K] K) e).trans (piRight k K K B)
  exact eTensor.symm.toRingEquiv.isSemisimpleRing

end Langlands.Algebra
