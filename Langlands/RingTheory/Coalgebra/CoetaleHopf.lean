import Langlands.RingTheory.Coalgebra.PrimitiveGroupLike
import Langlands.RingTheory.Coalgebra.Subcoalgebra.ScalarExtension
import Langlands.RingTheory.Coalgebra.ConvolutionBaseChange
import Langlands.RingTheory.Coalgebra.SeparablyClosedGroupLikeSpanningProof
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Coétale subcoalgebras of Hopf algebras without primitive elements -/

noncomputable section

open Coalgebra TensorProduct

namespace Langlands.CoetaleHopf

variable {k : Type*} [Field k]

/-- A subcoalgebra of a cocommutative coalgebra is cocommutative. -/
theorem isCocomm_subcoalgebra {C : Type*} [AddCommGroup C] [Module k C] [Coalgebra k C]
    [Coalgebra.IsCocomm k C] (D : Langlands.Subcoalgebra k C) : Coalgebra.IsCocomm k D := by
  have hcomm : ∀ t : D ⊗[k] D, D.tensorSquareInclusion (TensorProduct.comm k D D t) =
      TensorProduct.comm k C C (D.tensorSquareInclusion t) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul y z => rfl
    | add y z hy hz => simp only [map_add, hy, hz]
  refine ⟨LinearMap.ext fun x => D.tensorSquareInclusion_injective ?_⟩
  have hsub : D.tensorSquareInclusion (comul (R := k) x) = comul (R := k) (x : C) :=
    D.map_comul_subtype x
  change D.tensorSquareInclusion (TensorProduct.comm k D D (comul (R := k) x)) = _
  rw [hcomm, hsub, Coalgebra.comm_comul, ← hsub]

/-- The convolution dual of a finite-dimensional cocommutative coalgebra is étale as soon as it
is formally unramified. -/
theorem etale_of_formallyUnramified {D : Type*} [AddCommGroup D] [Module k D] [Coalgebra k D]
    [FiniteDimensional k D] [Coalgebra.IsCocomm k D]
    [Algebra.FormallyUnramified k (WithConv (D →ₗ[k] k))] :
    Algebra.Etale k (WithConv (D →ₗ[k] k)) := by
  have : Module.Finite k (WithConv (D →ₗ[k] k)) :=
    Module.Finite.equiv (WithConv.linearEquiv k (D →ₗ[k] k)).symm
  have : Algebra.FormallyEtale k (WithConv (D →ₗ[k] k)) :=
    Algebra.FormallyEtale.of_formallyUnramified_of_field k _
  exact ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩

/-- If the scalar extension of a commutative bialgebra to some field is spanned by group-like
elements, the bialgebra has no nonzero primitive element. -/
theorem eq_zero_of_isPrimitiveElem_of_span_baseChange {A : Type*} [CommRing A] [Bialgebra k A]
    (K : Type*) [Field K] [Algebra k K]
    (hspan : Submodule.span K {x : K ⊗[k] A | IsGroupLikeElem K x} = ⊤)
    (a : A) (ha : Bialgebra.IsPrimitiveElem k a) : a = 0 := by
  have h1 : Bialgebra.IsPrimitiveElem K ((1 : K) ⊗ₜ[k] a) := by
    rw [Bialgebra.isPrimitiveElem_iff_comul_eq_tmul_add_tmul, TensorProduct.comul_tmul,
      CommSemiring.comul_apply, ha.comul_eq_tmul_add_tmul, tmul_add, map_add,
      TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul,
      TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul,
      Algebra.TensorProduct.one_def]
  have h0 := eq_zero_of_isPrimitiveElem_of_mem_span h1 (hspan ▸ Submodule.mem_top)
  apply Algebra.TensorProduct.includeRight_injective (A := K) (algebraMap k K).injective
  rw [Algebra.TensorProduct.includeRight_apply, h0, map_zero]

section Hopf

variable {A : Type*} [CommRing A] [HopfAlgebra k A]

/-- **(b) ⇒ (c), coalgebra form.** In a commutative Hopf algebra over a field without nonzero
primitive elements, every finite-dimensional cocommutative subcoalgebra has an étale convolution
dual. -/
theorem etale_of_noPrimitive (hP : ∀ x : A, Bialgebra.IsPrimitiveElem k x → x = 0)
    (D : Langlands.Subcoalgebra k A) [FiniteDimensional k D] [Coalgebra.IsCocomm k D] :
    Algebra.Etale k (WithConv (D →ₗ[k] k)) := by
  let ka := AlgebraicClosure k
  let j := Langlands.Subcoalgebra.baseChangeMap ka D
  have hPka : ∀ x : ka ⊗[k] A, Bialgebra.IsPrimitiveElem ka x → x = 0 :=
    eq_zero_of_isPrimitiveElem_baseChange hP
  have hSP : ∀ a b : ka ⊗[k] D, IsGroupLikeElem ka a →
      comul (R := ka) b = a ⊗ₜ[ka] b + b ⊗ₜ[ka] a → b = 0 := by
    intro a b ha hb
    apply Langlands.Subcoalgebra.baseChangeMap_injective ka D
    rw [map_zero]
    refine eq_zero_of_comul_eq_of_isGroupLikeElem hPka (ha.map j) ?_
    rw [← CoalgHomClass.map_comp_comul_apply, hb, map_add, TensorProduct.map_tmul,
      TensorProduct.map_tmul]
    rfl
  have hspan := span_isGroupLikeElem_eq_top_of_skewPrimitive hSP
  obtain ⟨ι, ⟨fι⟩, ⟨ePi⟩⟩ := Langlands.CoalgebraDescent.exists_finite_convolutionDualEquivPi hspan
  let e := (Langlands.CoalgebraDescent.convolutionDualBaseChangeEquiv k D ka).trans ePi
  have := Langlands.CoalgebraDescent.formallyUnramified_of_tensorProduct_algEquiv_pi ka e
  exact etale_of_formallyUnramified

end Hopf

section SepClosed

variable {C : Type*} [AddCommGroup C] [Module k C] [Coalgebra k C]
  (Ks : Type*) [Field Ks] [Algebra k Ks] [IsSepClosed Ks]

/-- Over a separably closed extension, the scalar extension of a finite-dimensional coalgebra
with étale convolution dual is spanned by group-like elements. -/
theorem span_baseChange_of_etale {D : Type*} [AddCommGroup D] [Module k D] [Coalgebra k D]
    [FiniteDimensional k D] [Coalgebra.IsCocomm k D]
    [Algebra.Etale k (WithConv (D →ₗ[k] k))] :
    Submodule.span Ks {x : Ks ⊗[k] D | IsGroupLikeElem Ks x} = ⊤ := by
  have : Module.Finite k (WithConv (D →ₗ[k] k)) :=
    Module.Finite.equiv (WithConv.linearEquiv k (D →ₗ[k] k)).symm
  let e1 := (Langlands.CoalgebraDescent.convolutionDualBaseChangeEquiv k D Ks).symm
  let e2 := Algebra.FormallyEtale.equivPiOfIsSepClosed Ks (Ks ⊗[k] WithConv (D →ₗ[k] k))
  exact Langlands.CoalgebraDescent.span_isGroupLikeElem_eq_top_of_algEquiv_pi (e1.trans e2)

/-- **(c) ⇒ (d), coalgebra form.** If every element of a coalgebra lies in a finite-dimensional
cocommutative subcoalgebra with étale convolution dual, then its scalar extension to a separably
closed field is spanned by group-like elements. -/
theorem span_baseChange_of_coetale
    (h : ∀ c : C, ∃ D : Langlands.Subcoalgebra k C, c ∈ D ∧ FiniteDimensional k D ∧
      ∃ _ : Coalgebra.IsCocomm k D, Algebra.Etale k (WithConv (D →ₗ[k] k))) :
    Submodule.span Ks {x : Ks ⊗[k] C | IsGroupLikeElem Ks x} = ⊤ := by
  have hall : ∀ t : Ks ⊗[k] C, t ∈ Submodule.span Ks {x : Ks ⊗[k] C | IsGroupLikeElem Ks x} := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul c a =>
      obtain ⟨D, haD, hfin, hcocomm, hetale⟩ := h a
      have hspan := span_baseChange_of_etale (k := k) Ks (D := D)
      have hmem : (c ⊗ₜ[k] (⟨a, haD⟩ : D) : Ks ⊗[k] D) ∈
          Submodule.span Ks {x : Ks ⊗[k] D | IsGroupLikeElem Ks x} := by
        rw [hspan]
        trivial
      have hle : Submodule.span Ks {x : Ks ⊗[k] D | IsGroupLikeElem Ks x} ≤
          (Submodule.span Ks {x : Ks ⊗[k] C | IsGroupLikeElem Ks x}).comap
            (Langlands.Subcoalgebra.baseChangeMap Ks D).toLinearMap :=
        Submodule.span_le.mpr fun y hy =>
          Submodule.subset_span (hy.map (Langlands.Subcoalgebra.baseChangeMap Ks D))
      have := hle hmem
      rw [Submodule.mem_comap] at this
      change Langlands.Subcoalgebra.baseChangeMap Ks D (c ⊗ₜ[k] (⟨a, haD⟩ : D)) ∈ _ at this
      rwa [Langlands.Subcoalgebra.baseChangeMap_tmul] at this
    | add x y hx hy => exact Submodule.add_mem _ hx hy
  exact eq_top_iff.mpr fun t _ => hall t

end SepClosed

end Langlands.CoetaleHopf
