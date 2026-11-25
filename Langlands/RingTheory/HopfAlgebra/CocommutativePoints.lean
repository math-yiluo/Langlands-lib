module

public import Langlands.RingTheory.HopfAlgebra.PointGroup
public import Langlands.RingTheory.Coalgebra.TensorConvolution
public import Mathlib.RingTheory.Bialgebra.Equiv
public import Mathlib.RingTheory.TensorProduct.Maps

/-! # Testing cocommutativity on the two canonical tensor-valued points

A commutative bialgebra `H` over `R` is cocommutative exactly when its two points with values in
`H ⊗[R] H` given by the tensor inclusions commute in the convolution monoid
(`Langlands.HopfAlgebra.commute_includeLeft_includeRight_iff_isCocomm`). Their product in one
order is the comultiplication; in the other order it is the comultiplication followed by the swap
of the tensor factors.
-/

public section

open WithConv
open scoped TensorProduct

namespace Langlands.HopfAlgebra

variable (R H : Type*) [CommSemiring R] [CommSemiring H] [_root_.Bialgebra R H]

/-- The two tensor-factor points of `H` commute exactly when `H` is cocommutative. -/
theorem commute_includeLeft_includeRight_iff_isCocomm :
    Commute (toConv (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := H) (B := H)))
        (toConv (Algebra.TensorProduct.includeRight (R := R) (A := H) (B := H))) ↔
      Coalgebra.IsCocomm R H := by
  let swap := (Algebra.TensorProduct.comm R H H).toAlgHom
  have reversed := congrArg (AlgHom.mapValue swap)
    (Langlands.Bialgebra.comulPoint_eq_include_mul (R := R) (H := H))
  simp only [map_mul, AlgHom.mapValue_apply] at reversed
  have hl : swap.comp Algebra.TensorProduct.includeLeft = Algebra.TensorProduct.includeRight := by
    ext; simp [swap]
  have hr : swap.comp Algebra.TensorProduct.includeRight = Algebra.TensorProduct.includeLeft := by
    ext; simp [swap]
  rw [hl, hr] at reversed
  rw [commute_iff_eq, ← Langlands.Bialgebra.comulPoint_eq_include_mul, ← reversed,
    WithConv.toConv_injective.eq_iff]
  constructor
  · intro h
    exact ⟨congrArg AlgHom.toLinearMap h.symm⟩
  · intro hc
    apply AlgHom.toLinearMap_injective
    exact hc.comm_comp_comul.symm

end Langlands.HopfAlgebra
