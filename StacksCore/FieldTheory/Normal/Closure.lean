module

public import Mathlib.FieldTheory.Normal.Closure
public import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.CrossRefAttribute

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-! # Normal closure -/

@[expose] public section

open IntermediateField

attribute [mk_iff] IsNormalClosure

/-- An even more relative version of `normalClosure`. Given `L/N/M` and `L/K` and `N/K`,
the normal closure of `N/K` in `L/K` is actually an `M`-subalgebra of `L`. -/
noncomputable def normalClosure' (K M N L : Type*)
    [Field K] [Field M] [Field N] [Field L]
    [Algebra K N] [Algebra K L] [Algebra M N] [Algebra M L] [Algebra N L]
    [IsScalarTower K N L] [IsScalarTower M N L] :
    IntermediateField M L where
  __ := normalClosure K N L
  algebraMap_mem' x := (Algebra.algHom K N L).fieldRange_le_normalClosure ⟨algebraMap M N x, by
    simp [Algebra.algHom, ← IsScalarTower.algebraMap_apply]⟩

@[stacks 0BMG "2, containment"]
noncomputable instance normalClosure.algebraOfTower (K M N L : Type*)
    [Field K] [Field M] [Field N] [Field L]
    [Algebra K N] [Algebra K L] [Algebra M N] [Algebra M L] [Algebra N L]
    [IsScalarTower K N L] [IsScalarTower M N L] :
    Algebra M (normalClosure K N L) :=
  (normalClosure' K M N L).algebra

open TensorProduct PiTensorProduct
