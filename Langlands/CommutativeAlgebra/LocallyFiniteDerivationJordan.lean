import Langlands.LinearAlgebra.LocallyFiniteJordan
import Langlands.CommutativeAlgebra.SemisimpleDerivation
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.TensorProduct.Submodule

/-! # Jordan components of locally finite derivations -/

noncomputable section

universe u v w

open Module Polynomial
open scoped TensorProduct

namespace Langlands.LinearAlgebra

variable {k : Type u} [Field k]
    {V : Type v} [AddCommGroup V] [Module k V]
    {W : Type w} [AddCommGroup W] [Module k W]

/-- A squarefree minimal polynomial remains an annihilator after an algebra map. -/
theorem isSemisimple_map_end [FiniteDimensional k V]
    (F : End k V →ₐ[k] End k W) {f : End k V} (hf : f.IsSemisimple) :
    (F f).IsSemisimple := by
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero hf.minpoly_squarefree
  rw [aeval_algHom_apply, minpoly.aeval, map_zero]

/-- Endomorphisms on the two tensor factors commute. -/
theorem tensor_legs_commute (f : End k V) (g : End k W) :
    Commute (f.rTensor W) (g.lTensor V) := by
  apply TensorProduct.ext'
  intro x y
  simp only [Module.End.mul_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul]

/-- The additive action of two endomorphisms on their tensor product. -/
def tensorSum (f : End k V) (g : End k W) : End k (V ⊗[k] W) :=
  f.rTensor W + g.lTensor V

variable [FiniteDimensional k V] [FiniteDimensional k W] [PerfectField k]

/-- The tensor sum of semisimple endomorphisms is semisimple. -/
theorem tensorSum_isSemisimple {f : End k V} {g : End k W}
    (hf : f.IsSemisimple) (hg : g.IsSemisimple) :
    (tensorSum f g).IsSemisimple :=
  Module.End.IsSemisimple.add_of_commute (tensor_legs_commute f g)
    (isSemisimple_map_end (Module.End.rTensorAlgHom k V W) hf)
    (isSemisimple_map_end (Module.End.lTensorAlgHom k W V) hg)

/-- The canonical semisimple part respects tensor sums. -/
theorem jordanSemisimplePart_tensorSum (f : End k V) (g : End k W) :
    jordanSemisimplePart (tensorSum f g) =
      tensorSum (jordanSemisimplePart f) (jordanSemisimplePart g) := by
  obtain ⟨_, hnf, hsf, hcf⟩ := jordanSemisimplePart_properties f
  obtain ⟨_, hng, hsg, hcg⟩ := jordanSemisimplePart_properties g
  have hn : IsNilpotent (tensorSum (jordanNilpotentPart f) (jordanNilpotentPart g)) :=
    (tensor_legs_commute _ _).isNilpotent_add
      (hnf.map (Module.End.rTensorAlgHom k V W))
      (hng.map (Module.End.lTensorAlgHom k W V))
  have hc : Commute
      (tensorSum (jordanNilpotentPart f) (jordanNilpotentPart g))
      (tensorSum (jordanSemisimplePart f) (jordanSemisimplePart g)) :=
    ((hcf.map (Module.End.rTensorAlgHom k V W)).add_right
      (tensor_legs_commute _ _)).add_left
      ((tensor_legs_commute _ _).symm.add_right
        (hcg.map (Module.End.lTensorAlgHom k W V)))
  apply jordanSemisimplePart_eq_of_decomposition _ _ _ hn
    (tensorSum_isSemisimple hsf hsg) hc
  simp only [tensorSum, jordanNilpotentPart, LinearMap.rTensor_sub, LinearMap.lTensor_sub]
  abel

end Langlands.LinearAlgebra

namespace Langlands.Algebra.LocallyFiniteDerivationJordan

open Langlands.LinearAlgebra

variable {k : Type u} [Field k] [PerfectField k]
    {A : Type v} [CommRing A] [Algebra k A]
    (D : Derivation k A A) (hD : IsLocallyFinite D.toLinearMap)

omit [PerfectField k] in
/-- Leibniz intertwines multiplication on finite invariant subspaces with
 the tensor sum of their restricted endomorphisms. -/
theorem mulMap_intertwines (P Q : FiniteInvariantSubspace D.toLinearMap) :
    D.toLinearMap.comp (Submodule.mulMap P.carrier Q.carrier) =
      (Submodule.mulMap P.carrier Q.carrier).comp (tensorSum P.restrict Q.restrict) := by
  apply TensorProduct.ext'
  intro x y
  simp only [LinearMap.comp_apply, tensorSum, LinearMap.add_apply,
    LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, map_add, Submodule.mulMap_tmul]
  change D (x.val * y.val) = D x.val * y.val + x.val * D y.val
  rw [D.leibniz]
  simp only [smul_eq_mul]
  ring

/-- The compatible global semisimple component satisfies Leibniz. -/
theorem semisimplePart_leibniz (a b : A) :
    locallyFiniteSemisimplePart D.toLinearMap hD (a * b) =
      a * locallyFiniteSemisimplePart D.toLinearMap hD b +
      b * locallyFiniteSemisimplePart D.toLinearMap hD a := by
  obtain ⟨P, ha⟩ := hD a
  obtain ⟨Q, hb⟩ := hD b
  let aP : P.carrier := ⟨a, ha⟩
  let bQ : Q.carrier := ⟨b, hb⟩
  have h := LinearMap.congr_fun
    (locallyFiniteSemisimplePart_intertwines_finite hD
      (Submodule.mulMap P.carrier Q.carrier) (mulMap_intertwines D P Q))
    (aP ⊗ₜ[k] bQ)
  rw [jordanSemisimplePart_tensorSum] at h
  simp only [LinearMap.comp_apply, tensorSum, LinearMap.add_apply,
    LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, map_add, Submodule.mulMap_tmul] at h
  change locallyFiniteSemisimplePart D.toLinearMap hD (a * b) =
    P.semisimpleMap aP * b + a * Q.semisimpleMap bQ at h
  rw [locallyFiniteSemisimplePart_eq D.toLinearMap hD P aP,
    locallyFiniteSemisimplePart_eq D.toLinearMap hD Q bQ]
  exact h.trans (by ring)

/-- The semisimple component of a locally finite derivation is a derivation. -/
def semisimplePart : Derivation k A A :=
  Derivation.mk' (locallyFiniteSemisimplePart D.toLinearMap hD)
    (semisimplePart_leibniz D hD)

/-- The complementary component is also an actual derivation. -/
def nilpotentPart : Derivation k A A := D - semisimplePart D hD

@[simp] theorem semisimplePart_toLinearMap :
    (semisimplePart D hD).toLinearMap = locallyFiniteSemisimplePart D.toLinearMap hD := rfl

@[simp] theorem nilpotentPart_toLinearMap :
    (nilpotentPart D hD).toLinearMap = locallyFiniteNilpotentPart D.toLinearMap hD := rfl

end Langlands.Algebra.LocallyFiniteDerivationJordan
