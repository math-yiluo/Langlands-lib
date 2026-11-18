import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Centralizer
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # A finite semisimple operator algebra and its bicommutant -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe uk un

namespace Langlands.Algebra.SemisimpleOperatorAlgebra

variable {k : Type uk} [Field k] {n : Type un} [Fintype n] [DecidableEq n]
  (A : Subalgebra k (Module.End k (n → k)))

local instance operatorRing : Ring A := inferInstance

/-- Evaluate every operator on the standard coordinate basis. -/
def evaluationMap : A →ₗ[A] (n → (n → k)) where
  toFun a j := a.val (Pi.single j 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem evaluationMap_injective : Function.Injective (evaluationMap A) := by
  intro a b hab
  apply Subtype.ext
  apply (Pi.basisFun k n).ext
  intro j
  simpa [evaluationMap, Pi.basisFun_apply] using congrFun hab j

/-- A finite-coordinate algebra acting faithfully and semisimply is a
semisimple ring. -/
theorem isSemisimpleRing [IsSemisimpleModule A (n → k)] : IsSemisimpleRing A := by
  let e := LinearEquiv.ofInjective (evaluationMap A) (evaluationMap_injective A)
  exact IsSemisimpleModule.congr e

omit [Fintype n] [DecidableEq n] in
/-- Restricting an operator-module endomorphism to ground-field scalars puts it
in the commutant. -/
theorem restrictScalars_mem_centralizer (f : Module.End A (n → k)) :
    f.restrictScalars k ∈ Subalgebra.centralizer k (A : Set (Module.End k (n → k))) := by
  intro a ha
  apply LinearMap.ext
  intro v
  exact (f.map_smul (⟨a, ha⟩ : A) v).symm

omit [DecidableEq n] in
/-- Finite-dimensional Jacobson density identifies a semisimple operator
algebra with its bicommutant. -/
theorem centralizer_centralizer_eq [IsSemisimpleModule A (n → k)] :
    Subalgebra.centralizer k
      (Subalgebra.centralizer k (A : Set (Module.End k (n → k))) :
        Set (Module.End k (n → k))) = A := by
  classical
  apply le_antisymm ?_ (Subalgebra.le_centralizer_centralizer k)
  intro f hf
  let g : Module.End (Module.End A (n → k)) (n → k) :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := by
        intro a v
        exact (LinearMap.congr_fun
          (hf (a.restrictScalars k) (restrictScalars_mem_centralizer A a)) v).symm }
  let b := Module.finBasis k (n → k)
  obtain ⟨a, ha⟩ := jacobson_density (R := A) (M := n → k) g (Finset.univ.image b)
  have he : a.val = f := b.ext fun i =>
    (ha (b i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)).symm
  exact he ▸ a.property

omit [Fintype n] [DecidableEq n] in
private theorem center_mem_centralizer (z : Subalgebra.center k A) :
    z.val.val ∈ Subalgebra.centralizer k (A : Set (Module.End k (n → k))) := by
  intro a ha
  exact congrArg Subtype.val ((Subalgebra.mem_center_iff.mp z.property) (⟨a, ha⟩ : A))

/-- The centre of a semisimple operator algebra agrees with the centre of its
commutant, through their identical ambient operators. -/
def centerCentralizerEquiv [IsSemisimpleModule A (n → k)] :
    Subalgebra.center k A ≃ₐ[k]
      Subalgebra.center k
        (Subalgebra.centralizer k (A : Set (Module.End k (n → k)))) where
  toFun z :=
    ⟨⟨z.val.val, center_mem_centralizer A z⟩, by
      apply Subalgebra.mem_center_iff.mpr
      intro c
      apply Subtype.ext
      exact (c.property z.val.val z.val.property).symm⟩
  invFun z :=
    ⟨⟨z.val.val, by
      apply (centralizer_centralizer_eq A).le
      intro c hc
      exact congrArg Subtype.val
        ((Subalgebra.mem_center_iff.mp z.property) ⟨c, hc⟩)⟩, by
      apply Subalgebra.mem_center_iff.mpr
      intro a
      apply Subtype.ext
      exact z.val.property a.val a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

end Langlands.Algebra.SemisimpleOperatorAlgebra
