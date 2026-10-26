import Langlands.AlgebraicGeometry.Modules.PullbackTensor

/-! # Local finite pure-tensor decompositions of sections of a sheaf tensor -/

noncomputable section

universe u

open CategoryTheory
open scoped BigOperators TensorProduct

namespace Langlands.Scheme.Modules

/-- Every section of the actual sheaf tensor is locally the image, under the
sheafification unit, of a finite sum of pure sectionwise tensors.
This generalizes the local finite-sum step in Stacks Lemma 17.25.2. -/
def TensorLocalFiniteDecompositionStatement (X : AlgebraicGeometry.Scheme.{u}) : Prop :=
  ∀ (M N : X.Modules) (U : X.Opens)
    (z : (tensorObj M N).val.obj (Opposite.op U)) (x : X), x ∈ U →
    ∃ (V : X.Opens) (hVU : V ≤ U) (_hxV : x ∈ V) (n : ℕ)
      (s : Fin n → M.val.obj (Opposite.op V))
      (t : Fin n → N.val.obj (Opposite.op V)),
      ((tensorSheafifyUnit M N).app (Opposite.op V)).hom
          (∑ i : Fin n, s i ⊗ₜ[X.presheaf.obj (Opposite.op V)] t i) =
        (tensorObj M N).val.map (homOfLE hVU).op z

end Langlands.Scheme.Modules
