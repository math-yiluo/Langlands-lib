/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-!
# Extension of complexes preserves colimits

Source: the degreewise colimit construction in Mathlib's
`Algebra.Homology.HomologicalComplexLimits`, applied to extension by zero.
The proof is moved unchanged from `ProEtaleModuleCohomologyCoproducts`.
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u v w z

open CategoryTheory CategoryTheory.Limits

/-- Extension by zero along an embedding of complex shapes preserves colimits.
Source: Mathlib, `Algebra.Homology.HomologicalComplexLimits` and
`Algebra.Homology.Embedding.Extend`; the existing proof in
`WeilConjectures.AlgebraicGeometry.ProEtaleModuleCohomologyCoproducts`.
(auxiliary; not a blueprint node).
Proof: after evaluation at a degree in the embedding range, extension is naturally
isomorphic to evaluation at its preimage. Outside the range, it is the zero
functor. Both preserve colimits, including empty ones. Colimits of complexes are
computed degreewise, so the extension functor preserves them. -/
theorem extension_preservesColimits {C : Type u} [Category.{v} C]
    [HasZeroObject C] [HasZeroMorphisms C]
    {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (e : c.Embedding c') (J : Type w) [Category.{z} J] [HasColimitsOfShape J C] :
    PreservesColimitsOfShape J (e.extendFunctor C) := by
  have heval (n : ι') : PreservesColimitsOfShape J
      (e.extendFunctor C ⋙ HomologicalComplex.eval C c' n) := by
    classical
    by_cases hn : ∃ i, e.f i = n
    · obtain ⟨i, hi⟩ := hn
      let iso : e.extendFunctor C ⋙ HomologicalComplex.eval C c' n ≅
          HomologicalComplex.eval C c i := NatIso.ofComponents (fun K ↦ K.extendXIso e hi)
            (by
              intro K L f
              change (HomologicalComplex.extendMap f e).f n ≫
                (L.extendXIso e hi).hom = (K.extendXIso e hi).hom ≫ f.f i
              rw [HomologicalComplex.extendMap_f _ _ hi]
              simp)
      exact preservesColimitsOfShape_of_natIso iso.symm
    · exact Functor.preservesColimitsOfShape_of_isZero _
        (Functor.isZero _ fun K ↦ K.isZero_extend_X e n (by simpa using hn)) J
  constructor
  intro K
  apply preservesColimit_of_preserves_colimit_cocone (colimit.isColimit K)
  apply HomologicalComplex.isColimitOfEval
  intro n
  have := heval n
  exact isColimitOfPreserves (e.extendFunctor C ⋙ HomologicalComplex.eval C c' n)
    (colimit.isColimit K)
