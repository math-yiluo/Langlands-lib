import Langlands.GroupScheme.Rational.DynamicNestedParabolicDecompositionStatement
import Langlands.GroupScheme.Rational.StandardCocharacterStatement
import Langlands.GroupScheme.Rational.StandardParabolicOrderStatement
import Langlands.GroupScheme.Rational.StandardLeviIntersectionStatement

/-! # Standard-index comparison for the nested dynamic decomposition target -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.GroupScheme

/-- The dynamic target supplies all three standard-index products on every
test, conditional on standard cocharacter realization and the standard order. -/
theorem nestedLeviDecomposition_standard_of_dynamic
    (hD : DynamicNestedParabolicDecompositionStatement.{u})
    (hC : StandardCocharacterStatement.{u})
    (hO : StandardParabolicOrderStatement.{u})
    (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T) :
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    IsGenericCocharacter i ν →
      ∀ J K : Set (characterLattice T),
        J ⊆ simpleRelativeRoots i ν → K ⊆ simpleRelativeRoots i ν → J ⊆ K →
        SubgroupFunctor.NestedLeviDecomposition
          (standardParabolic i ν J) (standardLevi i ν J)
          (standardUnipotent i ν J) (standardLevi i ν K) (standardUnipotent i ν K) := by
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  intro hν J K hJ hK hJK
  obtain ⟨⟨α, hα⟩, hcJ⟩ := hC k G hG T i hi ν hν J hJ
  obtain ⟨⟨β, hβ⟩, hcK⟩ := hC k G hG T i hi ν hν K hK
  obtain ⟨hPJ, hMJ, hNJ⟩ := hcJ α hα
  obtain ⟨hPK, hMK, hUK⟩ := hcK β hβ
  obtain ⟨hP, hLU⟩ := (hO k G hG T i hi ν hν).1 J K hJ hK
  obtain ⟨hL, _⟩ := hLU hJK
  have hPD : Dynamic.parabolic (CommGroupScheme.groupHom α ≫ i) ≤
      Dynamic.parabolic (CommGroupScheme.groupHom β ≫ i) := by
    rw [← hPJ, ← hPK]
    exact hP.1 hJK
  have hLD : Dynamic.centralizer (CommGroupScheme.groupHom α ≫ i) ≤
      Dynamic.centralizer (CommGroupScheme.groupHom β ≫ i) := by
    rw [← hMJ, ← hMK]
    exact hL
  have hd := hD k G hG (CommGroupScheme.groupHom α ≫ i)
    (CommGroupScheme.groupHom β ≫ i)
    (Dynamic.isCompatibleNestedPair_of_torus i hi α β hPD hLD)
  change SubgroupFunctor.NestedLeviDecomposition
    (Dynamic.parabolic (CommGroupScheme.groupHom α ≫ i))
    (Dynamic.centralizer (CommGroupScheme.groupHom α ≫ i))
    (Dynamic.unipotent (CommGroupScheme.groupHom α ≫ i))
    (Dynamic.centralizer (CommGroupScheme.groupHom β ≫ i))
    (Dynamic.unipotent (CommGroupScheme.groupHom β ≫ i)) at hd
  rw [hPJ, hMJ, hNJ, hMK, hUK]
  exact hd

/-- The previously published nested standard-index target follows from the
dynamic target, standard cocharacter realization and the standard order. -/
theorem standardLeviIntersectionStatement_of_dynamicNestedParabolicDecomposition
    (hD : DynamicNestedParabolicDecompositionStatement.{u})
    (hC : StandardCocharacterStatement.{u})
    (hO : StandardParabolicOrderStatement.{u}) :
    StandardLeviIntersectionStatement.{u} := by
  intro k _ G hG T i hi ν hν J K hJ hK hJK
  have h := nestedLeviDecomposition_standard_of_dynamic hD hC hO
    k G hG T i hi ν hν J K hJ hK hJK
  refine ⟨fun X => ?_, ?_⟩
  · have hx := h X
    exact ⟨hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1⟩
  · exact (h (Over.mk (𝟙 _))).2.2.2.2.2.1

end Langlands.GroupScheme
