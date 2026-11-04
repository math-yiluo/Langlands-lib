import Langlands.GroupScheme.Lie.ElementCentralizer
import Langlands.GroupScheme.Lie.TorusCentralizer
import Langlands.GroupScheme.RepresentedSubgroup

/-! # Tangent vectors fixed by a whole torus -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Lie

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)}
  {T : CommGroupScheme (Spec R)} [IsAffineHom G.X.hom]

/-- Containment in an actual Lie-element centralizer is precisely zero adjoint
weight, with both conditions tested over every coefficient algebra. -/
theorem range_le_elementCentralizer_iff_weightSpace_zero
    (i : T.toGrp ⟶ G) (X : lieKernel G R) :
    SubgroupFunctor.range i ≤ elementCentralizer G X ↔
      Additive.ofMul X ∈ weightSpace i 0 := by
  constructor
  · intro h A _ _ t
    rw [characterValue_zero, Units.val_one, one_smul]
    exact (mem_elementCentralizer_adjoint_iff G X (t ≫ i.hom.hom)).1
      (h _ (SubgroupFunctor.mem_range.2 ⟨t, rfl⟩))
  · intro h U g hg A _ _ a
    obtain ⟨t, rfl⟩ := SubgroupFunctor.mem_range.1 hg
    apply (commute_constant_iff G _ _).2
    have h' := h A (a ≫ t)
    rw [characterValue_zero, Units.val_one, one_smul] at h'
    exact Additive.ofMul.injective h'

variable [IsAffineHom T.toGrp.X.hom]

/-- All-test symmetry between a torus centralizing a Lie element and that
Lie element belonging to the tangent space of the whole-torus centralizer. -/
theorem range_le_elementCentralizer_iff_mem_torusCentralizerLie
    (i : T.toGrp ⟶ G) (X : lieKernel G R) :
    SubgroupFunctor.range i ≤ elementCentralizer G X ↔
      Additive.ofMul X ∈ torusCentralizerLie i := by
  rw [torusCentralizerLie_eq_weightSpace_zero]
  exact range_le_elementCentralizer_iff_weightSpace_zero i X

/-- The canonical actual tangent lift into a represented whole-torus
centralizer when the torus centralizes the tangent vector. -/
def torusCentralizerTangentFactor {C : GroupScheme (Spec R)}
    (i : T.toGrp ⟶ G) (j : C ⟶ G)
    (hrep : (torusCentralizer i).IsRepresentedBy j)
    (X : lieKernel G R)
    (hX : SubgroupFunctor.range i ≤ elementCentralizer G X) : lieKernel C R := by
  have hm := (range_le_elementCentralizer_iff_mem_torusCentralizerLie i X).1 hX
  let y := (hrep.pointsEquiv _).symm ⟨X.val, hm⟩
  have hy : y ≫ j.hom.hom = X.val := hrep.pointsEquiv_symm_comp _
  have : Mono j.hom.hom := hrep.1
  refine ⟨y, mem_lieKernel_of_comp j y ?_⟩
  rw [hy]
  exact X.property

@[simp]
theorem targetMap_torusCentralizerTangentFactor {C : GroupScheme (Spec R)}
    (i : T.toGrp ⟶ G) (j : C ⟶ G)
    (hrep : (torusCentralizer i).IsRepresentedBy j)
    (X : lieKernel G R)
    (hX : SubgroupFunctor.range i ≤ elementCentralizer G X) :
    targetMap j R (torusCentralizerTangentFactor i j hrep X hX) = X := by
  apply Subtype.ext
  exact hrep.pointsEquiv_symm_comp _

end Langlands.GroupScheme.Lie
