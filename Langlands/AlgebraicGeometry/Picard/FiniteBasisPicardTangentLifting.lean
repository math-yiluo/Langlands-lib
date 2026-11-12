import Langlands.AlgebraicGeometry.Picard.FiniteBasisPicardFamily
import Langlands.AlgebraicGeometry.Picard.ArtinianChartTestReduction
import Langlands.CategoryTheory.Sites.PseudofunctorPointFiberIdentity

/-! # Full specified-isomorphism tangent lifting for the finite basis family -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid.FiniteBasisPicardTangentLifting

open Langlands.AlgebraicGeometry.Deformation
open Langlands.CategoryTheory
open ArtinianChartLifting ArtinianChartVersality

variable {k K : Type u} [CommRing k] [Field K] [Algebra k K]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  (M : LineBundle ((relativeSpace f).obj (ArtinianTest.residueBase k K)))

/-- The actual basis family on its actual finite tangent test. -/
abbrev bundle [IsProper f] :=
  (FiniteBasisPicardFamily.family f M).right.of

/-- Pointed dual-number realizations imply lifting of the full specified point. -/
theorem hasLiftingForAt_of_parameters {A : ArtinianTest k K}
    (D : ArtinianTestDeformations.Deformations f M A)
    (h : ∀ N : ArtinianTestDeformations.Deformations f M
      (ArtinianTest.dualNumbers k K), ∃ q : A ⟶ ArtinianTest.dualNumbers k K,
        Nonempty ((ArtinianTestDeformations.restrict f M q).obj D ≅ N)) :
    ArtinianChartVersality.HasLiftingForAt f D.right.of
      (ArtinianTest.reduction A)
      (ArtinianTest.dualReduction k K) := by
  apply (ArtinianChartTestReduction.hasLiftingForAt_iff_base f D.right.of
    (ArtinianTest.reduction A)
    (ArtinianTest.dualReduction k K)).mpr
  intro N y hy
  rcases y with ⟨p, d⟩
  have hp : p = ArtinianTest.reduction A := by
    simpa only [reduction_residue, Category.id_comp] using hy
  subst p
  let N' : ArtinianTestDeformations.Deformations f M (ArtinianTest.dualNumbers k K) :=
    StructuredArrow.mk (D.hom ≫ d.hom)
  obtain ⟨q, ⟨e⟩⟩ := h N'
  obtain ⟨x, hx⟩ :=
    PseudofunctorPointFiber.exists_identityPoint_of_pointedIso (relative f)
      (T₀ := ArtinianTest.residueBase k K) (Core.mk M)
      (ArtinianTest.pointedMap q) D N' e d rfl
  refine ⟨x, ?_⟩
  exact hx

/-- The basis family lifts every actual dual-number point with its specified
residue map and entire specified isomorphism. -/
theorem hasLiftingForAt [IsProper f] :
    ArtinianChartVersality.HasLiftingForAt f (bundle f M)
      (ArtinianTest.reduction (FiniteBasisPicardFamily.test f M))
      (ArtinianTest.dualReduction k K) := by
  apply hasLiftingForAt_of_parameters f M
    (A := ArtinianTest.FiniteTangents.test k K (FiniteBasisPicardFamily.Index f M))
    (FiniteTangentFamily.family f M (FiniteBasisPicardFamily.basis f M))
  intro N
  obtain ⟨c, hc, _⟩ := FiniteBasisPicardFamily.existsUnique_parameter f M N
  exact ⟨ArtinianTest.FiniteTangents.weighted k K c, hc⟩

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid.FiniteBasisPicardTangentLifting
