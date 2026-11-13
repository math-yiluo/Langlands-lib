import Langlands.GroupScheme.SimplyConnected.ClassicalTypeDSpinPresentationStatement
import Langlands.GroupScheme.SimplyConnected.ClassicalTypeDAlignedSpinCoverStatement
import Langlands.GroupScheme.SimplyConnected.AlignedSpinCoverTitsIndexStatement

/-!
# Reduction of the type-D spin presentation to an aligned cover and its index

The classical type-`D` spin presentation with index comparisons follows from the
existence of a spin cover aligned with the numbered vector vertex and from the
index comparison for every such aligned cover.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The aligned spin cover supplied by `ClassicalTypeDAlignedSpinCoverStatement`
satisfies the index comparisons of `AlignedSpinCoverTitsIndexStatement`, which
gives `ClassicalTypeDSpinPresentationStatement`. -/
theorem classicalTypeDSpinPresentation_of_aligned
    (hA : ClassicalTypeDAlignedSpinCoverStatement.{u})
    (hB : AlignedSpinCoverTitsIndexStatement.{u}) :
    ClassicalTypeDSpinPresentationStatement.{u} := by
  intro K _ G _ _ d n e hn hsc has hcartan hstar
  obtain ⟨D, _, _, _, _, degree, m, hdeg, hdim, hm, σ, hsym, q, hq, π, hπ, hal⟩ :=
    hA K G d n e hn hsc has hcartan hstar
  obtain ⟨hwitt, hvert⟩ :=
    hB K G d n e hn hsc has hcartan hstar D degree m hdeg hdim hm σ hsym q hq π hπ hal
  exact ⟨D, inferInstance, inferInstance, inferInstance, inferInstance, degree, m, hdeg, hdim,
    hm, σ, hsym, q, hq, hwitt, hvert, π, hπ⟩

end Langlands.GroupScheme
