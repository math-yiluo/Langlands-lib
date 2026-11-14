import Langlands.AllFieldBZ.Representation.Classification.SupercuspidalSupport
import Langlands.AllFieldBZ.Representation.Derivative.MirabolicMinusExactnessStatement
import Langlands.AllFieldBZ.Representation.Filtration.SimpleSubquotientFactorProof
import Langlands.Representation.Filtration.ExactFunctorDetectedConstituent

/-!
# All-field port of `Langlands.Representation.Filtration.ExactFunctorDetectedConstituent`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Filtration.ExactFunctorDetectedConstituent` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
namespace Langlands.AllFieldBZ
universe uG uH uV

namespace ObjectRepFiltration
open Langlands.ObjectRepFiltration
private theorem _root_.Langlands.ObjectRepFiltration.adjacent_steps_ne_of_nontrivial
    {k G : Type*} [Field k] [Monoid G] {A : Rep k G} {r : ℕ}
    (s : ObjectRepFiltration A r) (i : Fin r)
    [Nontrivial (s.gradedRepresentation i)] :
    s.subrepresentation i.castSucc ≠ s.subrepresentation i.succ := by
  intro he
  have hz (x : s.gradedRepresentation i) : x = 0 := by
    obtain ⟨v, rfl⟩ := s.gradedProjection_surjective i x
    apply (s.gradedProjection_eq_zero_iff i v).mpr
    rw [he]
    exact v.property
  exact (not_nontrivial_iff_subsingleton.mpr
    ⟨fun x y => (hz x).trans (hz y).symm⟩) inferInstance

end ObjectRepFiltration
namespace ExactFunctorDetectedConstituent
open Langlands.ExactFunctorDetectedConstituent
variable {G : Type uG} [Group G] [TopologicalSpace G]
  {H : Type uH} [Group H] [TopologicalSpace H]
  (J : SmoothRep.{0,uG,uV} ℂ G ⥤ SmoothRep.{0,uH,uV} ℂ H)
  [J.PreservesZeroMorphisms]
  (hJ : Derivative.Mirabolic.MapsShortExactIntertwiners J)

end ExactFunctorDetectedConstituent
end Langlands.AllFieldBZ
