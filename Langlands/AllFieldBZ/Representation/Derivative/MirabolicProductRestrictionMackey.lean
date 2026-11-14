import Langlands.AllFieldBZ.Group.GL.CompactOpen
import Langlands.AllFieldBZ.Group.GL.CountabilityProof
import Langlands.AllFieldBZ.Group.GL.Maps
import Langlands.AllFieldBZ.Group.GL.MirabolicMixedProductSubgroups
import Langlands.AllFieldBZ.Representation.Derivative.MinusVanishing
import Langlands.Representation.Derivative.MirabolicProductRestrictionMackey

/-!
# All-field port of `Langlands.Representation.Derivative.MirabolicProductRestrictionMackey`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.MirabolicProductRestrictionMackey` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
namespace Langlands.AllFieldBZ
universe uF uV uR uG uC vC

namespace RepFunctorFiltration
open Langlands.RepFunctorFiltration
variable {R : Type uR} [CommRing R] {G : Type uG} [Monoid G]
  {C : Type uC} [Category.{vC} C] {F : C ⥤ Rep.{uV} R G}

end RepFunctorFiltration
namespace Derivative.MirabolicProductRestriction
open Langlands.Derivative.MirabolicProductRestriction hiding exists_exact_restrictedCompactInduction
open Langlands.GeneralLinear
variable {F : LocalFieldPackage.{uF}}

/-- The Mackey sequence for compact induction from the binary parabolic restricted
to the mirabolic subgroup: the open-orbit piece, the whole restriction, and the
closed-orbit piece. -/
theorem exists_exact_restrictedCompactInduction (T : F.TopologicalData) (m n : ℕ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup ((m + 1) + (n + 1))
    ∃ (i : Geometric.orbitPiece.{0, uF, uV} (R := ℂ) (parabolicP F.Carrier m n)
          (mirabolicQ F.Carrier m n) (openRep F.Carrier m n) ⟶
        Geometric.restrictedCompactInduction (parabolicP F.Carrier m n)
          (mirabolicQ F.Carrier m n))
      (q : Geometric.restrictedCompactInduction.{0, uF, uV} (R := ℂ) (parabolicP F.Carrier m n)
          (mirabolicQ F.Carrier m n) ⟶
        Geometric.orbitPiece (parabolicP F.Carrier m n) (mirabolicQ F.Carrier m n) 1),
      ∀ X, Function.Injective (i.app X).hom ∧
        LinearMap.range (i.app X).hom.toLinearMap = LinearMap.ker (q.app X).hom.toLinearMap ∧
        Function.Surjective (q.app X).hom := by
  let := T.topology
  let := T.generalLinearTopologicalGroup ((m + 1) + (n + 1))
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearNonarchimedean ((m + 1) + (n + 1))
  let := T.generalLinearLocallyCompactSpace ((m + 1) + (n + 1))
  let := T.generalLinearT2Space ((m + 1) + (n + 1))
  let := T.generalLinearSigmaCompactSpace ((m + 1) + (n + 1))
  have hP : IsClosed (parabolicP F.Carrier m n : Set (GeneralLinear ((m + 1) + (n + 1)) F.Carrier)) :=
    (shape m n).isClosed_parabolic F.Carrier
  have hQ : IsClosed (mirabolicQ F.Carrier m n : Set (GeneralLinear ((m + 1) + (n + 1)) F.Carrier)) :=
    Mirabolic.isClosed
  have hM := Geometric.closedSubgroupMackeyFiltration.{uF, uV}
    (GeneralLinear ((m + 1) + (n + 1)) F.Carrier) (parabolicP F.Carrier m n)
    (mirabolicQ F.Carrier m n) hP hQ 2 (orbitOrdering m n)
  obtain ⟨e₀⟩ := hM 0
  obtain ⟨e₁⟩ := hM 1
  exact RepFunctorFiltration.exists_exact_of_two _ e₀ e₁

end Derivative.MirabolicProductRestriction
end Langlands.AllFieldBZ
