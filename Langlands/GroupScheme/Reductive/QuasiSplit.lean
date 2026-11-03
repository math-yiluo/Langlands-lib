import Langlands.GroupScheme.Absolute.ParabolicTransport
import Langlands.GroupScheme.Absolute.BorelTransport
import Langlands.GroupScheme.Rational.SplitRankTransport
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport

/-! # Field-defined geometric Borel subgroups and quasi-split reductive groups -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
variable {B G H : GroupScheme (Spec (CommRingCat.of k))}

/-- A field-defined Borel inclusion whose algebraic-closure base change is also Borel. -/
def IsGeometricBorelSubgroup (i : B ⟶ G) : Prop :=
  IsBorelSubgroup i ∧
    IsBorelSubgroup ((GroupScheme.baseChange (toAlgebraicClosure k)).map i)

/-- The geometric Borel condition includes the existing field-level Borel condition. -/
theorem IsGeometricBorelSubgroup.isBorelSubgroup {i : B ⟶ G}
    (hi : IsGeometricBorelSubgroup i) : IsBorelSubgroup i := hi.1

/-- A field-defined geometric Borel is a parabolic subgroup in the existing interface. -/
theorem IsGeometricBorelSubgroup.isParabolicSubgroup {i : B ⟶ G}
    (hi : IsGeometricBorelSubgroup i) : IsParabolicSubgroup i := by
  refine ⟨hi.1.isClosedSubgroup, hi.1.smooth, ?_⟩
  exact ⟨_, _, 𝟙 _, hi.2, Category.id_comp _⟩

/-- Ambient isomorphisms preserve field-defined geometric Borel inclusions. -/
theorem IsGeometricBorelSubgroup.comp_iso {i : B ⟶ G}
    (hi : IsGeometricBorelSubgroup i) (e : G ≅ H) :
    IsGeometricBorelSubgroup (i ≫ e.hom) := by
  refine ⟨hi.1.comp_iso e, ?_⟩
  let F := GroupScheme.baseChange (toAlgebraicClosure k)
  change IsBorelSubgroup (F.map (i ≫ e.hom))
  rw [F.map_comp]
  exact hi.2.comp_iso (F.mapIso e)

/-- The geometric Borel condition is invariant under an ambient isomorphism. -/
theorem isGeometricBorelSubgroup_comp_iso_iff (i : B ⟶ G) (e : G ≅ H) :
    IsGeometricBorelSubgroup (i ≫ e.hom) ↔ IsGeometricBorelSubgroup i := by
  constructor
  · intro hi
    have h := hi.comp_iso e.symm
    change IsGeometricBorelSubgroup ((i ≫ e.hom) ≫ e.inv) at h
    simpa only [Category.assoc, e.hom_inv_id, Category.comp_id] using h
  · exact fun hi => hi.comp_iso e

/-- A connected reductive field group is quasi-split when it contains an actual
field-defined Borel that remains Borel over the algebraic closure. -/
structure IsQuasiSplit (G : GroupScheme (Spec (CommRingCat.of k))) : Prop where
  isConnectedReductive : IsConnectedReductive G
  exists_isGeometricBorelSubgroup :
    ∃ (B : GroupScheme (Spec (CommRingCat.of k))) (i : B ⟶ G), IsGeometricBorelSubgroup i

/-- Quasi-splitness supplies a field-defined parabolic which is solvable. -/
theorem IsQuasiSplit.exists_solvable_parabolic (h : IsQuasiSplit G) :
    ∃ (B : GroupScheme (Spec (CommRingCat.of k))) (i : B ⟶ G),
      IsParabolicSubgroup i ∧ IsSolvableGroupScheme B := by
  obtain ⟨B, i, hi⟩ := h.exists_isGeometricBorelSubgroup
  exact ⟨B, i, hi.isParabolicSubgroup, hi.1.isSolvableGroupScheme⟩

/-- Quasi-splitness is invariant under field-group isomorphisms. -/
theorem IsQuasiSplit.of_iso (e : G ≅ H) (h : IsQuasiSplit H) : IsQuasiSplit G := by
  obtain ⟨B, i, hi⟩ := h.exists_isGeometricBorelSubgroup
  exact ⟨h.isConnectedReductive.of_iso e, B, i ≫ e.inv, hi.comp_iso e.symm⟩

/-- The full quasi-splitness comparison under isomorphism. -/
theorem isQuasiSplit_iff_of_iso (e : G ≅ H) : IsQuasiSplit G ↔ IsQuasiSplit H :=
  ⟨fun h => h.of_iso e.symm, fun h => h.of_iso e⟩

end Langlands.GroupScheme
