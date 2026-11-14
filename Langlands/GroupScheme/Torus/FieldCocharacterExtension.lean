import Langlands.GroupScheme.Torus.ExponentCocharacters

/-! # Extending field cocharacters of a specified split torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

namespace IsSplitTorus

/-- Every cocharacter of a field-valued fibre of a split torus extends over
the original base. The base need not be reduced or connected. -/
theorem cocharacterLattice_baseChange_surjective_field
    {S : Scheme.{u}} (T : CommGroupScheme S) (hT : IsSplitTorus T.toGrp)
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S) :
    Function.Surjective (cocharacterLattice.baseChange b T) := by
  classical
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let : Fintype I := Fintype.ofFinite I
  let e' : T ≅ splitTorus.commGroupScheme S I := CommGroupScheme.isoOfGroupIso e
  intro ν
  let ν' := ν ≫ (CommGroupScheme.baseChange b).map e'.hom
  let n := splitTorus.cocharacterLatticeEquiv k I
    (ν' ≫ (splitTorus.commBaseChangeIso b I).hom)
  have hn : cocharacterLattice.baseChange b _
      (splitTorus.exponentCocharacter S I n) = ν' := by
    apply (cancel_mono (splitTorus.commBaseChangeIso b I).hom).1
    rw [splitTorus.exponentCocharacter_baseChange,
      splitTorus.exponentCocharacter_eq_cocharacterLatticeEquiv_symm]
    exact (splitTorus.cocharacterLatticeEquiv k I).symm_apply_apply _
  refine ⟨splitTorus.exponentCocharacter S I n ≫ e'.inv, ?_⟩
  rw [cocharacterLattice.baseChange_comp, hn]
  simp [ν', ← Functor.map_comp, Category.assoc]

/-- A chosen actual extension, in the same specified torus, of a
cocharacter over any field-valued point of the base. -/
def extendFieldCocharacter
    {S : Scheme.{u}} (T : CommGroupScheme S) (hT : IsSplitTorus T.toGrp)
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S)
    (ν : cocharacterLattice ((CommGroupScheme.baseChange b).obj T)) :
    cocharacterLattice T :=
  (cocharacterLattice_baseChange_surjective_field T hT b ν).choose

/-- The extension has exactly the prescribed field cocharacter. -/
@[simp] theorem baseChange_extendFieldCocharacter
    {S : Scheme.{u}} (T : CommGroupScheme S) (hT : IsSplitTorus T.toGrp)
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S)
    (ν : cocharacterLattice ((CommGroupScheme.baseChange b).obj T)) :
    cocharacterLattice.baseChange b T (extendFieldCocharacter T hT b ν) = ν :=
  (cocharacterLattice_baseChange_surjective_field T hT b ν).choose_spec

end IsSplitTorus

end Langlands.GroupScheme
