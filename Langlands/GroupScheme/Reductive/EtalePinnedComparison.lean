import Langlands.GroupScheme.Reductive.AffinePinnedAtlas
import Langlands.GroupScheme.Reductive.AffinePinnedScalarExtension
import Langlands.GroupScheme.Reductive.FibrewiseRootDatumComparison
import Langlands.GroupScheme.Reductive.AffineSplitIsomorphismTheoremStatement

/-! # Conditional étale comparisons from actual field isomorphisms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

/-- An actual isomorphism of two groups on an affine étale chart of their
common base. This structure supplies data and asserts no existence. -/
structure AffineComparisonChart {S : Scheme.{u}} (G H : GroupScheme S) where
  ring : Type u
  [commRing : CommRing ring]
  map : Spec (CommRingCat.of ring) ⟶ S
  etale : Etale map
  iso : (baseChange map).obj G ≅ (baseChange map).obj H

attribute [instance] AffineComparisonChart.commRing

namespace AffineComparisonChart

/-- Assuming the affine split isomorphism theorem, actual field
isomorphisms with a pinned model yield affine étale comparisons above every
base point. This is a conditional construction; it does not prove that input. -/
theorem exists_over_of_pinned_fieldIso
    (hAffine : AffineSplitIsomorphismTheoremStatement.{u})
    (M : AffinePinnedModel.{u}) (H : GroupScheme M.base) (hH : IsReductive H)
    (hfield : ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (b : Spec (CommRingCat.of K) ⟶ M.base),
      Nonempty ((baseChange b).obj M.group ≅ (baseChange b).obj H))
    (s : M.base) : ∃ C : AffineComparisonChart M.group H,
      ∃ x : Spec (CommRingCat.of C.ring), C.map x = s := by
  classical
  obtain ⟨C, x, hx⟩ := AffinePinnedChart.exists_over hH s
  let A := C.model.ring
  let : CommRing A := C.model.commRing
  let : Algebra M.ring A := (Spec.preimage C.map).hom.toAlgebra
  have hb : algebraBaseMap M.ring A = C.map := Spec.map_preimage C.map
  let N := M.scalarExtension A
  let eN : N.group ≅ (baseChange C.map).obj M.group :=
    eqToIso (congrArg (fun b => (baseChange b).obj M.group) hb)
  let K := AlgebraicClosure (C.model.base.residueField x)
  let b := geometricPoint C.model.base x
  let : Algebra A K := (Spec.preimage b).hom.toAlgebra
  let q := algebraBaseMap A K
  obtain ⟨e⟩ := hfield K (q ≫ C.map)
  let ef : (baseChange q).obj N.group ≅ (baseChange q).obj C.model.group :=
    (baseChange q).mapIso eN ≪≫ (baseChangeCompIso C.map q M.group).symm ≪≫ e ≪≫
      baseChangeCompIso C.map q H ≪≫ (baseChange q).mapIso C.iso
  let : Smooth N.group.X.hom := N.reductive.smooth
  let : Smooth C.model.group.X.hom := C.model.reductive.smooth
  have hnmax := splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise (R := A)
    N.coordinates N.group N.inclusion N.maximal K
  have hcmax := splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise
    C.model.coordinates C.model.group C.model.inclusion C.model.maximal K
  obtain ⟨f⟩ := N.fibrewiseRootDatum.nonempty_equiv_of_reductive_fieldIso (R := A)
    C.model.fibrewiseRootDatum N.reductive C.model.reductive K hnmax hcmax ef
  obtain ⟨phi, _, _, _⟩ := hAffine A N.group C.model.group N.reductive C.model.reductive
    N.coordinates C.model.coordinates N.inclusion C.model.inclusion
    N.rootIndex C.model.rootIndex N.rootDatum C.model.rootDatum
    N.closed N.maximal N.fibrewiseRootDatum N.rootLines
    C.model.closed C.model.maximal C.model.fibrewiseRootDatum C.model.rootLines f.symm
  exact ⟨⟨A, C.map, C.etale, eN.symm ≪≫ phi ≪≫ C.iso.symm⟩, x, hx⟩

end AffineComparisonChart

/-- A point-indexed covering family of actual affine étale comparisons. -/
structure AffineComparisonAtlas {S : Scheme.{u}} (G H : GroupScheme S) where
  chart : S → AffineComparisonChart G H
  point : ∀ s, Spec (CommRingCat.of (chart s).ring)
  image_point : ∀ s, (chart s).map (point s) = s

namespace AffineComparisonAtlas

/-- The conditional comparison charts chosen simultaneously above every
point, with exact distinguished points witnessing the étale cover. -/
def ofPinnedFieldIso
    (hAffine : AffineSplitIsomorphismTheoremStatement.{u})
    (M : AffinePinnedModel.{u}) (H : GroupScheme M.base) (hH : IsReductive H)
    (hfield : ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (b : Spec (CommRingCat.of K) ⟶ M.base),
      Nonempty ((baseChange b).obj M.group ≅ (baseChange b).obj H)) :
    AffineComparisonAtlas M.group H := by
  classical
  choose C x hx using
    AffineComparisonChart.exists_over_of_pinned_fieldIso hAffine M H hH hfield
  exact ⟨C, x, hx⟩

end AffineComparisonAtlas

end Langlands.GroupScheme
