import Langlands.AlgebraicGeometry.SmoothReducedProof
import Langlands.GroupScheme.Unipotent.PerfectFieldSplitProof
import Langlands.GroupScheme.Unipotent.PerfectWoundFiniteStatement
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.Topology.Separation.Connected

/-! # Wound unipotent groups over perfect fields are finite -/

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The identity section of a finite smooth connected group over a field
is an isomorphism. -/
private theorem isIso_structure_of_finite
    {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [ConnectedSpace G.X.left] [IsFinite G.X.hom] :
    IsIso G.X.hom := by
  have : IsLocallyArtinian G.X.left := IsLocallyArtinian.of_locallyQuasiFinite G.X.hom
  have : Subsingleton G.X.left := PreconnectedSpace.trivial_of_discrete
  let e := η[G.X].left
  have he : e ≫ G.X.hom = 𝟙 _ := Over.w η[G.X]
  have : IsClosedImmersion e := isClosedImmersion_of_comp_eq_id G.X.hom e he
  have : Surjective e := ⟨fun x => ⟨IsLocalRing.closedPoint k, Subsingleton.elim _ x⟩⟩
  have : IsReduced G.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field k _ G.X.hom
  have : IsIso e := isIso_of_isClosedImmersion_of_surjective e
  exact IsIso.of_isIso_fac_left he

/-- Milne 14.70 in the smooth connected setting, for every perfect field. -/
theorem perfectFieldWoundUnipotentFinite : PerfectFieldWoundUnipotentFiniteStatement.{u} := by
  intro k _ _ G _ _ hConnected hUnipotent
  let : ConnectedSpace G.X.left := hConnected
  constructor
  · intro hWound
    have hId := hWound.hom_eq_zero_of_isSplitUnipotent
      (perfectFieldUnipotentSplit k G hConnected hUnipotent) (𝟙 G)
    have hComp : G.X.hom ≫ η[G.X].left = 𝟙 G.X.left := by
      have h := congrArg (fun f : G ⟶ G => f.hom.hom.left) hId
      change 𝟙 G.X.left = (toUnit G.X ≫ η[G.X]).left at h
      simpa only [Over.comp_left, Over.toUnit_left] using h.symm
    have : IsIso G.X.hom := ⟨⟨η[G.X].left, hComp, Over.w η[G.X]⟩⟩
    infer_instance
  · intro hFinite f
    have : IsIso G.X.hom := isIso_structure_of_finite G
    refine ⟨η[G.X], ?_⟩
    apply Over.OverMorphism.ext
    apply (cancel_mono G.X.hom).mp
    simp only [Over.w]

end Langlands.GroupScheme
