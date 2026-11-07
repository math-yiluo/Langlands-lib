import Langlands.GroupScheme.Reductive.PinnedIsomorphismReduction
import Langlands.GroupScheme.Reductive.SplitIsomorphismProof
import Langlands.GroupScheme.Reductive.PinnedRootScalingProof

/-! # Chosen actual pinned lifts of based root-datum equivalences -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitPinning

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  (p : SplitPinning G) (q : SplitPinning H)
  (e : RootPairing.Equiv p.rootDatum q.rootDatum)
  (hsimple : ∀ a, a ∈ p.base.support ↔ e.indexEquiv a ∈ q.base.support)

/-- A chosen actual pinned isomorphism lifting a based root-datum equivalence.
The existence premises are discharged by common-torus extension and root scaling. -/
def isoOfRootDatumEquiv : SplitPinning.Iso p q :=
  Classical.choose (PinnedIsomorphism.exists_iso p q
    splitCommonTorusIsomorphism pinnedRootScaling e hsimple)

@[simp]
theorem isoOfRootDatumEquiv_torusIso :
    (p.isoOfRootDatumEquiv q e hsimple).torusIso = p.torusIsoOfRootDatumEquiv q e :=
  (Classical.choose_spec (PinnedIsomorphism.exists_iso p q
    splitCommonTorusIsomorphism pinnedRootScaling e hsimple)).1

@[simp]
theorem isoOfRootDatumEquiv_indexEquiv :
    (p.isoOfRootDatumEquiv q e hsimple).indexEquiv = e.indexEquiv :=
  (Classical.choose_spec (PinnedIsomorphism.exists_iso p q
    splitCommonTorusIsomorphism pinnedRootScaling e hsimple)).2

/-- The forward character map of the chosen actual pinned lift is the prescribed
full integral weight equivalence. -/
theorem isoOfRootDatumEquiv_character :
    (characterLattice.congr (p.isoOfRootDatumEquiv q e hsimple).torusIso).toIntLinearEquiv =
      e.weightEquiv := by
  rw [p.isoOfRootDatumEquiv_torusIso q e hsimple]
  exact p.torusIsoOfRootDatumEquiv_character q e

/-- The forward cocharacter map of the chosen actual pinned lift is the inverse
of the contravariant coweight equivalence. -/
theorem isoOfRootDatumEquiv_cocharacter :
    (cocharacterLattice.congr
      (p.isoOfRootDatumEquiv q e hsimple).torusIso).toIntLinearEquiv =
      e.coweightEquiv.symm := by
  rw [p.isoOfRootDatumEquiv_torusIso q e hsimple]
  exact p.torusIsoOfRootDatumEquiv_cocharacter q e

end Langlands.GroupScheme.SplitPinning
