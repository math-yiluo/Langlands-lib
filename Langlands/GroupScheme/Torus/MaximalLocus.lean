import Langlands.GroupScheme.Torus.FieldPointMaximality
import Langlands.GroupScheme.Torus.Relative

/-! # The residue-fibre maximal-torus locus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {T T' : CommGroupScheme S} {G : GroupScheme S}

/-- Points at which the supplied torus inclusion is maximal on the actual
residue-field fibre. -/
def maximalTorusLocus (i : T.toGrp ⟶ G) : Set S :=
  {s | IsMaximalTorus
    (T := (CommGroupScheme.baseChange (S.fromSpecResidueField s)).obj T)
    ((baseChange (S.fromSpecResidueField s)).map i)}

/-- Replacing the source by an isomorphic torus preserves its maximal locus. -/
theorem maximalTorusLocus_iso_comp (e : T'.toGrp ≅ T.toGrp) (i : T.toGrp ⟶ G) :
    maximalTorusLocus (T := T') (e.hom ≫ i) = maximalTorusLocus i := by
  ext s
  simp only [maximalTorusLocus, Set.mem_ofPred_eq, Functor.map_comp]
  exact IsMaximalTorus.iso_comp_iff
    (T := (CommGroupScheme.baseChange (S.fromSpecResidueField s)).obj T)
    (T' := (CommGroupScheme.baseChange (S.fromSpecResidueField s)).obj T')
    ((baseChange (S.fromSpecResidueField s)).mapIso e) _

namespace splitTorus

variable {R : Type u} [CommRing R] (I : Type u) [Fintype I] [DecidableEq I]
  (G : GroupScheme (Spec (CommRingCat.of R)))
  [Smooth G.X.hom] [IsAffineHom G.X.hom]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)

/-- For a reductive ambient group, the maximal locus of a coordinate torus
is its geometric self-centralizing locus. -/
theorem maximalTorusLocus_eq_geometricSelfCentralizingTorusLocus
    (hG : IsReductive G) (hi : IsClosedSubgroup i) :
    maximalTorusLocus (T := commGroupScheme _ I) i =
      geometricSelfCentralizingTorusLocus I G i := by
  ext s
  constructor
  · intro hs
    exact mem_geometricSelfCentralizingTorusLocus_of_geometricFiberHom I G i hG hi s
      (isMaximalTorus_geometricFiberHom_of_residueFibre I G i s hs)
  · intro hs
    exact isMaximalTorus_residueFibre_of_geometricFiberHom I G i hi s
      (isMaximalTorus_geometricFiberHom_of_mem I G i hG hi s hs)

/-- The maximal locus of a closed coordinate split torus in a reductive
group over any ring is open. -/
theorem isOpen_maximalTorusLocus (hG : IsReductive G) (hi : IsClosedSubgroup i) :
    IsOpen (maximalTorusLocus (T := commGroupScheme _ I) i) := by
  rw [maximalTorusLocus_eq_geometricSelfCentralizingTorusLocus I G i hG hi]
  exact isOpen_geometricSelfCentralizingTorusLocus I G i hi

end splitTorus

/-- A closed split torus in a reductive group over an arbitrary affine ring
has an open maximal locus. -/
theorem IsReductive.isOpen_maximalTorusLocus_of_isSplitTorus
    {R : Type u} [CommRing R] {G : GroupScheme (Spec (CommRingCat.of R))}
    (hG : IsReductive G) {T : CommGroupScheme (Spec (CommRingCat.of R))}
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G) (hi : IsClosedSubgroup i) :
    IsOpen (maximalTorusLocus i) := by
  classical
  let := hG.smooth
  let := hG.isAffineHom
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let : Fintype I := Fintype.ofFinite I
  have h := splitTorus.isOpen_maximalTorusLocus I G (e.inv ≫ i) hG
    (hi.iso_comp e.symm)
  have he := maximalTorusLocus_iso_comp (T' := splitTorus.commGroupScheme _ I) e.symm i
  exact he ▸ h

end Langlands.GroupScheme
