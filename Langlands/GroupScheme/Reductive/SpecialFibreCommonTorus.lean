import Langlands.GroupScheme.Torus.LocalSpecialization
import Langlands.GroupScheme.Reductive.StrictHenselianGenericIsoProof

/-! # A common maximal torus for a homomorphism with isomorphic special fibre -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

/-- A specified field-valued isomorphism reflects to the actual residue-field
fibre at the image of its point. -/
theorem isIso_residueFibre_of_fieldPoint
    {S : Scheme.{u}} {G H : GroupScheme S} (f : G ⟶ H)
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S)
    (hf : IsIso ((GroupScheme.baseChange b).map f)) :
    IsIso ((GroupScheme.baseChange
      (S.fromSpecResidueField (b (IsLocalRing.closedPoint k)))).map f) := by
  let : Algebra (S.residueField (b (IsLocalRing.closedPoint k))) k :=
    (fieldPointResidueMap b).hom.toAlgebra
  let a := S.fromSpecResidueField (b (IsLocalRing.closedPoint k))
  let c := Spec.map (fieldPointResidueMap b)
  have hc : IsIso ((GroupScheme.baseChange (c ≫ a)).map f) := by
    dsimp [c, a]
    rw [fieldPointResidueMap_factorization]
    exact hf
  have := (TorusIsomorphismLocus.isIso_comp_baseChange_iff a c f).mp hc
  obtain ⟨hcs, hcf, hcq⟩ :=
    fieldExtension_fpqc (S.residueField (b (IsLocalRing.closedPoint k))) k
  have : Surjective c := hcs
  have : Flat c := hcf
  have : QuasiCompact c := hcq
  exact isIso_of_baseChange c ((GroupScheme.baseChange a).map f)

/-- The quotient residue-field isomorphism condition implies the canonical
scheme-residue closed-fibre isomorphism condition. -/
theorem isIso_closedFibre_of_specialFibre
    {R : Type u} [CommRing R] [IsLocalRing R]
    {G H : GroupScheme (Spec (CommRingCat.of R))} (f : G ⟶ H)
    (hf : TorusLocalSpecialization.IsSpecialFibreIsomorphism f) :
    IsIso ((GroupScheme.baseChange
      ((Spec (CommRingCat.of R)).fromSpecResidueField
        (IsLocalRing.closedPoint R))).map f) := by
  have h := isIso_residueFibre_of_fieldPoint f
    (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) hf
  have hb : (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))
      (IsLocalRing.closedPoint (IsLocalRing.ResidueField R)) =
        IsLocalRing.closedPoint R :=
    IsLocalRing.comap_closedPoint (IsLocalRing.residue R)
  rwa [hb] at h

/-- A closed split torus maximal in every source fibre stays maximal in every
target fibre under a homomorphism with isomorphic special fibre over a local ring. -/
theorem IsReductive.isFibrewiseMaximalTorus_comp_of_specialFibreIso
    {R : Type u} [CommRing R] [IsLocalRing R]
    {G H : GroupScheme (Spec (CommRingCat.of R))} (hH : IsReductive H)
    {T : CommGroupScheme (Spec (CommRingCat.of R))} (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) (hi : IsClosedSubgroup i)
    (hmax : IsFibrewiseMaximalTorus i) (f : G ⟶ H)
    (hf : TorusLocalSpecialization.IsSpecialFibreIsomorphism f) :
    IsClosedSubgroup (i ≫ f) ∧ IsFibrewiseMaximalTorus (i ≫ f) := by
  let := hH.isAffineHom
  have hclosed := TorusLocalSpecialization.isClosedSubgroup_comp_of_specialFibreIso
    hT i hi f hf
  refine ⟨hclosed, ?_⟩
  have hfc := isIso_closedFibre_of_specialFibre f hf
  let := hfc
  apply hH.isMaximalTorus_residueFibre_of_closedFibre hT (i ≫ f) hclosed
  rw [Functor.map_comp]
  exact (hmax (IsLocalRing.closedPoint R)).comp_iso (asIso ((GroupScheme.baseChange
    ((Spec (CommRingCat.of R)).fromSpecResidueField
      (IsLocalRing.closedPoint R))).map f))

/-- A common coordinate maximal torus for the specified homomorphism: its
source embedding and its composite with the homomorphism are both closed and
maximal in every residue-field fibre. -/
def HasCommonCoordinateMaximalTorus
    {S : Scheme.{u}} {G H : GroupScheme S} (f : G ⟶ H) : Prop :=
  ∃ (I : Type u) (_ : Fintype I) (i : splitTorus S I ⟶ G),
    IsClosedSubgroup i ∧
    IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme S I) i ∧
    IsClosedSubgroup (i ≫ f) ∧
    IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme S I) (i ≫ f)

/-- A homomorphism of reductive groups over a strictly Henselian local ring
with isomorphic special fibre has a common coordinate maximal torus. -/
theorem hasCommonCoordinateMaximalTorus_of_specialFibreIso
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)]
    {G H : GroupScheme (Spec (CommRingCat.of R))}
    (hG : IsReductive G) (hH : IsReductive H) (f : G ⟶ H)
    (hf : TorusLocalSpecialization.IsSpecialFibreIsomorphism f) :
    HasCommonCoordinateMaximalTorus f := by
  obtain ⟨I, hI, i, hi, hmax⟩ :=
    exists_coordinate_fibrewiseMaximalTorus_of_strictHenselian R G hG
  let : Fintype I := hI
  have hT : IsSplitTorus (splitTorus (Spec (CommRingCat.of R)) I) :=
    isSplitTorus_splitTorus I
  obtain ⟨hic, hmaxc⟩ := hH.isFibrewiseMaximalTorus_comp_of_specialFibreIso
    (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) hT i hi hmax f hf
  exact ⟨I, hI, i, hi, hmax, hic, hmaxc⟩

end Langlands.GroupScheme
