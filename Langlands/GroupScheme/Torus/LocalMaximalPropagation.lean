import Langlands.GroupScheme.Reductive.LiftedTorusNeighbourhood
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerProof

/-! # Propagating maximality of a split torus from the closed fibre -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace splitTorus

variable {r : Type u} [CommRing r]
  (I : Type u) [Fintype I] [DecidableEq I]
  (G : GroupScheme (Spec (CommRingCat.of r))) [Smooth G.X.hom] [IsAffineHom G.X.hom]
  (i : splitTorus (Spec (CommRingCat.of r)) I ⟶ G)

local instance propagation_smooth_geometricFiber (s : Spec (CommRingCat.of r)) :
    Smooth (geometricFiber G s).X.hom :=
  inferInstanceAs (Smooth (Limits.pullback.snd G.X.hom (geometricPoint _ s)))

local instance propagation_affine_geometricFiber (s : Spec (CommRingCat.of r)) :
    IsAffineHom (geometricFiber G s).X.hom :=
  inferInstanceAs (IsAffineHom (Limits.pullback.snd G.X.hom (geometricPoint _ s)))

omit [DecidableEq I] in
/-- Maximality in the actual residue fibre gives maximality of the chosen
geometric-fibre split-torus map. -/
theorem isMaximalTorus_geometricFiberHom_of_residueFibre (s : Spec (CommRingCat.of r))
    (hmax : IsMaximalTorus
      (T := (CommGroupScheme.baseChange
        ((Spec (CommRingCat.of r)).fromSpecResidueField s)).obj (commGroupScheme _ I))
      ((baseChange ((Spec (CommRingCat.of r)).fromSpecResidueField s)).map i)) :
    IsMaximalTorus (T := commGroupScheme _ I) (geometricFiberHom I G i s) := by
  have hcm : IsMaximalTorus (T := commGroupScheme _ I)
      (RelativeCocharacterCentralizer.baseChangedTorusHom I G i
        ((Spec (CommRingCat.of r)).fromSpecResidueField s)) :=
    IsMaximalTorus.iso_comp
      (T := (CommGroupScheme.baseChange
        ((Spec (CommRingCat.of r)).fromSpecResidueField s)).obj (commGroupScheme _ I))
      (T' := commGroupScheme _ I) (baseChangeIso _ I).symm hmax
  exact isMaximalTorus_fieldPoint_extension I G i
    (k := (Spec (CommRingCat.of r)).residueField s)
    (K := AlgebraicClosure ((Spec (CommRingCat.of r)).residueField s)) _ hcm

omit [DecidableEq I] [Smooth G.X.hom] [IsAffineHom G.X.hom] in
/-- Maximality of the chosen geometric-fibre split-torus map reflects to the
actual residue fibre. -/
theorem isMaximalTorus_residueFibre_of_geometricFiberHom (hi : IsClosedSubgroup i)
    (s : Spec (CommRingCat.of r))
    (hgeom : IsMaximalTorus (T := commGroupScheme _ I) (geometricFiberHom I G i s)) :
    IsMaximalTorus
      (T := (CommGroupScheme.baseChange
        ((Spec (CommRingCat.of r)).fromSpecResidueField s)).obj (commGroupScheme _ I))
      ((baseChange ((Spec (CommRingCat.of r)).fromSpecResidueField s)).map i) := by
  have hactual : IsMaximalTorus
      (T := (CommGroupScheme.baseChange (geometricPoint _ s)).obj (commGroupScheme _ I))
      ((baseChange (geometricPoint _ s)).map i) :=
    (IsMaximalTorus.iso_comp_iff
      (T := (CommGroupScheme.baseChange (geometricPoint _ s)).obj (commGroupScheme _ I))
      (T' := commGroupScheme _ I) (baseChangeIso (geometricPoint _ s) I).symm _).mp hgeom
  have hcomp := isMaximalTorus_baseChange_comp
    ((Spec (CommRingCat.of r)).fromSpecResidueField s)
    (toAlgebraicClosure ((Spec (CommRingCat.of r)).residueField s))
    (commGroupScheme _ I) i hactual
  exact IsMaximalTorus.of_baseChange
    (k := (Spec (CommRingCat.of r)).residueField s)
    (K := AlgebraicClosure ((Spec (CommRingCat.of r)).residueField s))
    (hi.baseChange _) hcomp

omit [DecidableEq I] in
/-- The chosen geometric point over `s` sends its closed point to `s`. -/
theorem geometricPoint_closedPoint (s : Spec (CommRingCat.of r)) :
    geometricPoint (Spec (CommRingCat.of r)) s
      (IsLocalRing.closedPoint
        (AlgebraicClosure ((Spec (CommRingCat.of r)).residueField s))) = s := by
  change (Spec (CommRingCat.of r)).fromSpecResidueField s _ = s
  exact Scheme.fromSpecResidueField_apply _ _

/-- A geometric-fibre maximal torus of a reductive group is self-centralizing
in the geometric identity component. -/
theorem mem_geometricSelfCentralizingTorusLocus_of_geometricFiberHom
    (hG : IsReductive G) (hi : IsClosedSubgroup i) (s : Spec (CommRingCat.of r))
    (hgeom : IsMaximalTorus (T := commGroupScheme _ I) (geometricFiberHom I G i s)) :
    s ∈ geometricSelfCentralizingTorusLocus I G i := by
  have hred : s ∈ identityComponentReductiveLocus G :=
    (hG.geometricFiber s).isConnectedReductive_of_isAlgClosed.identityComponent
  have hs : geometricPoint (Spec (CommRingCat.of r)) s
      (IsLocalRing.closedPoint
        (AlgebraicClosure ((Spec (CommRingCat.of r)).residueField s))) ∈
        identityComponentReductiveLocus G := by
    rw [geometricPoint_closedPoint]
    exact hred
  have h := mem_geometricSelfCentralizingTorusLocus_of_maximal_fieldPoint I G i
    (fun k _ _ H hH T j hj => maximalTorusCentralizer k H hH T j hj)
    hi (geometricPoint _ s) hs hgeom
  rwa [geometricPoint_closedPoint] at h

omit [DecidableEq I] in
/-- On the self-centralizing locus of a reductive group, the chosen geometric
fibre map itself is a maximal torus. -/
theorem isMaximalTorus_geometricFiberHom_of_mem
    (hG : IsReductive G) (hi : IsClosedSubgroup i) (s : Spec (CommRingCat.of r))
    (hs : s ∈ geometricSelfCentralizingTorusLocus I G i) :
    IsMaximalTorus (T := commGroupScheme _ I) (geometricFiberHom I G i s) := by
  let : ConnectedSpace (geometricFiber G s).X.left := (hG.geometricFiber s).connectedSpace
  have h := (isMaximalTorus_geometricIdentityComponentHom_of_mem I G i hi s hs).comp_iso
    (IdentityComponent.connectedIso (geometricFiber G s))
  rwa [IdentityComponent.connectedIso_hom, geometricIdentityComponentHom_comp] at h

/-- Over a local ring, a point of the open self-centralizing locus at the
closed point forces every point into this locus. -/
theorem mem_geometricSelfCentralizingTorusLocus_of_closedPoint [IsLocalRing r]
    (hi : IsClosedSubgroup i)
    (h₀ : IsLocalRing.closedPoint r ∈ geometricSelfCentralizingTorusLocus I G i)
    (s : Spec (CommRingCat.of r)) :
    s ∈ geometricSelfCentralizingTorusLocus I G i :=
  (IsLocalRing.specializes_closedPoint (R := r) s).mem_open
    (isOpen_geometricSelfCentralizingTorusLocus I G i hi) h₀

/-- A closed standard split torus in a reductive group over a local ring is
maximal on all actual residue fibres if it is maximal on the closed fibre. -/
theorem isMaximalTorus_residueFibre_of_closedFibre [IsLocalRing r]
    (hG : IsReductive G) (hi : IsClosedSubgroup i)
    (hmax : IsMaximalTorus
      (T := (CommGroupScheme.baseChange
        ((Spec (CommRingCat.of r)).fromSpecResidueField (IsLocalRing.closedPoint r))).obj
          (commGroupScheme _ I))
      ((baseChange
        ((Spec (CommRingCat.of r)).fromSpecResidueField (IsLocalRing.closedPoint r))).map i))
    (s : Spec (CommRingCat.of r)) :
    IsMaximalTorus
      (T := (CommGroupScheme.baseChange
        ((Spec (CommRingCat.of r)).fromSpecResidueField s)).obj (commGroupScheme _ I))
      ((baseChange ((Spec (CommRingCat.of r)).fromSpecResidueField s)).map i) := by
  have h₀ := mem_geometricSelfCentralizingTorusLocus_of_geometricFiberHom I G i hG hi _
    (isMaximalTorus_geometricFiberHom_of_residueFibre I G i _ hmax)
  exact isMaximalTorus_residueFibre_of_geometricFiberHom I G i hi s
    (isMaximalTorus_geometricFiberHom_of_mem I G i hG hi s
      (mem_geometricSelfCentralizingTorusLocus_of_closedPoint I G i hi h₀ s))

end splitTorus

/-- Precomposing with an inverse source isomorphism leaves maximality of every
actual pullback unchanged. -/
theorem isMaximalTorus_baseChange_inv_comp_iff {S : Scheme.{u}} {k : Type u} [Field k]
    (b : Spec (CommRingCat.of k) ⟶ S)
    {T T' : CommGroupScheme S} (e : T.toGrp ≅ T'.toGrp) {G : GroupScheme S}
    (i : T.toGrp ⟶ G) :
    IsMaximalTorus (T := (CommGroupScheme.baseChange b).obj T') ((baseChange b).map (e.inv ≫ i)) ↔
      IsMaximalTorus (T := (CommGroupScheme.baseChange b).obj T) ((baseChange b).map i) := by
  rw [Functor.map_comp]
  exact IsMaximalTorus.iso_comp_iff
    (T := (CommGroupScheme.baseChange b).obj T) (T' := (CommGroupScheme.baseChange b).obj T')
    ((baseChange b).mapIso e.symm) _

/-- A closed split torus in a reductive group over a local ring is maximal on
all actual residue fibres if it is maximal on the closed fibre. -/
theorem IsReductive.isMaximalTorus_residueFibre_of_closedFibre
    {R : Type u} [CommRing R] [IsLocalRing R]
    {G : GroupScheme (Spec (CommRingCat.of R))} (hG : IsReductive G)
    {T : CommGroupScheme (Spec (CommRingCat.of R))} (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) (hi : IsClosedSubgroup i)
    (hmax : IsMaximalTorus
      (T := (CommGroupScheme.baseChange
        ((Spec (CommRingCat.of R)).fromSpecResidueField (IsLocalRing.closedPoint R))).obj T)
      ((baseChange
        ((Spec (CommRingCat.of R)).fromSpecResidueField (IsLocalRing.closedPoint R))).map i))
    (s : Spec (CommRingCat.of R)) :
    IsMaximalTorus
      (T := (CommGroupScheme.baseChange
        ((Spec (CommRingCat.of R)).fromSpecResidueField s)).obj T)
      ((baseChange ((Spec (CommRingCat.of R)).fromSpecResidueField s)).map i) := by
  classical
  let := hG.smooth
  let := hG.isAffineHom
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let : Fintype I := Fintype.ofFinite I
  have hj : IsClosedSubgroup (e.inv ≫ i) := hi.iso_comp e.symm
  have hm := (isMaximalTorus_baseChange_inv_comp_iff
    (k := (Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R))
    ((Spec (CommRingCat.of R)).fromSpecResidueField (IsLocalRing.closedPoint R))
    (T' := splitTorus.commGroupScheme _ I) e i).mpr hmax
  exact (isMaximalTorus_baseChange_inv_comp_iff
    (k := (Spec (CommRingCat.of R)).residueField s)
    ((Spec (CommRingCat.of R)).fromSpecResidueField s)
    (T' := splitTorus.commGroupScheme _ I) e i).mp
    (splitTorus.isMaximalTorus_residueFibre_of_closedFibre I G (e.inv ≫ i) hG hj hm s)

/-- Over every commutative local ring, an actual closed split torus in a
reductive group scheme that is maximal on the closed fibre is maximal on every
actual residue-field fibre. -/
def LocalClosedFibreMaximalPropagationStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R]
    (G : GroupScheme (Spec (CommRingCat.of R))), IsReductive G →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of R))) (i : T.toGrp ⟶ G),
      IsSplitTorus T.toGrp → IsClosedSubgroup i →
      IsMaximalTorus
        (T := (CommGroupScheme.baseChange
          ((Spec (CommRingCat.of R)).fromSpecResidueField (IsLocalRing.closedPoint R))).obj T)
        ((baseChange
          ((Spec (CommRingCat.of R)).fromSpecResidueField (IsLocalRing.closedPoint R))).map i) →
      ∀ s : Spec (CommRingCat.of R),
        IsMaximalTorus
          (T := (CommGroupScheme.baseChange
            ((Spec (CommRingCat.of R)).fromSpecResidueField s)).obj T)
          ((baseChange ((Spec (CommRingCat.of R)).fromSpecResidueField s)).map i)

/-- Maximality of a closed split torus propagates from the closed fibre over
every commutative local ring. -/
theorem localClosedFibreMaximalPropagation :
    LocalClosedFibreMaximalPropagationStatement.{u} :=
  fun _ _ _ _ hG _ i hT hi hmax s => hG.isMaximalTorus_residueFibre_of_closedFibre hT i hi hmax s

end Langlands.GroupScheme
