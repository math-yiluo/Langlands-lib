import Langlands.GroupScheme.Reductive.IsogenyRootMonicity
import Langlands.GroupScheme.Reductive.IsogenyRootFactors
import Langlands.GroupScheme.Reductive.IsogenyTorusRestriction

/-! # Actual root parametrizations for factor-one root pullbacks -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000

namespace Langlands.GroupScheme

namespace VectorGroup.IsTorusEquivariant

variable {k : Type u} [Field k]
    {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {i : T'.toGrp ⟶ G}
    {x : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G}
    (t : T ⟶ T') {β : characterLattice T'}

/-- Exact scalar equivariance descends through a flat surjective torus map,
on arbitrary scheme tests. -/
theorem of_torusPullback (ht : IsIsogeny (CommGroupScheme.groupHom t))
    (hx : VectorGroup.IsTorusEquivariant (CommGroupScheme.groupHom t ≫ i) x (t ≫ β)) :
    VectorGroup.IsTorusEquivariant i x β := by
  intro U s a
  let q := (CommGroupScheme.groupHom t).hom.hom
  let : Flat q.left := ht.2.1
  let : Surjective q.left := ht.2.2
  let V : Over (Spec (CommRingCat.of k)) :=
    Over.mk (pullback.fst s.left q.left ≫ U.hom)
  let c : V ⟶ U := Over.homMk (pullback.fst s.left q.left) rfl
  let z : V ⟶ T.X :=
    Over.homMk (pullback.snd s.left q.left) (by
      rw [← Over.w q, ← Category.assoc, ← pullback.condition,
        Category.assoc, Over.w s]
      rfl)
  have hcs : c ≫ s = z ≫ q := Over.OverMorphism.ext pullback.condition
  let : Flat c.left := by change Flat (pullback.fst _ _); infer_instance
  let : Surjective c.left := by change Surjective (pullback.fst _ _); infer_instance
  let : Epi c.left := Flat.epi_of_flat_of_surjective _
  let : Epi c := Over.epi_of_epi_left _
  have hv : VectorGroup.charValue (t ≫ β) V z =
      c.left.appTop (VectorGroup.charValue β U s) := by
    change VectorGroup.charValue β V (z ≫ q) = _
    rw [← hcs, VectorGroup.charValue_comp]
  apply (cancel_epi c).1
  simp only [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc,
    VectorGroup.scalarPoint_comp, map_mul]
  have h := hx V z (c.left.appTop a)
  dsimp only [q] at hcs
  simpa only [Grp.comp_hom_hom, ← Category.assoc, ← hcs, hv] using h

end VectorGroup.IsTorusEquivariant

namespace RelativeRoot

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom]
    {i : T.toGrp ⟶ G} {α : characterLattice T}

/-- A root with no higher positive roots has an actual equivariant standard
additive-line representative. -/
theorem exists_equivariant_rootParametrization
    (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp)
    (hi : IsMaximalTorus i) (hα : α ∈ roots i)
    (hhigh : HasNoHigherRoots i α) :
    ∃ u : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G,
      (subgroup i α).IsRepresentedBy u ∧
        VectorGroup.IsTorusEquivariant i u α := by
  let : Smooth G.X.hom := hG.smooth
  obtain ⟨U, j, hj, hjclosed, _, _⟩ :=
    subgroup_isSmoothConnectedClosed_of_ne_zero hT i α hα.1
  let : IsClosedImmersion j.hom.hom.left := hjclosed
  let : IsAffineHom U.X.hom := hjclosed.isAffineHom
  let : CommGroup (lieKernel U k) := lieKernelCommGroup U
  let : Module k (Additive (lieKernel U k)) := lieKernelModule U
  obtain ⟨n, e, he⟩ :=
    exists_weightVectorCoordinates_of_noHigherRoots hT i hα.1 hhigh hj
  have hn : n = 1 := by
    let E := vectorLieCoordinates e he.1 (CommAlgCat.of k k)
    let L := representedRootLieEquiv hT i hα.1 hhigh hj
    obtain ⟨l⟩ := splitRootLieLine k G hG T hT i hi α hα
    calc
      n = Module.finrank k (Fin n → k) := by simp
      _ = Module.finrank k (Additive (lieKernel U k)) := E.finrank_eq.symm
      _ = Module.finrank k (weightSpace i α) := L.finrank_eq
      _ = 1 := by rw [← l.finrank_eq, Module.finrank_self]
  subst n
  let E := vectorGroupIso e he.1
  let u := E.inv ≫ j
  have hc (Z : Over (Spec (CommRingCat.of k))) (c : Γ(Z.left, ⊤)) :
      (e Z (VectorGroup.scalarPoint (CommRingCat.of k) Z c ≫ E.inv.hom.hom)).toAdd =
        fun _ => c := by
    have h := coordinates_comp_vectorGroupIso_hom e he.1 Z
      (VectorGroup.scalarPoint (CommRingCat.of k) Z c ≫ E.inv.hom.hom)
    change VectorGroup.coordinates (CommRingCat.of k) 1 Z
      ((VectorGroup.scalarPoint (CommRingCat.of k) Z c ≫ E.inv.hom.hom) ≫
        E.hom.hom.hom) = _ at h
    rw [Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom,
      Category.comp_id] at h
    exact (congrArg Multiplicative.toAdd h.symm).trans
      (funext fun l => VectorGroup.coordinates_scalarPoint _ _ _ l)
  refine ⟨u, ⟨?_, ?_⟩, ?_⟩
  · change Mono (E.inv.hom.hom ≫ j.hom.hom)
    let : Mono j.hom.hom := hj.1
    infer_instance
  · exact (SubgroupFunctor.range_iso_comp E.symm j).trans hj.2
  · intro Z s c
    have ha : (subgroupAction i α j hj).act s
          (VectorGroup.scalarPoint (CommRingCat.of k) Z c ≫ E.inv.hom.hom) =
        VectorGroup.scalarPoint (CommRingCat.of k) Z
          (VectorGroup.charValue α Z s * c) ≫ E.inv.hom.hom := by
      apply (e Z).injective
      apply Multiplicative.toAdd.injective
      rw [he.2, hc, hc]
      rfl
    have h := (subgroupAction_act_comp i α j hj s
      (VectorGroup.scalarPoint (CommRingCat.of k) Z c ≫ E.inv.hom.hom)).symm
    rw [ha] at h
    simpa only [u, Grp.comp_hom_hom, ← Category.assoc] using h

end RelativeRoot

namespace IsRootDatumOf

variable {k : Type u} [Field k]
    {G G' : GroupScheme (Spec (CommRingCat.of k))}
    {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom G'.X.hom] [LocallyOfFiniteType G'.X.hom]
    {J J' : Type u}
    {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
    {P' : RootDatum J' (characterLattice T') (cocharacterLattice T')}
    [P.IsReduced] [P'.IsReduced]
    {i : T.toGrp ⟶ G} {i' : T'.toGrp ⟶ G'}
    (hP : IsRootDatumOf i P) (hP' : IsRootDatumOf i' P')

include hP hP'

/-- Exact root pullback makes the composite of an actual source additive
root representative represent the whole corresponding target root subgroup. -/
theorem exists_rootParametrization_of_exactPullback
    (hG : IsConnectedReductive G) (hG' : IsConnectedReductive G')
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (hi : IsMaximalTorus i) (hi' : IsMaximalTorus i')
    (φ : G ⟶ G') [IsFinite φ.hom.hom.left] (t : T ⟶ T')
    (ht : IsIsogeny (CommGroupScheme.groupHom t))
    (hsquare : i ≫ φ = CommGroupScheme.groupHom t ≫ i')
    (r : J) (s : J') (hroot : t ≫ P'.root s = P.root r) :
    ∃ u : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G,
      (RelativeRoot.subgroup i (P.root r)).IsRepresentedBy u ∧
        (RelativeRoot.subgroup i' (P'.root s)).IsRepresentedBy (u ≫ φ) := by
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom T'.toGrp.X.hom := hi'.2.1.isAffineHom
  let hV : RelativeRoot.IsVectorGroupOfDimension
      (VectorGroup.groupScheme (CommRingCat.of k) 1) 1 :=
    ⟨VectorGroup.coordinates (CommRingCat.of k) 1, VectorGroup.isNaturalVectorCoordinates⟩
  let : IsAffineHom (VectorGroup.groupScheme (CommRingCat.of k) 1).X.hom :=
    hV.isAffineHom
  let : Smooth (VectorGroup.groupScheme (CommRingCat.of k) 1).X.hom := hV.smooth
  let : ConnectedSpace (VectorGroup.groupScheme (CommRingCat.of k) 1).X.left :=
    hV.connectedSpace
  have hr : P.root r ∈ roots i := hP.2.1 ▸ Set.mem_range_self r
  have hs : P'.root s ∈ roots i' := hP'.2.1 ▸ Set.mem_range_self s
  obtain ⟨u, hu, hue⟩ := RelativeRoot.exists_equivariant_rootParametrization
    hG hT hi hr (hP.noHigherRoots hT r)
  have hcomp : VectorGroup.IsTorusEquivariant
      (CommGroupScheme.groupHom t ≫ i') (u ≫ φ) (t ≫ P'.root s) := by
    rw [hroot]
    intro Z z c
    have h := congrArg (fun v => v ≫ φ.hom.hom) (hue Z z c)
    rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp] at h
    have hz := congrArg (fun f : T.toGrp ⟶ G' => z ≫ f.hom.hom) hsquare
    simp only [Grp.comp_hom_hom] at hz
    simpa only [Grp.comp_hom_hom, Category.assoc, hz] using h
  have he := hcomp.of_torusPullback t ht
  let : Mono u.hom.hom := hu.1
  let : IsClosedImmersion u.hom.hom.left := HomImage.isClosedSubgroup_of_mono u
  let : IsFinite (u ≫ φ).hom.hom.left := by
    change IsFinite (u.hom.hom.left ≫ φ.hom.hom.left)
    infer_instance
  let : Mono (u ≫ φ).hom.hom :=
    HomImage.mono_of_noHigherRoots hT' i'
      (VectorGroup.weightAction (P'.root s))
      (VectorGroup.coordinates (CommRingCat.of k) 1)
      (VectorGroup.isWeightVectorCoordinates_weightAction (P'.root s)) (u ≫ φ)
      (fun Z z v => he.weightAction_comp Z z v) hs.1 (hP'.noHigherRoots hT' s)
  exact ⟨u, hu, he.represents_root hG' hT' hi' hs (hP'.noHigherRoots hT' s)⟩

/-- A chosen actual source root parametrization whose composite represents
the corresponding target root, for a factor-one pullback equation. -/
def rootParametrizationOfExactPullback
    (hG : IsConnectedReductive G) (hG' : IsConnectedReductive G')
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (hi : IsMaximalTorus i) (hi' : IsMaximalTorus i')
    (φ : G ⟶ G') [IsFinite φ.hom.hom.left] (t : T ⟶ T')
    (ht : IsIsogeny (CommGroupScheme.groupHom t))
    (hsquare : i ≫ φ = CommGroupScheme.groupHom t ≫ i')
    (r : J) (s : J') (hroot : t ≫ P'.root s = P.root r) :
    {u : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G //
      (RelativeRoot.subgroup i (P.root r)).IsRepresentedBy u ∧
        (RelativeRoot.subgroup i' (P'.root s)).IsRepresentedBy (u ≫ φ)} :=
  Classical.choice (by
    obtain ⟨u, hu⟩ := hP.exists_rootParametrization_of_exactPullback hP'
      hG hG' hT hT' hi hi' φ t ht hsquare r s hroot
    exact ⟨⟨u, hu⟩⟩)

end IsRootDatumOf

end Langlands.GroupScheme
