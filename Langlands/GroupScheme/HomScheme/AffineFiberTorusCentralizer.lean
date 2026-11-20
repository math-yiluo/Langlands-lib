import Langlands.AlgebraicGeometry.ArtinianLiftingSmooth
import Langlands.AlgebraicGeometry.SmoothNilIdealSections
import Langlands.GroupScheme.HomScheme.AffineFiberValuation
import Langlands.GroupScheme.Torus.CentralizerConnected
import Langlands.GroupScheme.Torus.RelativeFieldComparison
import Langlands.GroupScheme.Torus.SeparatedCentralizerModel

/-! # Geometry of torus centralizers with affine residue fibres -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.TorusSubgroupModuli

variable {S : Scheme.{u}} {G C : GroupScheme S} {T : CommGroupScheme S}

/-- A closed subgroup of a group with affine residue fibres has affine residue fibres. -/
theorem hasAffineResidueFibers_of_closedSubgroup {c : C ⟶ G}
    (hc : IsClosedSubgroup c) (hG : HasAffineResidueFibers G) : HasAffineResidueFibers C := by
  intro s
  let c' := (baseChange (S.fromSpecResidueField s)).map c
  have : IsClosedImmersion c'.hom.hom.left := hc.baseChange _
  have : IsAffineHom (RelativeIdentityComponent.residueFiber G s).X.hom := hG s
  rw [← Over.w c'.hom.hom]
  infer_instance

/-- A torus centralizer in a smooth group with affine, geometrically connected
fibres has geometrically connected fibres. -/
theorem geometricallyConnected_of_affineFiberCentralizer
    [Smooth G.X.hom] [GeometricallyConnected G.X.hom] (hG : HasAffineResidueFibers G)
    (t : T.toGrp ⟶ G) (hT : RelativeTorus.IsTorus T.toGrp) {c : C ⟶ G}
    (hc : (torusCentralizer t).IsRepresentedBy c) : GeometricallyConnected C.X.hom := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun k _ b => ?_⟩
  let G' := (baseChange b).obj G
  let T' := (CommGroupScheme.baseChange b).obj T
  let t' : T'.toGrp ⟶ G' := (baseChange b).map t
  have : IsAffineHom G'.X.hom := G.isAffineHom_fieldPullback_of_residueFibers hG b
  have : Smooth G'.X.hom := MorphismProperty.pullback_snd (P := @Smooth) _ _ inferInstance
  have : ConnectedSpace G'.X.left :=
    (geometrically_iff_of_isClosedUnderIsomorphisms.mp
      (GeometricallyConnected.geometrically_connectedSpace (f := G.X.hom))) k b
  have hrep : (torusCentralizer t').IsRepresentedBy ((baseChange b).map c) := by
    rw [torusCentralizer_baseChange]
    exact hc.baseChange b
  exact (hT.baseChange b).isTorus.connectedSpace_centralizer t' hrep

/-- For a smooth ambient group that becomes affine on local Artinian
tests, an actual closed relative torus centralizer is smooth over any locally
noetherian base. -/
theorem smooth_of_artinianAffineCentralizer [IsLocallyNoetherian S] [Smooth G.X.hom]
    (hA : ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A]
      (a : Spec (CommRingCat.of A) ⟶ S), IsAffineHom ((baseChange a).obj G).X.hom)
    (t : T.toGrp ⟶ G) (hT : RelativeTorus.IsTorus T.toGrp) {c : C ⟶ G}
    (hclosed : IsClosedSubgroup c) (hrep : (torusCentralizer t).IsRepresentedBy c) :
    Smooth C.X.hom := by
  have : IsClosedImmersion c.hom.hom.left := hclosed
  have : LocallyOfFiniteType C.X.hom := by
    rw [← c.hom.hom.w]
    infer_instance
  apply Langlands.AlgebraicGeometry.ArtinianLiftingSmooth.smooth_of_liftsArtinian
  intro A B _ _ _ _ _ _ q hq hker α β w _
  let Q := baseChange β
  let G' := Q.obj G
  let C' := Q.obj C
  let T' := (CommGroupScheme.baseChange β).obj T
  let t' : T'.toGrp ⟶ G' := Q.map t
  have : IsAffineHom G'.X.hom := hA A β
  have hG' : Smooth G'.X.hom := MorphismProperty.pullback_snd (P := @Smooth) _ _ inferInstance
  obtain ⟨D, d, _, hD, hd⟩ := relativeTorusCentralizer_hasSmoothClosedRepresentative t'
    (hT.baseChange β) hG'
  have hrep' : (torusCentralizer t').IsRepresentedBy (Q.map c) := by
    rw [torusCentralizer_baseChange]
    exact hrep.baseChange β
  have : Smooth C'.X.hom := smooth_of_over_iso ((Grp.forget _).mapIso
    (hrep'.isoOfIsRepresentedBy hd)) hD
  let : Algebra A B := q.toAlgebra
  let b := Spec.map (CommRingCat.ofHom q)
  let x : Spec (CommRingCat.of B) ⟶ C'.X.left := pullback.lift α b w
  have hk : RingHom.ker q ≤ nilradical A := by
    have hm : RingHom.ker q ≤ maximalIdeal A := le_maximalIdeal (RingHom.ker_ne_top q)
    intro a ha
    apply mem_nilradical.mpr
    refine ⟨2, ?_⟩
    have he := Ideal.mul_mem_mul (hm ha) ha
    rw [hker, Ideal.mem_bot] at he
    simpa only [pow_two] using he
  obtain ⟨y, hy, hxy⟩ := Langlands.AlgebraicGeometry.SmoothNilIdealSections.exists_lift_of_nil_kernel
    C'.X.hom hq hk x (pullback.lift_snd _ _ _)
  refine ⟨y ≫ pullback.fst C.X.hom β, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc]
    change (y ≫ C'.X.hom) ≫ β = β
    rw [hy, Category.id_comp]
  · rw [← Category.assoc]
    change b ≫ y = x at hxy
    exact (congrArg (fun a => a ≫ pullback.fst C.X.hom β) hxy).trans (pullback.lift_fst _ _ _)

/-- The represented centralizer of a relative torus in a smooth separated
quasi-compact group with affine geometrically connected fibres is smooth,
separated and quasi-compact with affine geometrically connected fibres, if
the ambient group is affine on local Artinian tests. -/
def AffineFiberTorusCentralizerGeometryStatement : Prop :=
  ∀ (S : Scheme.{u}) [IsLocallyNoetherian S] (G : GroupScheme S) [Smooth G.X.hom]
    [IsSeparated G.X.hom] [QuasiCompact G.X.hom] [GeometricallyConnected G.X.hom],
    HasAffineResidueFibers G →
    (∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A]
      (a : Spec (CommRingCat.of A) ⟶ S), IsAffineHom ((baseChange a).obj G).X.hom) →
    ∀ (T : CommGroupScheme S) (t : T.toGrp ⟶ G) (hT : RelativeTorus.IsTorus T.toGrp),
      let C := separatedRelativeTorusCentralizerModel t hT
      Smooth C.group.X.hom ∧ IsSeparated C.group.X.hom ∧ QuasiCompact C.group.X.hom ∧
        HasAffineResidueFibers C.group ∧ GeometricallyConnected C.group.X.hom

theorem affineFiberTorusCentralizerGeometry : AffineFiberTorusCentralizerGeometryStatement.{u} := by
  intro S _ G _ _ _ _ hG hA T t hT
  let C := separatedRelativeTorusCentralizerModel t hT
  have : IsClosedImmersion C.hom.hom.hom.left := C.closed
  refine ⟨smooth_of_artinianAffineCentralizer hA t hT C.closed C.represents, ?_, ?_,
    hasAffineResidueFibers_of_closedSubgroup C.closed hG,
    geometricallyConnected_of_affineFiberCentralizer hG t hT C.represents⟩
  · rw [← C.hom.hom.hom.w]
    infer_instance
  · rw [← C.hom.hom.hom.w]
    infer_instance

end Langlands.GroupScheme.TorusSubgroupModuli
