import Langlands.GroupScheme.Reductive.CoordinateTranslationClosure
import Langlands.GroupScheme.Reductive.SplitLeviGluingSimpleUnipotent
import Langlands.GroupScheme.Rational.StandardRepresentability

/-! # Coordinate invariance from the simple roots of a chamber -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048

namespace Langlands.GroupScheme.UnipotentCoordinateInvariance

open AffineCoordinates CoordinateTranslationClosure

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G U : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom U.X.hom] [Smooth U.X.hom]

local instance {K : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom K.X.hom] :
    IsAffine K.X.left := isAffine_of_isAffineHom K.X.hom

/-- The coordinate stabilizer envelope, mapped into the ambient group. -/
def ambientStabilizerHom (j : U ⟶ G) (b : algebra U) :
    (leftStabilizerEnvelope U b).group ⟶ G :=
  (leftStabilizerEnvelope U b).inclusion ≫ j

/-- A smooth family with rational images fixing the coordinate factors through
its actual closed stabilizer envelope. -/
theorem factorsThrough_stabilizerEnvelope
    {P : Over (Spec (CommRingCat.of k))} [Smooth P.hom]
    (a : P ⟶ U.X) (b : algebra U)
    (ha : ∀ (h : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ P)
      (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ U.X),
      pointAlgebraHom U _ ((h ≫ a) * g) b = pointAlgebraHom U _ g b) :
    FactorsThrough a (leftStabilizerEnvelope U b).inclusion := by
  have : IsReduced P.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field k _ P.hom
  apply LeviGluing.factorsThrough_of_range_subset (leftStabilizerEnvelope U b).closed
  rw [(leftStabilizerEnvelope U b).range_eq]
  apply LeviGluing.range_subset_closure_rationalPointImage
  intro h
  exact ha h

variable [Smooth G.X.hom] [ConnectedSpace G.X.left]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {i : T.toGrp ⟶ G} {J : Type v}
    {Q : RootDatum J (characterLattice T) (cocharacterLattice T)}
    {ν : cocharacterLattice T}

/-- Rational simple-root translations fixing a coordinate force every
unipotent point into its closed stabilizer envelope, on every test. -/
theorem mem_range_stabilizerEnvelope_of_simpleRoots
    (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp)
    (hi : IsMaximalTorus i) (hQ : IsRootDatumOf i Q) (hν : IsGenericCocharacter i ν)
    (j : U ⟶ G) (hj : (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy j)
    (hjc : IsClosedSubgroup j) (b : algebra U)
    (hroot : ∀ a ∈ simpleRelativeRoots i ν,
      ∀ (x g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ U.X),
        x ≫ j.hom.hom ∈ (RelativeRoot.subgroup i a).carrier _ →
        pointAlgebraHom U _ (x * g) b = pointAlgebraHom U _ g b)
    (V : Over (Spec (CommRingCat.of k))) (x : V ⟶ U.X) :
    x ∈ (SubgroupFunctor.range (leftStabilizerEnvelope U b).inclusion).carrier V := by
  let E := leftStabilizerEnvelope U b
  have hpos : ∀ a ∈ simpleRelativeRoots i ν,
      RelativeRoot.subgroup i a ≤ SubgroupFunctor.range (ambientStabilizerHom j b) := by
    intro a ha
    have hane : a ≠ 0 := (mem_relativeRoots.mp ha.1.1).1
    obtain ⟨R, jR, hR, _, hs, _⟩ :=
      RelativeRoot.subgroup_has_smooth_closed_representative hT i a hane
    let : Smooth R.X.hom := hs
    let f : R ⟶ U := hR.inclusionHom hj
      (RelativeRoot.subgroup_le_dynamicUnipotent i ν ha.1.2)
    have hf : f ≫ j = jR := SubgroupFunctor.IsRepresentedBy.inclusionHom_comp _ _ _
    have hfac : FactorsThrough f.hom.hom E.inclusion := by
      apply factorsThrough_stabilizerEnvelope f.hom.hom b
      intro h g
      apply hroot a ha
      rw [Category.assoc, ← Grp.comp_hom_hom, hf, ← hR.2]
      exact SubgroupFunctor.mem_range.mpr ⟨h, rfl⟩
    obtain ⟨c, hc⟩ := hfac
    intro W z hz
    rw [← hR.2] at hz
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hz
    apply SubgroupFunctor.mem_range.mpr
    refine ⟨y ≫ c, ?_⟩
    change (y ≫ c) ≫ E.inclusion.hom.hom ≫ j.hom.hom = y ≫ jR.hom.hom
    rw [Category.assoc, ← Category.assoc c, hc,
      ← Grp.comp_hom_hom, hf]
  have hgen := LeviGluing.unipotent_le_range_of_simpleRoots hG hT hi hQ hν
    (ambientStabilizerHom j b) (E.closed.comp hjc) hpos
  have hx : x ≫ j.hom.hom ∈
      (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).carrier V := by
    rw [← hj.2]
    exact SubgroupFunctor.mem_range.mpr ⟨x, rfl⟩
  obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp (hgen V hx)
  apply SubgroupFunctor.mem_range.mpr
  refine ⟨y, ?_⟩
  have : Mono j.hom.hom := hj.1
  apply (cancel_mono j.hom.hom).mp
  exact (Category.assoc _ _ _).trans hy

/-- Simple-root invariance at rational points implies left invariance on the
whole chamber unipotent group, with arbitrary tests in the conclusion. -/
theorem leftInvariant_of_simpleRoots
    (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp)
    (hi : IsMaximalTorus i) (hQ : IsRootDatumOf i Q) (hν : IsGenericCocharacter i ν)
    (j : U ⟶ G) (hj : (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy j)
    (hjc : IsClosedSubgroup j) (b : algebra U)
    (hroot : ∀ a ∈ simpleRelativeRoots i ν,
      ∀ (x g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ U.X),
        x ≫ j.hom.hom ∈ (RelativeRoot.subgroup i a).carrier _ →
        pointAlgebraHom U _ (x * g) b = pointAlgebraHom U _ g b)
    (V : Over (Spec (CommRingCat.of k))) (x g : V ⟶ U.X) :
    pointAlgebraHom U V (x * g) b = pointAlgebraHom U V g b := by
  obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp
    (mem_range_stabilizerEnvelope_of_simpleRoots hG hT hi hQ hν j hj hjc b hroot V x)
  rw [← hy]
  exact leftInvariant_stabilizerEnvelope U b V y g

/-- Such a coordinate takes its actual identity value at every test point. -/
theorem eq_identityValue_of_simpleRoots
    (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp)
    (hi : IsMaximalTorus i) (hQ : IsRootDatumOf i Q) (hν : IsGenericCocharacter i ν)
    (j : U ⟶ G) (hj : (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy j)
    (hjc : IsClosedSubgroup j) (b : algebra U)
    (hroot : ∀ a ∈ simpleRelativeRoots i ν,
      ∀ (x g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ U.X),
        x ≫ j.hom.hom ∈ (RelativeRoot.subgroup i a).carrier _ →
        pointAlgebraHom U _ (x * g) b = pointAlgebraHom U _ g b)
    (V : Over (Spec (CommRingCat.of k))) (x : V ⟶ U.X) :
    pointAlgebraHom U V x b = pointAlgebraHom U V 1 b := by
  simpa only [mul_one] using
    leftInvariant_of_simpleRoots hG hT hi hQ hν j hj hjc b hroot V x 1

end Langlands.GroupScheme.UnipotentCoordinateInvariance
