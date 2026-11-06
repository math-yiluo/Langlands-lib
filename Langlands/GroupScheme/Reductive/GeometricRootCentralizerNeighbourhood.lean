import Langlands.GroupScheme.Reductive.GeometricRankOneNeighbourhood
import Langlands.GroupScheme.Reductive.FiniteCentralizerNeighbourhood
import Langlands.GroupScheme.Torus.RelativeRootCentralizerProfiles
import Langlands.GroupScheme.Torus.RelativeCentralizerTransporters

/-! # Actual geometric root reflections and centralizer neighbourhoods -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.splitTorus

variable {r : Type u} [CommRing r] (I : Type u) [Fintype I] [DecidableEq I]
  (G : GroupScheme (Spec (CommRingCat.of r))) [Smooth G.X.hom] [IsAffineHom G.X.hom]
  (i : splitTorus (Spec (CommRingCat.of r)) I ⟶ G)

local instance rootNeighbourhood_smooth_geometricFiber (s : Spec (CommRingCat.of r)) :
    Smooth (geometricFiber G s).X.hom :=
  inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.snd G.X.hom (geometricPoint _ s)))

local instance rootNeighbourhood_affine_geometricFiber (s : Spec (CommRingCat.of r)) :
    IsAffineHom (geometricFiber G s).X.hom :=
  inferInstanceAs (IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (geometricPoint _ s)))

namespace RelativeCocharacterCentralizer

variable (n : I → ℤ) (s : Spec (CommRingCat.of r))
  (e : (I → ℤ) ≃ₗ[ℤ] (I → ℤ))
  (hfix : CommGroupScheme.groupHom (exponentCocharacter
      (Spec (CommRingCat.of (AlgebraicClosure ((Spec (CommRingCat.of r)).residueField s))))
      I n) ≫ (exponentIso _ I e).hom =
    CommGroupScheme.groupHom (exponentCocharacter _ I n))
  (g : Over.mk (𝟙 (Spec (CommRingCat.of
      (AlgebraicClosure ((Spec (CommRingCat.of r)).residueField s)))) ) ⟶
    (identityComponent (geometricFiber G s)).X)
  (hg : PointwiseSchemeAction.IsTransporter
    ((exponentIso _ I e).hom ≫ geometricIdentityComponentHom I G i s)
    (geometricIdentityComponentHom I G i s) g)

/-- A geometric identity-component transporter fixing the actual cocharacter
factors through the actual centralizer's geometric identity component. -/
def geometricIdentityTransporterPoint :
    Over.mk (𝟙 (Spec (CommRingCat.of
      (AlgebraicClosure ((Spec (CommRingCat.of r)).residueField s)))) ) ⟶
        (identityComponent (geometricFiber (groupScheme I G i n) s)).X :=
  ((isRepresentedBy_geometricIdentityInclusion I G i n s).pointsEquiv _).symm
    ⟨g, hg.mem_centralizer_of_fixed_cocharacter
      (CommGroupScheme.groupHom (exponentCocharacter _ I n)) hfix⟩

@[reassoc (attr := simp)]
theorem geometricIdentityTransporterPoint_comp :
    geometricIdentityTransporterPoint I G i n s e hfix g hg ≫
      (geometricIdentityInclusion I G i n s).hom.hom = g :=
  (isRepresentedBy_geometricIdentityInclusion I G i n s).pointsEquiv_symm_comp _

/-- The same integral automorphism transports the actual factored torus, on
every test refinement, in the centralizer's actual geometric identity component. -/
theorem geometricIdentityTransporterPoint_isTransporter :
    PointwiseSchemeAction.IsTransporter
      ((exponentIso _ I e).hom ≫
        geometricIdentityComponentHom I (groupScheme I G i n) (torusHom I G i n) s)
      (geometricIdentityComponentHom I (groupScheme I G i n) (torusHom I G i n) s)
      (geometricIdentityTransporterPoint I G i n s e hfix g hg) := by
  let : Mono (geometricIdentityInclusion I G i n s).hom.hom :=
    (isRepresentedBy_geometricIdentityInclusion I G i n s).1
  apply PointwiseSchemeAction.IsTransporter.of_comp (geometricIdentityInclusion I G i n s)
  simpa only [Category.assoc, geometricIdentityTorusHom_comp,
    geometricIdentityTransporterPoint_comp] using hg

omit e hfix g hg in
/-- A surviving actual exponent weight has the ambient relative rank at the
specified base point. -/
theorem exponentWeightRank_eq_of_dot_eq_zero (m : I → ℤ)
    (hm : ∑ j, m j * n j = 0) :
    exponentWeightRank I (groupScheme I G i n) (torusHom I G i n) m s =
      exponentWeightRank I G i m s := by
  rw [← finrank_weight_geometricIdentityComponentHom,
    ← finrank_weight_geometricIdentityComponentHom]
  exact finrank_geometricCentralizerWeight I G i n s m hm

end RelativeCocharacterCentralizer

/-- Actual original-fibre reflection data for a root and its canonically
chosen generic annihilating cocharacter. Existence is a separate field theorem. -/
structure GeometricRootReflectionData (s : Spec (CommRingCat.of r))
    (m : I → ℤ) (hm : m ∈ geometricExponentRoots I G i s) where
  automorphism : (I → ℤ) ≃ₗ[ℤ] (I → ℤ)
  inverts : automorphism m = -m
  fixesCocharacter : CommGroupScheme.groupHom (exponentCocharacter
      (Spec (CommRingCat.of (AlgebraicClosure ((Spec (CommRingCat.of r)).residueField s))))
      I (rootCentralizerVector I G i s m hm)) ≫
        (exponentIso _ I automorphism).hom =
    CommGroupScheme.groupHom (exponentCocharacter _ I (rootCentralizerVector I G i s m hm))
  point : Over.mk (𝟙 (Spec (CommRingCat.of
      (AlgebraicClosure ((Spec (CommRingCat.of r)).residueField s)))) ) ⟶
    (identityComponent (geometricFiber G s)).X
  transports : PointwiseSchemeAction.IsTransporter
    ((exponentIso _ I automorphism).hom ≫ geometricIdentityComponentHom I G i s)
    (geometricIdentityComponentHom I G i s) point

/-- Construct a good neighbourhood for a fixed actual root centralizer from
the ambient fibre's forward root data and actual reflection point. -/
def rootCentralizerReductiveNeighbourhood_of_geometricReflection
    (hi : IsClosedSubgroup i) (s : Spec (CommRingCat.of r))
    (hself : s ∈ geometricSelfCentralizingTorusLocus I G i)
    (m : I → ℤ) (hm : m ∈ geometricExponentRoots I G i s)
    (hneg : -m ∈ geometricExponentRoots I G i s)
    (hred : ∀ a ∈ geometricExponentRoots I G i s,
      ¬ LinearIndependent ℤ ![
        exponentCharacter
          (Spec (CommRingCat.of (AlgebraicClosure ((Spec (CommRingCat.of r)).residueField s)))) I m,
        exponentCharacter
          (Spec (CommRingCat.of (AlgebraicClosure ((Spec (CommRingCat.of r)).residueField s)))) I a] →
        a = m ∨ a = -m)
    (hpos : exponentWeightRank I G i m s = 1)
    (hminus : exponentWeightRank I G i (-m) s = 1)
    (d : GeometricRootReflectionData I G i s m hm) :
    IdentityComponentReductiveOpenNeighbourhood
      (RelativeCocharacterCentralizer.groupScheme I G i (rootCentralizerVector I G i s m hm)) s := by
  let n := rootCentralizerVector I G i s m hm
  have hdot : ∑ j, m j * n j = 0 := dot_rootCentralizerVector I G i s m hm
  have hdotneg : ∑ j, (-m) j * n j = 0 := by
    simpa only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_eq_zero] using hdot
  apply rankOneIdentityComponentReductiveNeighbourhood_of_geometricTransporter I
    (RelativeCocharacterCentralizer.groupScheme I G i n)
    (RelativeCocharacterCentralizer.torusHom I G i n)
    (RelativeCocharacterCentralizer.isClosedSubgroup_torusHom I G i n hi) s
    (mem_geometricSelfCentralizingTorusLocus_centralizer I G i hi n s hself) m
    ((mem_geometricExponentRoots_iff I G i s m).mp hm).1
    (mem_geometricRootCentralizerExponentRoots_iff_pair I G i s m hm hneg hred)
    ((RelativeCocharacterCentralizer.exponentWeightRank_eq_of_dot_eq_zero
      I G i n s m hdot).trans hpos)
    ((RelativeCocharacterCentralizer.exponentWeightRank_eq_of_dot_eq_zero
      I G i n s (-m) hdotneg).trans hminus)
    d.automorphism d.inverts
    (RelativeCocharacterCentralizer.geometricIdentityTransporterPoint
      I G i n s d.automorphism d.fixesCocharacter d.point d.transports)
  exact RelativeCocharacterCentralizer.geometricIdentityTransporterPoint_isTransporter
    I G i n s d.automorphism d.fixesCocharacter d.point d.transports

/-- Finite assembly constructs an actual ambient good open from original-fibre
root negation, reducedness, lines and actual reflection data. -/
def identityComponentReductiveNeighbourhood_of_geometricRootReflections
    (hi : IsClosedSubgroup i) (s : Spec (CommRingCat.of r))
    (hself : s ∈ geometricSelfCentralizingTorusLocus I G i)
    (hneg : ∀ m ∈ geometricExponentRoots I G i s,
      -m ∈ geometricExponentRoots I G i s)
    (hred : ∀ m ∈ geometricExponentRoots I G i s,
      ∀ a ∈ geometricExponentRoots I G i s,
      ¬ LinearIndependent ℤ ![
        exponentCharacter
          (Spec (CommRingCat.of (AlgebraicClosure ((Spec (CommRingCat.of r)).residueField s)))) I m,
        exponentCharacter
          (Spec (CommRingCat.of (AlgebraicClosure ((Spec (CommRingCat.of r)).residueField s)))) I a] →
        a = m ∨ a = -m)
    (hlines : ∀ m ∈ geometricExponentRoots I G i s, exponentWeightRank I G i m s = 1)
    (hreflection : ∀ m (hm : m ∈ geometricExponentRoots I G i s),
      Nonempty (GeometricRootReflectionData I G i s m hm)) :
    IdentityComponentReductiveOpenNeighbourhood G s := by
  let n : geometricExponentRootFinset I G i s → (I → ℤ) := fun a =>
    rootCentralizerVector I G i s a.val ((mem_geometricExponentRootFinset I G i s a.val).mp a.property)
  apply identityComponentReductiveNeighbourhood_of_rootCentralizers I G i hi s hself n
  · intro a
    exact dot_rootCentralizerVector I G i s a.val
      ((mem_geometricExponentRootFinset I G i s a.val).mp a.property)
  · intro a
    have ha := (mem_geometricExponentRootFinset I G i s a.val).mp a.property
    exact rootCentralizerReductiveNeighbourhood_of_geometricReflection I G i hi s hself a.val ha
      (hneg a.val ha) (hred a.val ha) (hlines a.val ha) (hlines (-a.val) (hneg a.val ha))
      (Classical.choice (hreflection a.val ha))

end Langlands.GroupScheme.splitTorus
